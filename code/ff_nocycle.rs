// ff_nocycle.rs — the arithmetic derivative over F_q[t] has NO cycles, for a degree reason.
//
// For squarefree f = prod pi_i in F_q[t] the arithmetic derivative is f' = sum_i f/pi_i. Each term
// has degree deg f - deg pi_i <= deg f - 1, so deg f' <= deg f - 1: the derivative STRICTLY drops
// the degree. A two-cycle f' = g, g' = f would force deg f <= deg g - 1 <= deg f - 2. Impossible.
//
// This is precisely where the number field differs. Over Z the mass sigma(n) = sum_{p|n} 1/p can
// exceed 1, so n' can exceed n. Over F_q[t] the ultrametric forces |sigma(f)| = max_i |1/pi_i| < 1
// always, so the mass can never reach 1 and the cycle equation sigma(f) sigma(g) = 1 is unsolvable.
// #307 is an ARCHIMEDEAN phenomenon.
//
// Verified here by brute force, independently of the proof: all monic squarefree f over F_2 and F_3
// with deg f <= D, checking deg f' <= deg f - 1 and that no f, g form a two-cycle.
// Build: rustc -O -o ff_nocycle ff_nocycle.rs
type P = Vec<u32>; // coefficients, low to high, normalised so last != 0; empty = zero

fn norm(mut a: P) -> P { while a.last() == Some(&0) { a.pop(); } a }
fn deg(a: &P) -> i32 { a.len() as i32 - 1 }
fn add(a: &P, b: &P, q: u32) -> P {
    let n = a.len().max(b.len());
    norm((0..n).map(|i| ((*a.get(i).unwrap_or(&0) + *b.get(i).unwrap_or(&0)) % q)).collect())
}
fn mul(a: &P, b: &P, q: u32) -> P {
    if a.is_empty() || b.is_empty() { return vec![]; }
    let mut r = vec![0u32; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() { for (j, &y) in b.iter().enumerate() { r[i + j] = (r[i + j] + x * y) % q; } }
    norm(r)
}
fn monics(d: usize, q: u32) -> Vec<P> { // all monic of exact degree d
    let mut out = vec![vec![1u32]];
    for _ in 0..d { let mut nx = Vec::new();
        for m in &out { for c in 0..q { let mut v = vec![c]; v.extend(m.iter()); nx.push(v); } } out = nx; }
    out.into_iter().map(norm).filter(|p| deg(p) == d as i32).collect()
}
fn divides(a: &P, b: &P, q: u32) -> Option<P> { // b / a exactly, or None
    if a.is_empty() { return None; }
    let mut r = b.clone(); let mut quo = vec![0u32; (deg(b) - deg(a) + 1).max(0) as usize];
    let inv = (1..q).find(|&x| x * a[a.len() - 1] % q == 1).unwrap();
    while deg(&r) >= deg(a) && !r.is_empty() {
        let sh = (deg(&r) - deg(a)) as usize;
        let c = r[r.len() - 1] * inv % q;
        quo[sh] = c;
        let mut t = vec![0u32; sh]; t.push(c);
        let sub = mul(a, &t, q);
        let neg: P = norm(sub.iter().map(|&x| (q - x) % q).collect());
        r = add(&r, &neg, q);
    }
    if r.is_empty() { Some(norm(quo)) } else { None }
}
fn main() {
    for &q in &[2u32, 3] {
        let d_max = if q == 2 { 13 } else { 8 };
        // irreducibles by trial division
        let mut irr: Vec<P> = Vec::new();
        for d in 1..=d_max { for m in monics(d, q) {
            if !irr.iter().any(|p| deg(p) * 2 <= deg(&m) + deg(p) && divides(p, &m, q).is_some() && deg(p) < deg(&m)) { irr.push(m); } } }
        // squarefree f = products of DISTINCT irreducibles, deg <= d_max; compute f'
        let mut checked = 0u64; let mut viol = 0u64;
        let mut der_of: std::collections::HashMap<Vec<u32>, Vec<u32>> = std::collections::HashMap::new();
        fn rec(i: usize, irr: &[P], q: u32, d_max: i32, cur: P, sel: &[usize],
               checked: &mut u64, viol: &mut u64, map: &mut std::collections::HashMap<Vec<u32>, Vec<u32>>) {
            if !sel.is_empty() {
                let mut d = vec![];
                for &s in sel { d = add(&d, &divides(&irr[s], &cur, q).unwrap(), q); }
                *checked += 1;
                if !(deg(&d) <= deg(&cur) - 1) { *viol += 1; }
                map.insert(cur.clone(), d);
            }
            for j in i..irr.len() {
                let nx = mul(&cur, &irr[j], q);
                if deg(&nx) > d_max { continue; }
                let mut s2 = sel.to_vec(); s2.push(j);
                rec(j + 1, irr, q, d_max, nx, &s2, checked, viol, map);
            }
        }
        rec(0, &irr, q, d_max as i32, vec![1u32], &[], &mut checked, &mut viol, &mut der_of);
        // two-cycles: f' = g and g' = f with f != g
        let mut cyc = 0u64;
        for (f, g) in der_of.iter() { if let Some(ff) = der_of.get(g) { if ff == f && f != g { cyc += 1; } } }
        println!("F_{}[t], deg <= {:>2}: {} squarefree monics, deg f' <= deg f - 1 violations {}, two-cycles {}",
                 q, d_max, checked, viol, cyc);
    }
    println!("\n  Degree strictly drops, so the orbit descends and no cycle of any length can exist.");
}
