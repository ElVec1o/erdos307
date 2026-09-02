// close60.rs — Erdős #307: direct search for a level-60 solution (the smallest possible),
// extending close59 to 60-prime supports.
//
// A #307 solution with |P∪Q| = 60 is a set U of 60 primes with T(U) = Σ 1/p > 2 and BOTH
//   N_U + 2 D_U = (a+b)²   and   N_U − 2 D_U = (a−b)²   perfect squares
// (D_U = ∏U, N_U = Σ D_U/p = cofactor sum; a = ∏P, b = ∏Q).  close59 proved no 59-set works;
// the pair sector at level 60 is congruence-immune (locally soluble everywhere), so the ONLY
// attack is this direct both-squares search.
//
// Every 60-set with T(U) > 2 contains the 27 smallest primes (2..103), forced; the other 33 come
// from the pool of primes 107..P_K.  This program enumerates all such sets with T(U) > 2 (exact
// rational pruning), and for each tests the plus-square (fast reject) then the minus-square.
// A hit is a candidate #307 SOLUTION — it is printed in full for verification.
//
// Build:  rustc -O -o close60 close60.rs
// Run:    ./close60 [K]     K = number of leading primes to draw the pool from (default 66).
//                           K=66 ~ 3.3M sets (seconds); 68 ~ 1e8 (minutes); 70 ~ 2e9 (hours).

use std::env;
use std::time::Instant;

type Big = Vec<u64>;
fn norm(mut a: Big) -> Big { while a.len() > 1 && *a.last().unwrap() == 0 { a.pop(); } a }
fn from_u64(x: u64) -> Big { vec![x] }
fn is_zero(a: &Big) -> bool { a.len() == 1 && a[0] == 0 }
fn cmp_big(a: &Big, b: &Big) -> std::cmp::Ordering {
    use std::cmp::Ordering::*;
    if a.len() != b.len() { return a.len().cmp(&b.len()); }
    for i in (0..a.len()).rev() { if a[i] != b[i] { return if a[i] < b[i] { Less } else { Greater }; } }
    Equal
}
fn add_big(a: &Big, b: &Big) -> Big {
    let n = a.len().max(b.len()); let mut r = Vec::with_capacity(n + 1); let mut c = 0u128;
    for i in 0..n { let s = c + *a.get(i).unwrap_or(&0) as u128 + *b.get(i).unwrap_or(&0) as u128; r.push(s as u64); c = s >> 64; }
    if c > 0 { r.push(c as u64); } norm(r)
}
fn sub_big(a: &Big, b: &Big) -> Big {
    let mut r = Vec::with_capacity(a.len()); let mut br = 0i128;
    for i in 0..a.len() { let d = a[i] as i128 - *b.get(i).unwrap_or(&0) as i128 - br;
        if d < 0 { r.push((d + (1i128 << 64)) as u64); br = 1; } else { r.push(d as u64); br = 0; } }
    assert_eq!(br, 0); norm(r)
}
fn mul_small(a: &Big, m: u64) -> Big {
    let mut r = Vec::with_capacity(a.len() + 1); let mut c = 0u128;
    for &x in a { let p = x as u128 * m as u128 + c; r.push(p as u64); c = p >> 64; }
    if c > 0 { r.push(c as u64); } norm(r)
}
fn div_small(a: &Big, d: u64) -> (Big, u64) {
    let mut q = vec![0u64; a.len()]; let mut rem = 0u128;
    for i in (0..a.len()).rev() { let cur = (rem << 64) | a[i] as u128; q[i] = (cur / d as u128) as u64; rem = cur % d as u128; }
    (norm(q), rem as u64)
}
fn mul_big(a: &Big, b: &Big) -> Big {
    let mut r = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() { let mut c = 0u128;
        for (j, &y) in b.iter().enumerate() { let t = r[i + j] as u128 + x as u128 * y as u128 + c; r[i + j] = t as u64; c = t >> 64; }
        let mut k = i + b.len(); while c > 0 { let t = r[k] as u128 + c; r[k] = t as u64; c = t >> 64; k += 1; } }
    norm(r)
}
fn bit_len(a: &Big) -> usize { 64 * (a.len() - 1) + (64 - a.last().unwrap().leading_zeros() as usize) }
fn shr_bits(a: &Big, k: usize) -> Big {
    let (l, b) = (k / 64, k % 64); if l >= a.len() { return from_u64(0); }
    let mut r = Vec::with_capacity(a.len() - l);
    for i in l..a.len() { let mut v = a[i] >> b; if b > 0 && i + 1 < a.len() { v |= a[i + 1] << (64 - b); } r.push(v); }
    norm(r)
}
fn shl_bits(a: &Big, k: usize) -> Big {
    let (l, b) = (k / 64, k % 64); let mut r = vec![0u64; l]; let mut c = 0u64;
    for &x in a { r.push((x << b) | c); c = if b > 0 { x >> (64 - b) } else { 0 }; }
    if c > 0 { r.push(c); } norm(r)
}
fn isqrt_exact(n: &Big) -> bool {
    if is_zero(n) { return true; }
    let l = bit_len(n); let mut bit = shl_bits(&from_u64(1), (l - 1) & !1);
    let mut res = from_u64(0); let mut rem = n.clone();
    while !is_zero(&bit) {
        let t = add_big(&res, &bit);
        if cmp_big(&rem, &t) != std::cmp::Ordering::Less { rem = sub_big(&rem, &t); res = add_big(&shr_bits(&res, 1), &bit); }
        else { res = shr_bits(&res, 1); }
        bit = shr_bits(&bit, 2);
    }
    is_zero(&rem)
}
fn mod_small(a: &Big, m: u64) -> u64 { let mut r = 0u128; for i in (0..a.len()).rev() { r = ((r << 64) | a[i] as u128) % m as u128; } r as u64 }

fn main() {
    let k: usize = env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(66);

    // primes
    let bound = 2000usize;
    let mut comp = vec![false; bound + 1]; let mut primes: Vec<u64> = Vec::new();
    for i in 2..=bound { if !comp[i] { primes.push(i as u64); let mut j = i * i; while j <= bound { comp[j] = true; j += i; } } }
    let forced: Vec<u64> = primes[..27].to_vec();          // 2..103
    assert_eq!(*forced.last().unwrap(), 103);
    let pool: Vec<u64> = primes[27..k].to_vec();           // 107 .. p_K
    let need = 60 - forced.len();                          // 33
    eprintln!("forced 27 (2..103); pool {} ({}..{}); choose {}; K={}",
              pool.len(), pool[0], pool[pool.len()-1], need, k);
    assert!(pool.len() >= need, "K too small");

    // exact rational threshold: chosen pool reciprocals must exceed 2 - Σ1/forced.
    // Use f64 with a safety margin for the DFS prune, exact recheck via cofactor sum at the leaf.
    let tforced: f64 = forced.iter().map(|&p| 1.0 / p as f64).sum();
    let thr = 2.0 - tforced;
    let pf: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    // suffix sums for pruning
    let mut suf = vec![0.0f64; pool.len() + 1];
    for i in (0..pool.len()).rev() { suf[i] = suf[i + 1] + pf[i]; }
    let mut dforced = from_u64(1);
    for &p in &forced { dforced = mul_small(&dforced, p); }

    // small-prime QR wheel to reject non-square plus-values fast
    let sieve_primes: Vec<u64> = primes.iter().cloned().filter(|&p| p > 103 && p < 400).collect();
    let qr: Vec<Vec<bool>> = sieve_primes.iter().map(|&m| {
        let mut v = vec![false; m as usize]; for x in 0..m { v[((x * x) % m) as usize] = true; } v
    }).collect();

    let start = Instant::now();
    let mut count: u64 = 0;
    let mut plus_sq: u64 = 0;
    let mut hits: u64 = 0;

    // iterative DFS choosing `need` pool indices in increasing order
    // frame: (next_index, chosen_so_far, running f64 recip sum, chosen list)
    let mut stack: Vec<(usize, usize, f64, Vec<usize>)> = vec![(0, 0, 0.0, Vec::new())];
    while let Some((i, cho, cur, chosen)) = stack.pop() {
        if cho == need {
            // exact leaf: build U, cofactor sum, both-squares
            let mut d = dforced.clone();
            for &j in &chosen { d = mul_small(&d, pool[j]); }
            // exact T>2 recheck: cofactor sum N vs 2D
            let u: Vec<u64> = forced.iter().cloned().chain(chosen.iter().map(|&j| pool[j])).collect();
            let mut nu = from_u64(0);
            for &p in &u { let (q, r) = div_small(&d, p); debug_assert_eq!(r, 0); nu = add_big(&nu, &q); }
            let d2 = mul_small(&d, 2);
            if cmp_big(&nu, &d2) != std::cmp::Ordering::Greater { continue; } // T<=2 exact
            count += 1;
            let plus = add_big(&nu, &d2);
            // QR wheel
            let mut ok = true;
            for (s, &m) in sieve_primes.iter().enumerate() { if !qr[s][mod_small(&plus, m) as usize] { ok = false; break; } }
            if !ok { continue; }
            if !isqrt_exact(&plus) { continue; }
            plus_sq += 1;
            let minus = sub_big(&nu, &d2);
            if isqrt_exact(&minus) {
                hits += 1;
                println!("\n*** LEVEL-60 BOTH-SQUARES HIT — CANDIDATE #307 SOLUTION ***");
                println!("U = {:?}", u);
                println!("(verify: split U into P,Q with ∏P+∏Q = √plus, and D(∏P)=∏Q)");
            }
            continue;
        }
        // prune: even taking the largest-reciprocal remaining pool primes can't reach thr
        let remaining = need - cho;
        if i + remaining > pool.len() { continue; }
        if cur + suf[i] < thr - 1e-9 { continue; }             // can't possibly reach 2
        // (optional upper cut: smallest reciprocals; not needed for correctness)
        // branch: skip i, or take i
        stack.push((i + 1, cho, cur, chosen.clone()));
        let mut c2 = chosen.clone(); c2.push(i);
        stack.push((i + 1, cho + 1, cur + pf[i], c2));

        if count > 0 && count % 2_000_000 == 0 {
            let el = start.elapsed().as_secs_f64();
            eprint!("\r  sets {}  plus-squares {}  hits {}  {:.0}s   ", count, plus_sq, hits, el);
        }
    }
    eprintln!();
    println!("\n=== close60 (pool ≤ first {} primes) ===", k);
    println!("60-sets with T>2 examined: {}", count);
    println!("passed plus-square: {}", plus_sq);
    println!("BOTH-squares hits (candidate solutions): {}", hits);
    if hits == 0 { println!("=> no level-60 solution with all primes among the first {} ({}).", k, pool[pool.len()-1]); }
    println!("time {:.0}s", start.elapsed().as_secs_f64());
}
