// ff_twist.rs — does the function-field NO-theorem survive an infinite unit group?
//
// prop:ff-pyth kills cycles over F_q[t] by DEGREE: with pi' = 1, deg D(a) <= deg a - 1, so
// D(a) = b, D(b) = a forces deg b <= deg a - 1 <= deg b - 2. The paper reads this as the
// archimedean/degree obstruction. But over the S-integers F_q[t, 1/t] the unit group is
// infinite (c * t^k), and a unit-valued derivative may take values u_i = c_i t^{k_i}. Then
//     deg D(a) <= deg a - 1 + K,      K = max k_i,
// and the two-cycle inequalities give 0 <= -2 + 2K: the degree obstruction DIES at K >= 1.
//
// So: is F_q[t] immune because of the degree, or because its unit group is finite? This
// program searches for genuine two-cycles D(a) = b, D(b) = a with a, b monic squarefree,
// coprime to each other and to t, over F_3[t], with unit values c * t^k, c in F_3^*,
// k <= KMAX. KMAX = 0 must find nothing (that is prop:ff-pyth). KMAX >= 1 is the question.
//
// Build: rustc -O -o ff_twist ff_twist.rs
// Run:   ./ff_twist [DEGMAX KMAX]        default 6 1

const Q: u32 = 3;

type Poly = Vec<u32>;                    // coeffs mod 3, little-endian, trimmed

fn trim(mut a: Poly) -> Poly { while a.len() > 1 && *a.last().unwrap() == 0 { a.pop(); } a }
fn is_zero(a: &Poly) -> bool { a.len() == 1 && a[0] == 0 }
fn deg(a: &Poly) -> usize { a.len() - 1 }

fn add(a: &Poly, b: &Poly) -> Poly {
    let n = a.len().max(b.len());
    let mut r = vec![0u32; n];
    for i in 0..n {
        let x = if i < a.len() { a[i] } else { 0 };
        let y = if i < b.len() { b[i] } else { 0 };
        r[i] = (x + y) % Q;
    }
    trim(r)
}
fn mul(a: &Poly, b: &Poly) -> Poly {
    if is_zero(a) || is_zero(b) { return vec![0]; }
    let mut r = vec![0u32; a.len() + b.len() - 1];
    for i in 0..a.len() { if a[i] != 0 {
        for j in 0..b.len() { r[i + j] = (r[i + j] + a[i] * b[j]) % Q; }
    }}
    trim(r)
}
fn scale(a: &Poly, c: u32) -> Poly { trim(a.iter().map(|&x| (x * c) % Q).collect()) }
fn shift(a: &Poly, k: usize) -> Poly {          // multiply by t^k
    if is_zero(a) { return vec![0]; }
    let mut r = vec![0u32; k]; r.extend_from_slice(a); trim(r)
}
// divide a by b exactly (b monic); returns None if not exact
fn div_exact(a: &Poly, b: &Poly) -> Option<Poly> {
    if is_zero(b) { return None; }
    if is_zero(a) { return Some(vec![0]); }
    if deg(a) < deg(b) { return None; }
    let mut rem = a.clone();
    let mut q = vec![0u32; deg(a) - deg(b) + 1];
    let binv = {  // inverse of leading coeff of b
        let lb = b[deg(b)]; (1..Q).find(|&x| (x * lb) % Q == 1).unwrap()
    };
    while !is_zero(&rem) && deg(&rem) >= deg(b) {
        let d = deg(&rem) - deg(b);
        let c = (rem[deg(&rem)] * binv) % Q;
        q[d] = c;
        let sub = shift(&scale(b, c), d);
        // rem -= sub  (char 3: subtract = add 2*)
        rem = add(&rem, &scale(&sub, Q - 1));
    }
    if is_zero(&rem) { Some(trim(q)) } else { None }
}

fn all_monic(degmax: usize) -> Vec<Poly> {
    let mut out = Vec::new();
    for d in 1..=degmax {
        let total = Q.pow(d as u32);
        for code in 0..total {
            let mut c = vec![0u32; d + 1];
            let mut x = code;
            for i in 0..d { c[i] = x % Q; x /= Q; }
            c[d] = 1;
            out.push(c);
        }
    }
    out
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let degmax: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(6);
    let kmax: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);

    let monics = all_monic(degmax);
    // irreducibles: monic, not divisible by any lower-degree monic of degree >=1
    let mut irr: Vec<Poly> = Vec::new();
    for p in &monics {
        let d = deg(p);
        let mut is_irr = true;
        for g in &irr {
            if deg(g) * 2 > d { break; }
            if div_exact(p, g).is_some() { is_irr = false; break; }
        }
        if is_irr { irr.push(p.clone()); }
    }
    // squarefree monics coprime to t (nonzero constant term), with their irreducible factors
    let mut items: Vec<(Poly, Vec<Poly>)> = Vec::new();
    for p in &monics {
        if p[0] == 0 { continue; }                       // divisible by t
        let mut rest = p.clone(); let mut fs: Vec<Poly> = Vec::new(); let mut ok = true;
        for g in &irr {
            if let Some(q) = div_exact(&rest, g) {
                if div_exact(&q, g).is_some() { ok = false; break; }   // square factor
                fs.push(g.clone()); rest = q;
            }
        }
        if ok && deg(&rest) == 0 && rest[0] == 1 && !fs.is_empty() {
            items.push((p.clone(), fs));
        }
    }
    eprintln!("F_3[t]: {} irreducibles, {} squarefree monics coprime to t, deg <= {}, KMAX = {}",
              irr.len(), items.len(), degmax, kmax);

    // all twisted derivative values of x with factors fs
    let derivs = |x: &Poly, fs: &Vec<Poly>| -> Vec<Poly> {
        let n = fs.len();
        let opts: usize = (2 * (kmax + 1)).pow(n as u32);      // (c in {1,2}) x (k in 0..=kmax)
        let mut out = Vec::new();
        for code in 0..opts {
            let mut acc: Poly = vec![0];
            let mut z = code;
            for f in fs.iter() {
                let c = 1 + (z % 2) as u32; z /= 2;
                let k = z % (kmax + 1); z /= kmax + 1;
                let cof = div_exact(x, f).unwrap();
                acc = add(&acc, &shift(&scale(&cof, c), k));
            }
            out.push(acc);
        }
        out
    };

    use std::collections::HashMap;
    let mut index: HashMap<Vec<u32>, usize> = HashMap::new();
    for (i, (p, _)) in items.iter().enumerate() { index.insert(p.clone(), i); }

    let mut cycles = 0u64;
    for (i, (aa, fa)) in items.iter().enumerate() {
        for db in derivs(aa, fa) {
            if is_zero(&db) { continue; }
            // normalise to monic (units are free)
            let lead = db[deg(&db)];
            let linv = (1..Q).find(|&x| (x * lead) % Q == 1).unwrap();
            let bb = scale(&db, linv);
            if bb[0] == 0 { continue; }                      // must be coprime to t
            let j = match index.get(&bb) { Some(&j) => j, None => continue };
            if j == i { continue; }                          // want a genuine 2-cycle
            // coprime to a ?
            let g = {
                let mut sh = false;
                for f in fa { if div_exact(&bb, f).is_some() { sh = true; break; } }
                sh
            };
            if g { continue; }
            // does D(b) hit a (up to unit)?
            let (_, fb) = &items[j];
            for da in derivs(&bb, fb) {
                if is_zero(&da) { continue; }
                let l2 = da[deg(&da)];
                let l2i = (1..Q).find(|&x| (x * l2) % Q == 1).unwrap();
                if scale(&da, l2i) == *aa {
                    cycles += 1;
                    if cycles <= 5 {
                        println!("TWISTED FF 2-CYCLE: a = {:?}  b = {:?}  (coeffs low->high, F_3)", aa, bb);
                    }
                    break;
                }
            }
        }
    }
    println!("KMAX = {}: twisted two-cycles found: {}", kmax, cycles);
    if kmax == 0 && cycles > 0 { println!("  !! contradicts prop:ff-pyth -- investigate"); }
}
