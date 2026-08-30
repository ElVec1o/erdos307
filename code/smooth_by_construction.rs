// Building candidates smooth BY CONSTRUCTION, inverting the order of the two failed routes.
//
// Earlier routes fixed a ground set U, split it A u B, and hoped beta = sum_{a in A} alpha/a came out
// smooth. It never did: 0 of 5,272 in-window splits met the necessary condition y_max(beta) >= 1/x
// of prop:coprimesieve.
//
// Here the order is reversed. Choose the small primes B0 we WANT to divide beta and impose
//        sum_{a in A} a^{-1} = 0   (mod q)   for every q in B0,
// which by lem:symbolfact is exactly q | beta and is a condition on A alone. Drawing A from primes
// above max(B0) makes B0 disjoint from A, so the forced primes genuinely divide beta, and then
// y_max(beta) >= sum_{q in B0} 1/q by construction. Choosing B0 with sum 1/q > 1 makes the
// necessary condition pass for every x > 1.
//
// The ground set is no longer fixed -- B is whatever factors beta -- so the rigid mass window
// x + y = T(U) of the earlier routes does not apply; only x > 1 is required.
//
// The congruences are solved exactly, by meet-in-the-middle over disjoint swap pairs chosen from
// adjacent primes so that the mass barely moves.

fn primes_upto(n: u64) -> Vec<u64> {
    let mut s = vec![true; (n + 1) as usize];
    let (mut v, mut i) = (Vec::new(), 2u64);
    while i <= n {
        if s[i as usize] { v.push(i); let mut j = i * i; while j <= n { s[j as usize] = false; j += i; } }
        i += 1;
    }
    v
}
fn inv_mod(a: u64, m: u64) -> u64 {
    let (mut r0, mut r1) = (a as i128, m as i128);
    let (mut s0, mut s1) = (1i128, 0i128);
    while r1 != 0 { let q = r0 / r1;
        let t = r0 - q * r1; r0 = r1; r1 = t;
        let t = s0 - q * s1; s0 = s1; s1 = t; }
    (((s0 % m as i128) + m as i128) % m as i128) as u64
}

fn run(b0: Vec<u64>, k: usize, verbose: bool) -> bool {
    let m: u64 = b0.iter().product();
    let ymin: f64 = b0.iter().map(|&q| 1.0 / q as f64).sum();
    let top = *b0.iter().max().unwrap();
    // the pool must avoid B0 entirely, or a forced prime could land in A and then not divide beta
    let pool: Vec<u64> = primes_upto(400_000).into_iter().filter(|&p| p > top).collect();
    let pmass: f64 = pool.iter().map(|&p| 1.0 / p as f64).sum();
    if pmass <= 1.01 { println!("  pool mass {:.4} too small", pmass); return false; }

    let enc = |r: &[u64]| -> u64 {
        let mut v = 0u64;
        for (i, &q) in b0.iter().enumerate().rev() { v = v * q + r[i]; }
        v
    };

    let mut inA = vec![false; pool.len()];
    let mut x = 0.0_f64;
    for i in 0..pool.len() { if x >= 1.004 { break; } inA[i] = true; x += 1.0 / pool[i] as f64; }
    // every pool prime is odd, so inv = 1 (mod 2): the residue mod 2 is pinned to |A| mod 2
    let mut n_used = inA.iter().filter(|&&v| v).count();
    if n_used % 2 == 1 { inA[n_used] = true; x += 1.0 / pool[n_used] as f64; n_used += 1; }

    let mut base: Vec<u64> = vec![0; b0.len()];
    for i in 0..pool.len() { if inA[i] {
        for (qi, &q) in b0.iter().enumerate() { base[qi] = (base[qi] + inv_mod(pool[i] % q, q)) % q; } } }

    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let (mut lo, mut hi) = (n_used - 1, n_used);
    while pairs.len() < k && lo > 0 && hi < pool.len() { pairs.push((lo, hi)); lo -= 1; hi += 1; }
    if pairs.len() < k { println!("  not enough swap pairs"); return false; }
    let deltas: Vec<(Vec<u64>, f64)> = pairs.iter().map(|&(ai, bi)| {
        let d: Vec<u64> = b0.iter().map(|&q|
            (inv_mod(pool[bi] % q, q) + q - inv_mod(pool[ai] % q, q)) % q).collect();
        (d, 1.0 / pool[bi] as f64 - 1.0 / pool[ai] as f64)
    }).collect();
    let drift: f64 = deltas.iter().map(|d| d.1.abs()).sum();

    let h = (k / 2).min(24);                       // caps the table at 2^24 entries (~200 MB)
    let mut tab: Vec<(u64, u32)> = Vec::with_capacity(1usize << h);
    for s in 0u32..(1u32 << h) {
        let mut r = base.clone();
        for i in 0..h { if s >> i & 1 == 1 {
            for qi in 0..b0.len() { r[qi] = (r[qi] + deltas[i].0[qi]) % b0[qi]; } } }
        tab.push((enc(&r), s));
    }
    tab.sort_unstable();
    let rest = k - h;
    // Forcing q | beta does not stop q^2 | beta, and then the block contributes 1/q^2 instead of
    // 1/q. Collect many hits and keep one where every forced prime divides beta EXACTLY once,
    // tested by the same identity taken modulo q^2.
    let exact_ok = |sel: &Vec<bool>| -> bool {
        for &q in &b0 {
            let q2 = q * q;
            let mut s2m = 0u64;
            for i in 0..pool.len() { if sel[i] { s2m = (s2m + inv_mod(pool[i] % q2, q2)) % q2; } }
            let mut al = 1u64;
            for i in 0..pool.len() { if sel[i] { al = al * (pool[i] % q2) % q2; } }
            let b = al as u128 * s2m as u128 % q2 as u128;      // beta mod q^2
            if b % q as u128 != 0 { return false; }             // q | beta
            if b == 0 { return false; }                         // q^2 | beta: rejected
        }
        true
    };
    let mut found: Option<(u32, u32)> = None;
    let mut tried = 0u32;
    'outer: for s2 in 0u32..(1u32 << rest) {
        let mut r: Vec<u64> = vec![0; b0.len()];
        for i in 0..rest { if s2 >> i & 1 == 1 {
            for qi in 0..b0.len() { r[qi] = (r[qi] + deltas[h + i].0[qi]) % b0[qi]; } } }
        let need: Vec<u64> = (0..b0.len()).map(|qi| (b0[qi] - r[qi]) % b0[qi]).collect();
        let key = enc(&need);
        if let Ok(pos) = tab.binary_search_by_key(&key, |&(kk, _)| kk) {
            let mut lo2 = pos; while lo2 > 0 && tab[lo2 - 1].0 == key { lo2 -= 1; }
            let mut hi2 = pos; while hi2 + 1 < tab.len() && tab[hi2 + 1].0 == key { hi2 += 1; }
            for idx in lo2..=hi2 {
                let s1 = tab[idx].1;
                let mut sel = inA.clone();
                for i in 0..h { if s1 >> i & 1 == 1 {
                    let (ai, bi) = pairs[i]; sel[ai] = false; sel[bi] = true; } }
                for i in 0..rest { if s2 >> i & 1 == 1 {
                    let (ai, bi) = pairs[h + i]; sel[ai] = false; sel[bi] = true; } }
                tried += 1;
                if exact_ok(&sel) { found = Some((s1, s2)); break 'outer; }
                if tried > 4000 { break 'outer; }
            }
        }
    }
    println!("      (candidates tested for exact divisibility: {})", tried);

    match found {
        None => { println!("  M = {:>15}  pool>{:2}  |A0| = {:4}  k = {:2}  ->  NO SOLUTION", m, top, n_used, k); false }
        Some((s1, s2)) => {
            let mut xa = x;
            let mut sel = inA.clone();
            for i in 0..h { if s1 >> i & 1 == 1 {
                let (ai, bi) = pairs[i]; sel[ai] = false; sel[bi] = true; xa += deltas[i].1; } }
            for i in 0..rest { if s2 >> i & 1 == 1 {
                let (ai, bi) = pairs[h + i]; sel[ai] = false; sel[bi] = true; xa += deltas[h + i].1; } }
            let mut chk: Vec<u64> = vec![0; b0.len()];
            for i in 0..pool.len() { if sel[i] {
                for (qi, &q) in b0.iter().enumerate() { chk[qi] = (chk[qi] + inv_mod(pool[i] % q, q)) % q; } } }
            let all0 = chk.iter().all(|&v| v == 0);
            let a: Vec<u64> = (0..pool.len()).filter(|&i| sel[i]).map(|i| pool[i]).collect();
            println!("  M = {:>15}  pool>{:2}  |A| = {:4}  k = {:2}  ->  SOLVED  (all residues zero: {})",
                     m, top, a.len(), k, all0);
            println!("      x = {:.10}  1/x = {:.10}  y_max >= {:.6}  sieve {}  (mass drift < {:.1e})",
                     xa, 1.0 / xa, ymin, if ymin >= 1.0 / xa && xa > 1.0 { "PASSES" } else { "FAILS" }, drift);
            if verbose { println!("A = {:?}", a); }
            all0
        }
    }
}

fn main() {
    println!("Forcing small primes to divide beta, by solving the subset-sum congruences exactly.\n");
    for nb in 8usize..=13 {
        let b0: Vec<u64> = primes_upto(100).into_iter().take(nb).collect();
        let m: u64 = b0.iter().product();
        let k = ((m as f64).log2().ceil() as usize + 5).min(48);
        println!("forcing {:2} primes {:?}", nb, b0);
        run(b0, k, nb == 12);
    }
}
