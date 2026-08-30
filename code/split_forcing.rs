// How much of the required divisibility of beta = alpha*sigma(alpha) can be forced?
//
// A two-cycle on a ground set U of primes is a split U = A u B with prod(B) = sum_{a in A} prod(A)/a.
// A necessary condition, one prime of B at a time, is lem:symbolfact with r = b:
//     b | beta   <=>   sum_{a in A} a^{-1} = 0  (mod b),
// which is a subset-sum condition on A alone and needs no factorisation of beta.
// This program maximises the forced divisor D(A) = prod{ b in B : the congruence holds }
// over splits obeying the mass window |x*y - 1| <= tol, by simulated annealing.
//
// Output is log10 D(A) against log10 beta: the fraction of the required divisibility
// that the congruence route can actually deliver.

fn primes(n: usize) -> Vec<u64> {
    let mut v = Vec::new();
    let mut c = 2u64;
    while v.len() < n {
        if (2..).take_while(|d| d * d <= c).all(|d| c % d != 0) { v.push(c); }
        c += 1;
    }
    v
}

fn inv_mod(a: u64, m: u64) -> u64 {
    // m prime, a not divisible by m
    let (mut b, mut e, mut r) = (a % m, m - 2, 1u64);
    while e > 0 {
        if e & 1 == 1 { r = r * b % m; }
        b = b * b % m;
        e >>= 1;
    }
    r
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0
    }
    fn f64(&mut self) -> f64 { (self.next() >> 11) as f64 / (1u64 << 53) as f64 }
}

fn main() {
    for k in [60usize, 62, 64, 66, 68, 70] {
        let u = primes(k);
        let t: f64 = u.iter().map(|&p| 1.0 / p as f64).sum();
        if t <= 2.0 { println!("k={:3}  T={:.6} <= 2, skipped", k, t); continue; }
        // inv[i][j] = p_i^{-1} mod p_j   (defined for i != j)
        let inv: Vec<Vec<u64>> = (0..k).map(|i| (0..k).map(|j|
            if i == j { 0 } else { inv_mod(u[i], u[j]) }).collect()).collect();
        let logp: Vec<f64> = u.iter().map(|&p| (p as f64).ln()).collect();

        let score = |a: &Vec<bool>| -> (f64, f64, f64) {
            let x: f64 = (0..k).filter(|&i| a[i]).map(|i| 1.0 / u[i] as f64).sum();
            let y: f64 = (0..k).filter(|&i| !a[i]).map(|i| 1.0 / u[i] as f64).sum();
            // forced divisor: primes b in B whose congruence is satisfied
            let mut forced = 0.0;
            for j in 0..k {
                if a[j] { continue; }
                let m = u[j];
                let mut s = 0u64;
                for i in 0..k { if a[i] { s = (s + inv[i][j]) % m; } }
                if s == 0 { forced += logp[j]; }
            }
            (forced, x, y)
        };

        let mut rng = Rng(0x243F6A8885A308D3 ^ (k as u64) << 32);

        // Phase 1: how close to x*y = 1 can a subset sum actually get?
        let mut best_dev = f64::MAX;
        for _r in 0..20 {
            let mut a: Vec<bool> = (0..k).map(|_| rng.f64() < 0.5).collect();
            let mut cur = score(&a);
            for step in 0..300_000u64 {
                let temp = 0.02 * (1.0 - step as f64 / 300_000.0) + 1e-5;
                let i = (rng.next() % k as u64) as usize;
                a[i] = !a[i];
                let cand = score(&a);
                let d0 = (cur.1 * cur.2 - 1.0).abs();
                let d1 = (cand.1 * cand.2 - 1.0).abs();
                if d1 <= d0 || rng.f64() < ((d0 - d1) / temp).exp() { cur = cand; }
                else { a[i] = !a[i]; }
                if (cur.1 * cur.2 - 1.0).abs() < best_dev { best_dev = (cur.1 * cur.2 - 1.0).abs(); }
            }
        }
        let tol = (best_dev * 10.0).max(1e-12);

        // Phase 2: the trade-off. Anneal on the forced divisor with a mild mass penalty and
        // record, for each mass-window width, the best forcing seen inside it.
        let thresholds = [1e-2_f64, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8];
        let mut bestf = [-1.0_f64; 7];
        let mut bestset: Vec<Vec<bool>> = vec![Vec::new(); 7];
        let mut bestxs = [0.0_f64; 7];
        for _restart in 0..60 {
            let mut a: Vec<bool> = (0..k).map(|_| rng.f64() < 0.5).collect();
            let mut cur = score(&a);
            for step in 0..400_000u64 {
                let temp = 0.8 * (1.0 - step as f64 / 400_000.0) + 0.01;
                let i = (rng.next() % k as u64) as usize;
                a[i] = !a[i];
                let cand = score(&a);
                let pen = |s: &(f64, f64, f64)| -> f64 {
                    s.0 - 60.0 * (s.1 * s.2 - 1.0).abs().ln().max(-40.0).abs().recip().recip() * 0.0
                        - 4.0 * ((s.1 * s.2 - 1.0).abs() / 1e-3).max(1.0).ln()
                };
                let (pc, pn) = (pen(&cur), pen(&cand));
                if pn >= pc || rng.f64() < ((pn - pc) / temp).exp() { cur = cand; }
                else { a[i] = !a[i]; }
                let dev = (cur.1 * cur.2 - 1.0).abs();
                for (ti, &th) in thresholds.iter().enumerate() {
                    if dev <= th && cur.0 > bestf[ti] {
                        bestf[ti] = cur.0; bestset[ti] = a.clone(); bestxs[ti] = cur.1;
                    }
                }
            }
        }
        println!("k={:3}  T={:.6}  best attainable |xy-1| = {:.3e}", k, t, best_dev);
        println!("      window      forced primes   log10 D    log10 beta   covered");
        for (ti, &th) in thresholds.iter().enumerate() {
            if bestf[ti] < 0.0 { println!("      {:.0e}      (none found)", th); continue; }
            let b = &bestset[ti];
            let nforced = { let mut c = 0;
                for jj in 0..k { if b[jj] { continue; }
                    let m = u[jj]; let mut ss = 0u64;
                    for ii in 0..k { if b[ii] { ss = (ss + inv[ii][jj]) % m; } }
                    if ss == 0 { c += 1; } } c };
            let nb = (0..k).filter(|&x| !b[x]).count();
            let l10a: f64 = (0..k).filter(|&x| b[x]).map(|x| (u[x] as f64).log10()).sum();
            let l10b = l10a + bestxs[ti].log10();
            let l10d = bestf[ti] / std::f64::consts::LN_10;
            println!("      {:.0e}        {:2} / {:2}      {:7.3}    {:8.3}     {:6.3}%",
                th, nforced, nb, l10d, l10b, 100.0 * l10d / l10b);
        }
        println!();
        continue;

    }
}
