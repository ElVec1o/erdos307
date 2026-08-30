// A cheap rejection sieve for candidate two-cycle splits, using no factorisation at all.
//
// For a split U = A u B of a ground set of primes, the partner is beta = sum_{a in A} prod(A)/a.
// If a coprime family B is to satisfy sum_{b in B} 1/b = alpha/beta, then B is a coprime
// factorisation of beta, and the largest reciprocal sum any coprime factorisation can reach is the
// one by prime powers:            y_max(beta) = sum_{p^e || beta} 1/p^e.
// So  y_max(beta) >= alpha/beta = 1/x  is NECESSARY.
//
// By lem:symbolfact with r = p^e (valid since p does not divide alpha),
//        beta = alpha * sum_{a in A} a^{-1}   (mod p^e),
// so the whole smoothness profile of beta is computable in small modular arithmetic: beta itself
// is never formed, and nothing is factored. Primes above the trial bound contribute below
// 1/BOUND each, so the computed value is an upper bound for y_max up to a negligible tail.

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
    let (mut old_r, mut r) = (a as i128, m as i128);
    let (mut old_s, mut s) = (1i128, 0i128);
    while r != 0 { let q = old_r / r;
        let t = old_r - q * r; old_r = r; r = t;
        let t = old_s - q * s; old_s = s; s = t; }
    (((old_s % m as i128) + m as i128) % m as i128) as u64
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 {
    self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn f64(&mut self) -> f64 { (self.next() >> 11) as f64 / (1u64 << 53) as f64 } }

fn main() {
    const BOUND: u64 = 100_000;          // trial bound for the smoothness profile
    let small = primes_upto(BOUND);
    let k = 60usize;
    let u: Vec<u64> = primes_upto(300).into_iter().take(k).collect();
    let t: f64 = u.iter().map(|&p| 1.0 / p as f64).sum();
    println!("ground set: {} primes up to {}, T = {:.6}", k, u[k - 1], t);
    println!("trial bound {}, tail per prime < {:.1e}\n", BOUND, 1.0 / BOUND as f64);

    let mut rng = Rng(0x9E3779B97F4A7C15);
    let (mut n, mut pass) = (0u64, 0u64);
    let mut smax = 0.0_f64;
    let mut ssum = 0.0_f64;
    let mut hist = [0u64; 12];
    let trials = 20_000;

    for _ in 0..trials {
        // a split with x*y near 1 (loose window; tighter only makes the sieve reject more)
        let a: Vec<bool> = (0..k).map(|_| rng.f64() < 0.5).collect();
        let x: f64 = (0..k).filter(|&i| a[i]).map(|i| 1.0 / u[i] as f64).sum();
        let y: f64 = t - x;
        if (x * y - 1.0).abs() > 1e-2 { continue; }
        let need = 1.0 / x;                       // = alpha/beta
        let aset: Vec<u64> = (0..k).filter(|&i| a[i]).map(|i| u[i]).collect();

        // y_max(beta) = sum over prime powers exactly dividing beta
        let mut ymax = 0.0_f64;
        for &p in &small {
            if aset.contains(&p) { continue; }    // p | alpha, so p does not divide beta
            // highest e with p^e | beta, capped at 2 (higher powers are negligible here)
            let mut modulus = p;
            let mut e = 0u32;
            for _ in 0..2 {
                let mut s: u128 = 0;
                for &aa in &aset { s += inv_mod(aa % modulus, modulus) as u128; }
                let mut alpha = 1u128;
                for &aa in &aset { alpha = alpha * (aa % modulus) as u128 % modulus as u128; }
                if (alpha * (s % modulus as u128)) % modulus as u128 == 0 { e += 1; modulus *= p; }
                else { break; }
            }
            if e > 0 { ymax += 1.0 / (p.pow(e) as f64); }
        }
        n += 1;
        ssum += ymax;
        if ymax > smax { smax = ymax; }
        let b = ((ymax * 10.0) as usize).min(11);
        hist[b] += 1;
        if ymax >= need { pass += 1; }
    }

    println!("splits inside the loose mass window: {}", n);
    println!("required  y_max >= 1/x  ~ {:.4}", 0.95);
    println!("mean y_max            = {:.4}", ssum / n as f64);
    println!("max  y_max observed   = {:.4}", smax);
    println!("splits passing        = {} / {}   ({:.4}%)", pass, n, 100.0 * pass as f64 / n as f64);
    println!("\nhistogram of y_max:");
    for (i, &c) in hist.iter().enumerate() {
        if c == 0 { continue; }
        println!("  [{:.1},{:.1})  {:6}  {}", i as f64 / 10.0, (i + 1) as f64 / 10.0, c,
                 "#".repeat((60.0 * c as f64 / n as f64) as usize));
    }
}
