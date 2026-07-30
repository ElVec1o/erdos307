// a10_weighted.rs -- the weighted count: WHERE should the first two-cycle be?
//
// prop:nearmiss showed the constant in the heuristic count cannot be measured, since the whole
// region r = sigma(a)sigma(a') >= 1 lies above the barrier. So compute it instead. prop:anticorr
// licenses the model: sigma(a') behaves exactly like the mass of a random integer COPRIME to a
// (measured/predicted ratio -> 1.01 precisely in the relevant regime), with no residual effect.
//
// Setup. A two-cycle is a'' = a, i.e. sigma(a') = 1/sigma(a) exactly. For a with sigma(a) = t,
// a'' is a determined integer of size ~a, so it lands on a with probability ~rho(a)/a where
// rho(a) is the density of r at 1. Writing r = t*s with s = sigma(a'), that density is g_P(1/t)/t,
// g_P being the density of sigma(n) over n coprime to the support P of a. Hence
//
//     E[#two-cycles with a <= X]  =  C log X,     C = E_P[ g_P(1/t) / t ],
//
// and the first two-cycle is expected near log X = 1/C.
//
// g_P(s) is a LARGE DEVIATION: the mean of sigma(n) over n coprime to P is sum_{p not in P} 1/p^2,
// which is tiny once P holds the small primes, while we need s = 1/t ~ 0.5. Computed by saddle
// point on the independent model, psi(th) = sum_{p not in P} log(1 + (e^{th/p}-1)/p):
//     g_P(s) ~ exp(psi(th) - th*s) / sqrt(2 pi psi''(th)),   psi'(th) = s.
// P itself is sampled from the same model, each prime p included with probability 1/p.
fn main() {
    let pmax: usize = 2_000_000;
    let mut sieve = vec![true; pmax + 1];
    sieve[0] = false; if pmax >= 1 { sieve[1] = false; }
    let mut i = 2usize;
    while i * i <= pmax { if sieve[i] { let mut j = i * i; while j <= pmax { sieve[j] = false; j += i; } } i += 1; }
    let pr: Vec<f64> = (2..=pmax).filter(|&x| sieve[x]).map(|x| x as f64).collect();
    let np = pr.len();

    // deterministic LCG: no Date/rand needed, and the run is reproducible
    let mut st: u64 = 0x243F6A8885A308D3;
    let mut rnd = || { st ^= st << 13; st ^= st >> 7; st ^= st << 17; (st >> 11) as f64 / (1u64 << 53) as f64 };

    // psi and derivatives over the primes NOT in P (in_p is a bitmask over indices)
    let psi = |th: f64, in_p: &[bool]| -> f64 {
        let mut v = 0.0;
        for k in 0..np { if in_p[k] { continue; }
            let u = th / pr[k];
            let e = if u > 700.0 { return f64::INFINITY } else { u.exp_m1() };
            v += (e / pr[k]).ln_1p();
        }
        v
    };
    let dpsi = |th: f64, in_p: &[bool]| -> f64 {
        let mut v = 0.0;
        for k in 0..np { if in_p[k] { continue; }
            let p = pr[k]; let u = th / p;
            if u > 700.0 { return f64::INFINITY }
            let e = u.exp();
            v += (e / (p * p)) / (1.0 + (e - 1.0) / p);
        }
        v
    };

    let trials = 400;
    let mut acc = 0.0f64; let mut used = 0u32;
    let mut best_c = 0.0f64;
    for _ in 0..trials {
        // sample the support P of a: prime p included with probability 1/p
        let mut in_p = vec![false; np];
        let mut t = 0.0f64;
        for k in 0..np { if rnd() < 1.0 / pr[k] { in_p[k] = true; t += 1.0 / pr[k]; } }
        if t < 0.35 { continue; }                 // need 1/t reachable at all
        let s = 1.0 / t;
        // saddle point: solve psi'(th) = s
        let (mut lo, mut hi) = (0.0f64, 1e7f64);
        if dpsi(hi, &in_p) < s { continue; }       // s unreachable with these primes
        for _ in 0..200 { let m = 0.5 * (lo + hi); if dpsi(m, &in_p) < s { lo = m; } else { hi = m; } }
        let th = 0.5 * (lo + hi);
        let h = (th * 1e-4).max(1e-3);
        let d2 = (dpsi(th + h, &in_p) - dpsi(th - h, &in_p)) / (2.0 * h);
        if !(d2 > 0.0) || !d2.is_finite() { continue; }
        let ln_g = psi(th, &in_p) - th * s - 0.5 * (2.0 * std::f64::consts::PI * d2).ln();
        let contrib = (ln_g - t.ln()).exp();
        if contrib.is_finite() { acc += contrib; used += 1; if contrib > best_c { best_c = contrib; } }
    }
    let c = acc / used.max(1) as f64;
    println!("samples used: {} of {}", used, trials);
    println!("C = E[ g_P(1/t) / t ]        = {:.4e}", c);
    println!("largest single contribution  = {:.4e}", best_c);
    println!("\nE[#two-cycles with a <= X] = C log X");
    for &l10 in &[113.0f64, 1000.0, 1e6] {
        println!("   log10 X = {:>9.0}  ->  expected {:.3e}", l10, c * l10 * std::f64::consts::LN_10);
    }
    if c > 0.0 {
        let lx = 1.0 / c;
        println!("\nexpected count reaches 1 at  log X = 1/C = {:.4e},  i.e. log10 X = {:.4e}", lx, lx / std::f64::consts::LN_10);
    } else {
        println!("\nC underflowed to 0: the deviation is beyond double precision.");
    }
}
