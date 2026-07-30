// a10_density1.rs -- the constant that decides where the first two-cycle should live.
//
// a'' = a exactly iff r(a) := sigma(a) sigma(a') = 1. Since a'' = a*r ranges over ~2a integers,
// the heuristic probability that a'' lands exactly on a is f(1)/a, where f is the DENSITY of r
// near 1. Hence the expected number of two-cycles below X is f(1) * log X, and the first one is
// expected near log X = 1/f(1).
//
// This measures f(1) directly from the histogram of r, which is far more robust than fitting a
// handful of near-misses. It also reports the mass of r near 1 and the tail P(r >= 1), the
// large-deviation event a solution requires.
fn main() {
    let a_max: usize = 10_000_000;
    let lim: usize = 40_000_000;
    let mut spf = vec![0u32; lim + 1];
    let mut i = 2usize;
    while i <= lim { if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } i += 1; }
    let deriv = |mut n: usize| -> Option<u128> {
        if n == 1 { return Some(0); }
        let orig = n as u128; let mut d: u128 = 0;
        while n > 1 { let p = spf[n] as usize; n /= p; if n % p == 0 { return None; } d += orig / p as u128; }
        Some(d)
    };
    const NB: usize = 400;                 // bins over r in [0, 2]
    let mut hist = vec![0u64; NB + 1];
    let mut tot = 0u64; let mut ge1 = 0u64; let mut rmax = 0f64; let mut rmax_a = 0usize;
    // running max of r by decade: how fast does the near-miss frontier advance?
    let mut dec_max = [0f64; 9]; let mut dec_at = [0usize; 9];
    for a in 2..=a_max {
        let da = match deriv(a) { Some(v) => v, None => continue };
        if da == 0 || da as usize > lim { continue; }
        let dda = match deriv(da as usize) { Some(v) => v, None => continue };
        let r = (dda as f64) / (a as f64);
        tot += 1;
        if r >= 1.0 { ge1 += 1; }
        if r > rmax { rmax = r; rmax_a = a; }
        { let d = (a as f64).log10().floor() as usize; if d < 9 && r > dec_max[d] { dec_max[d] = r; dec_at[d] = a; } }
        let b = ((r / 2.0) * NB as f64).floor();
        if b >= 0.0 && b <= NB as f64 { hist[b as usize] += 1; }
    }
    let binw = 2.0 / NB as f64;
    // density at r = 1: average the bins straddling 1
    let b1 = (0.5 * NB as f64) as usize;
    let near: u64 = hist[b1 - 1] + hist[b1] + hist[b1 + 1];
    let f1 = (near as f64 / tot as f64) / (3.0 * binw);
    println!("pairs (a, a') both squarefree, a <= 1e7 : {}", tot);
    println!("max r = sigma(a)sigma(a') observed      : {:.4}  at a = {}", rmax, rmax_a);
    println!("P(r >= 1)                               : {:.3e}   ({} cases)", ge1 as f64 / tot as f64, ge1);
    println!("density f(1) of r at 1                  : {:.4e}", f1);
    println!();
    println!("expected two-cycles below X  =  f(1) * log X");
    for &lx in &[113.0f64, 1000.0, 10000.0] {
        println!("   log10 X = {:>7.0}  ->  expected {:.3e}", lx, f1 * lx * std::f64::consts::LN_10);
    }
    if f1 > 0.0 {
        let need = 1.0 / f1;
        println!("\nexpected count reaches 1 at log X = 1/f(1) = {:.3e}, i.e. log10 X = {:.3e}", need, need / std::f64::consts::LN_10);
    }
    println!("\nfrontier: largest r = sigma(a)sigma(a') seen in each decade");
    let mut run = 0f64;
    for d in 1..8 {
        if dec_max[d] > 0.0 {
            if dec_max[d] > run { run = dec_max[d]; }
            println!("   a < 10^{}  : max r = {:.4}  (running {:.4})  at a = {}", d + 1, dec_max[d], run, dec_at[d]);
        }
    }
    println!("\n  r must reach 1 for a solution. thm:barrier forbids r >= 1 below 10^112.9,");
    println!("  so the whole relevant regime is unsampleable and f(1) is NOT measurable.");
    println!("\nhistogram of r near 1 (bin width {:.3}):", binw);
    for b in (b1 - 6)..=(b1 + 6) {
        println!("   r in [{:.3},{:.3}) : {}", b as f64 * binw, (b + 1) as f64 * binw, hist[b]);
    }
}
