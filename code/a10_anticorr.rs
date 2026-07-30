// a10_anticorr.rs -- is sigma(a') SUPPRESSED when sigma(a) is large?
//
// A two-cycle needs r = sigma(a) sigma(a') = 1. The barrier explains why that is hard by forcing
// sigma(a) up to ~1/E[sigma(a')] ~ 2.2, hence 59 primes and 1e112.9. But that reasoning assumes
// sigma(a') is INDEPENDENT of sigma(a), sitting at its unconditional mean. If instead sigma(a')
// is suppressed as sigma(a) grows -- a genuine anti-correlation -- then r = 1 is harder than the
// barrier accounts for, and the obstruction is stronger than currently proved.
//
// This measures E[sigma(a') | sigma(a) >= t] against the unconditional mean, for growing t.
// Flat  => independence, the barrier already captures everything, nothing new.
// Falling => a NEW obstruction beyond the barrier.
fn main() {
    let a_max: usize = 10_000_000;
    let lim: usize = 40_000_000;
    let mut spf = vec![0u32; lim + 1];
    let mut i = 2usize;
    while i <= lim { if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } i += 1; }
    let deriv = |mut n: usize| -> Option<(u128, f64)> {   // (n', sigma(n))
        if n == 1 { return Some((0, 0.0)); }
        let orig = n as u128; let mut d: u128 = 0; let mut s = 0f64;
        while n > 1 { let p = spf[n] as usize; n /= p; if n % p == 0 { return None; } d += orig / p as u128; s += 1.0 / p as f64; }
        Some((d, s))
    };
    let ts = [0.0f64, 0.3, 0.5, 0.7, 0.9, 1.0, 1.1, 1.2, 1.3];
    let mut sum = vec![0f64; ts.len()]; let mut cnt = vec![0u64; ts.len()];
    let mut sum_om = vec![0f64; ts.len()];   // also track omega(a') : few large primes vs many small
    for a in 2..=a_max {
        let (da, sa) = match deriv(a) { Some(v) => v, None => continue };
        if da == 0 || da as usize > lim { continue; }
        let (_, sda) = match deriv(da as usize) { Some(v) => v, None => continue };
        // omega(a')
        let mut n = da as usize; let mut om = 0f64;
        while n > 1 { let p = spf[n] as usize; while n % p == 0 { n /= p; } om += 1.0; }
        for (k, &t) in ts.iter().enumerate() {
            if sa >= t { sum[k] += sda; cnt[k] += 1; sum_om[k] += om; }
        }
    }
    println!("{:>10} {:>12} {:>18} {:>16}", "sigma(a) >=", "count", "E[sigma(a')]", "E[omega(a')]");
    for (k, &t) in ts.iter().enumerate() {
        if cnt[k] > 0 {
            println!("{:>10.1} {:>12} {:>18.4} {:>16.2}", t, cnt[k], sum[k] / cnt[k] as f64, sum_om[k] / cnt[k] as f64);
        }
    }
    println!("\n  flat E[sigma(a')] => independence, barrier already captures it.");
    println!("  falling          => a NEW obstruction beyond the barrier.");
    if cnt[0] > 0 {
        let base = sum[0] / cnt[0] as f64;
        println!("\n  unconditional mean E[sigma(a')] = {:.4}", base);
        println!("  a solution needs sigma(a) >= 1/E[sigma(a')] ~ {:.2} if independent", 1.0 / base);
    }
}
