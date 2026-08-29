// f1_variance.rs -- does the prop:anticorr model get the SPREAD of sigma(a') right, not just the mean?
//
// f(1) is an integral of the JOINT density of (sigma(a), sigma(a')) along sigma(a)sigma(a') = 1.
// prop:anticorr validates the model's conditional MEAN of sigma(a'). A model can match a mean and
// still misstate a density, and f(1) is a density. This program tests the next moment.
//
// The model says: given supp(a), each prime q not dividing a lands in a' independently with
// probability 1/q. Hence, per a,
//      E[sigma(a')]   = sum_{q not | a} 1/q^2
//      Var[sigma(a')] = sum_{q not | a} (1/q^2)(1/q)(1 - 1/q)
// Both are computable exactly from supp(a), so the prediction is per-a, not merely aggregate.
//
// We bin by sigma(a) and compare measured mean and variance of sigma(a') against the averaged
// predictions. Ratios near 1 in both moments support f(1) > 0. A mean that matches while the
// variance drifts would mean the model's tail is wrong in exactly the direction f(1) depends on.
//
// Rule 8: single-threaded, bounded memory, progress reported.

fn main() {
    let a_max: usize = 10_000_000;
    let lim: usize = 40_000_000;
    eprintln!("sieving smallest prime factor to {} ...", lim);
    let mut spf = vec![0u32; lim + 1];
    let mut i = 2usize;
    while i <= lim {
        if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } }
        i += 1;
    }
    // tail sums over ALL primes, for the per-a prediction: subtract a's own primes
    let mut s2_all = 0f64;  // sum 1/q^2
    let mut s3_all = 0f64;  // sum (1/q^3)(1 - 1/q)
    for q in 2..=lim { if spf[q] as usize == q {
        let f = q as f64;
        s2_all += 1.0 / (f * f);
        s3_all += (1.0 / (f * f * f)) * (1.0 - 1.0 / f);
    }}
    eprintln!("sum 1/q^2 = {:.10}, sum (1/q^3)(1-1/q) = {:.10}", s2_all, s3_all);

    let decomp = |mut n: usize| -> Option<(u128, f64, f64, f64)> {
        // (n', sigma(n), sum over p|n of 1/p^2, sum over p|n of (1/p^3)(1-1/p))
        if n == 1 { return Some((0, 0.0, 0.0, 0.0)); }
        let orig = n as u128; let mut d: u128 = 0;
        let (mut s, mut e2, mut e3) = (0f64, 0f64, 0f64);
        while n > 1 {
            let p = spf[n] as usize; n /= p;
            if n % p == 0 { return None; }            // not squarefree
            let f = p as f64;
            d += orig / p as u128;
            s += 1.0 / f;
            e2 += 1.0 / (f * f);
            e3 += (1.0 / (f * f * f)) * (1.0 - 1.0 / f);
        }
        Some((d, s, e2, e3))
    };

    let bands = [0.0f64, 0.5, 0.7, 0.9, 1.0, 1.1, 1.2, 1.3];
    let n = bands.len();
    let mut cnt = vec![0u64; n];
    let mut sum_act = vec![0f64; n];
    let mut sum_act2 = vec![0f64; n];
    let mut sum_pm = vec![0f64; n];
    let mut sum_pv = vec![0f64; n];

    for a in 2..=a_max {
        if a % 2_000_000 == 0 { eprintln!("  a = {} ...", a); }
        let (da, sa, e2, e3) = match decomp(a) { Some(v) => v, None => continue };
        if da == 0 || da as usize > lim { continue; }
        let (_, sda, _, _) = match decomp(da as usize) { Some(v) => v, None => continue };
        let pm = s2_all - e2;              // predicted mean of sigma(a')
        let pv = s3_all - e3;              // predicted variance of sigma(a')
        for b in 0..n {
            if sa >= bands[b] {
                cnt[b] += 1;
                sum_act[b] += sda;
                sum_act2[b] += sda * sda;
                sum_pm[b] += pm;
                sum_pv[b] += pv;
            }
        }
    }

    println!();
    println!(" sigma(a) >= |    count | meas mean | pred mean | ratio | meas var  | pred var  | ratio");
    for b in 0..n {
        if cnt[b] == 0 { continue; }
        let c = cnt[b] as f64;
        let mm = sum_act[b] / c;
        let mv = sum_act2[b] / c - mm * mm;
        let pm = sum_pm[b] / c;
        let pv = sum_pv[b] / c;
        println!("   {:>6.2}    | {:>8} |  {:.6} |  {:.6} | {:.3} | {:.6}  | {:.6}  | {:.3}",
                 bands[b], cnt[b], mm, pm, mm / pm, mv, pv, mv / pv);
    }
}
