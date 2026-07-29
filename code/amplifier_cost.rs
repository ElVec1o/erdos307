// amplifier_cost.rs — does the residue amplifier survive its own cost?
//
// rem:amplifier: for f_c(d) = d^2 + c, an admissible odd prime l (i.e. (-c|l) = +1) divides
// values with density 2/l, DOUBLE the random 1/l. A friendly c -- one making many small primes
// admissible -- therefore accumulates mass far faster than a random integer.
//
// But friendliness is not free. Each odd prime is admissible for only half the c, so forcing
// the first 58 odd primes costs a factor 2^-58 in c-space. The prediction is an EXACT
// CANCELLATION: over the 59 smallest primes,
//
//     (density of friendly c)  x  (amplified hit probability)
//        =  2^-58  x  (1/2) prod_{i=2}^{59} (2/l_i)  =  prod_{i=1}^{59} 1/l_i ,
//
// which is exactly the random-integer probability. If so, the quadratic reformulation is
// heuristically NEUTRAL: rem:amplifier's bias is real for a fixed friendly c and vanishes on
// average over c, so the YES lean of rem:killcount is neither strengthened nor weakened.
//
// TEST: average over c of P_d[sigma_B(f_c(d)) > T], against P_n[sigma_B(n) > T] for random n.
// Cancellation predicts the two agree.
//
// Build: rustc -O -o amplifier_cost amplifier_cost.rs
// Run:   ./amplifier_cost [D CMAX B]     default 200000 400 5000

fn primes_upto(n: usize) -> Vec<u64> {
    let mut is = vec![true; n + 1]; is[0] = false; if n >= 1 { is[1] = false; }
    let mut i = 2; while i * i <= n { if is[i] { let mut j = i * i; while j <= n { is[j] = false; j += i; } } i += 1; }
    (2..=n).filter(|&x| is[x]).map(|x| x as u64).collect()
}
fn sqrt_mod(a: u64, p: u64) -> Option<u64> {
    let a = a % p;
    if a == 0 { return Some(0); }
    for x in 1..p { if (x * x) % p == a { return Some(x); } }
    None
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let d_max: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(200_000);
    let c_max: u64   = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(400);
    let b: usize     = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(5_000);
    let pr = primes_upto(b);
    let thresholds = [0.8f64, 1.0, 1.2, 1.4];

    // ---- average over c of the quadratic's tail probabilities ----
    let mut acc = vec![0f64; thresholds.len()];
    let mut acc_mean = 0f64;
    let mut nc = 0u64;
    // also track the two extremes to show the spread the average is hiding
    let (mut best_mean, mut worst_mean) = (0f64, f64::MAX);
    for c in 1..=c_max {
        let mut sigma = vec![0f64; d_max + 1];
        for &p in &pr {
            let target = (p - (c % p)) % p;
            let r = match sqrt_mod(target, p) { Some(r) => r, None => continue };
            let mut roots = vec![r];
            if r != 0 && p != 2 && p - r != r { roots.push(p - r); }
            for r0 in roots {
                let mut d = r0 as usize; if d == 0 { d = p as usize; }
                while d <= d_max { sigma[d] += 1.0 / p as f64; d += p as usize; }
            }
        }
        let mut cnt = vec![0u64; thresholds.len()];
        let mut mean = 0f64;
        for d in 1..=d_max {
            mean += sigma[d];
            for (i, &t) in thresholds.iter().enumerate() { if sigma[d] > t { cnt[i] += 1; } }
        }
        mean /= d_max as f64;
        if mean > best_mean { best_mean = mean; }
        if mean < worst_mean { worst_mean = mean; }
        acc_mean += mean;
        for i in 0..thresholds.len() { acc[i] += cnt[i] as f64 / d_max as f64; }
        nc += 1;
    }
    for i in 0..thresholds.len() { acc[i] /= nc as f64; }
    acc_mean /= nc as f64;

    // ---- control: random integers ----
    let mut sigma = vec![0f64; d_max + 1];
    for &p in &pr { let mut n = p as usize; while n <= d_max { sigma[n] += 1.0 / p as f64; n += p as usize; } }
    let mut cnt = vec![0u64; thresholds.len()];
    let mut mean_r = 0f64;
    for n in 1..=d_max {
        mean_r += sigma[n];
        for (i, &t) in thresholds.iter().enumerate() { if sigma[n] > t { cnt[i] += 1; } }
    }
    mean_r /= d_max as f64;

    println!("averaged over c = 1..{}, d <= {}, primes <= {}\n", c_max, d_max, b);
    println!("mean sigma_B:  quadratic (avg over c) = {:.5}   random integers = {:.5}   ratio {:.4}",
             acc_mean, mean_r, acc_mean / mean_r);
    println!("  (spread hidden by the average: worst c {:.4}, best c {:.4})\n", worst_mean, best_mean);
    println!("{:>6} {:>16} {:>16} {:>10}", "T", "quad avg P[>T]", "random P[>T]", "ratio");
    for (i, &t) in thresholds.iter().enumerate() {
        let r = cnt[i] as f64 / d_max as f64;
        let ratio = if r > 0.0 { acc[i] / r } else { f64::NAN };
        println!("{:>6.1} {:>16.3e} {:>16.3e} {:>10.4}", t, acc[i], r, ratio);
    }
    println!("\nprediction: ratios ~ 1 (amplifier exactly paid for by the rarity of friendly c)");
}
