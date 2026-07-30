// region_shape.rs -- the achievable region R = {(sigma(n), sigma(n')) : n, n' squarefree}.
//
// Sprint 1/2 gate data. Measures, over squarefree n <= N with n' squarefree:
//   (1) max sigma(n) + sigma(n')            -- how close R gets to the half-mass threshold 2
//   (2) max sigma(n) * sigma(n') = n''/n    -- how close R gets to the hyperbola xy = 1
//   (3) min |sigma(n) - sigma(n')|          -- how close R gets to the diagonal (sigma is
//                                              injective, so the diagonal is never met)
//   (4) the same three restricted to sigma(n) > 1, the side a two-cycle's mass-rich member sits on
//   (5) max sigma(n') over windows of sigma(n) near 1 -- the "danger regime" of rem:lyapstatus
//
// A two-cycle is exactly a point of R on xy = 1 with x > 1; it has x + y > 2. So (1) and (2) are
// the two distances to the target, measured on the same sweep.
//
// Rule 8: single-threaded, bounded memory (4 bytes per sieve entry, cap = 2N), progress + ETA,
// atomic checkpoint every 20s, resume via argv[1].
use std::io::Write;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let resume: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
    let n_max: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(10_000_000);
    let cap: usize = 2 * n_max + 10;
    eprintln!("sieving spf to {} ({:.2} GB)...", cap, 4.0 * (cap as f64) / 1.073_741_824e9);
    let mut spf = vec![0u32; cap + 1];
    let mut i = 2usize;
    while i <= cap {
        if spf[i] == 0 {
            let mut j = i;
            while j <= cap {
                if spf[j] == 0 { spf[j] = i as u32; }
                j += i;
            }
        }
        i += 1;
    }
    eprintln!("sieve done; sweeping n from {} to {}", resume.max(2), n_max);

    // (sigma(n), n') for squarefree n; None if n is not squarefree.
    let fac = |mut n: usize| -> Option<(f64, u128)> {
        if n == 1 { return Some((0.0, 0)); }
        let orig = n as u128;
        let (mut s, mut d) = (0.0f64, 0u128);
        while n > 1 {
            let p = spf[n] as usize;
            n /= p;
            if n % p == 0 { return None; }
            s += 1.0 / p as f64;
            d += orig / (p as u128);
        }
        Some((s, d))
    };

    let (mut max_sum, mut max_sum_n) = (0.0f64, 0usize);
    let (mut max_prod, mut max_prod_n) = (0.0f64, 0usize);
    let (mut min_gap, mut min_gap_n) = (f64::INFINITY, 0usize);
    let (mut max_sum_hi, mut max_sum_hi_n) = (0.0f64, 0usize);   // restricted to sigma(n) > 1
    let (mut max_prod_hi, mut max_prod_hi_n) = (0.0f64, 0usize);
    // danger windows [1-10^-k, 1) and [1, 1+10^-k): largest sigma(n') seen
    let mut win_lo = [0.0f64; 5];
    let mut win_hi = [0.0f64; 5];
    let mut steps = 0u64;

    let t0 = std::time::Instant::now();
    let mut last = std::time::Instant::now();
    for n in resume.max(2)..=n_max {
        if let Some((s, d)) = fac(n) {
            if d > 1 && (d as usize) <= cap {
                if let Some((s2, _)) = fac(d as usize) {
                    steps += 1;
                    let sum = s + s2;
                    let prod = s * s2;
                    let gap = (s - s2).abs();
                    if sum > max_sum { max_sum = sum; max_sum_n = n; }
                    if prod > max_prod { max_prod = prod; max_prod_n = n; }
                    if gap < min_gap { min_gap = gap; min_gap_n = n; }
                    if s > 1.0 {
                        if sum > max_sum_hi { max_sum_hi = sum; max_sum_hi_n = n; }
                        if prod > max_prod_hi { max_prod_hi = prod; max_prod_hi_n = n; }
                    }
                    for k in 0..5 {
                        let e = 10f64.powi(-(k as i32) - 1);
                        if s >= 1.0 - e && s < 1.0 && s2 > win_lo[k] { win_lo[k] = s2; }
                        if s >= 1.0 && s < 1.0 + e && s2 > win_hi[k] { win_hi[k] = s2; }
                    }
                }
            }
        }
        if last.elapsed().as_secs_f64() > 20.0 {
            let el = t0.elapsed().as_secs_f64();
            let frac = (n - resume) as f64 / ((n_max - resume).max(1)) as f64;
            let eta = if frac > 1e-9 { el / frac - el } else { 0.0 };
            eprint!("\r  n={:>10}/{}  {:.2}%  steps {}  maxsum {:.6}  maxprod {:.6}  ETA {:.1}m   ",
                    n, n_max, 100.0 * frac, steps, max_sum, max_prod, eta / 60.0);
            let _ = std::io::stderr().flush();
            let tmp = "region_shape.progress.tmp";
            if let Ok(mut f) = std::fs::File::create(tmp) {
                let _ = writeln!(f, "n {} steps {} maxsum {:.9} maxprod {:.9} mingap {:.9}",
                                 n, steps, max_sum, max_prod, min_gap);
                let _ = std::fs::rename(tmp, "region_shape.progress");
            }
            last = std::time::Instant::now();
        }
    }

    println!("\n\nn <= {}: {} steps (squarefree n with n' squarefree)", n_max, steps);
    println!("  max sigma(n)+sigma(n')      = {:.9}   at n = {}   [threshold 2 of thm:halflyap]",
             max_sum, max_sum_n);
    println!("  max sigma(n)*sigma(n')=n''/n= {:.9}   at n = {}   [target value 1]",
             max_prod, max_prod_n);
    println!("  min |sigma(n)-sigma(n')|    = {:.3e}   at n = {}   [lem:sigmainj: never 0]",
             min_gap, min_gap_n);
    println!("  restricted to sigma(n) > 1:");
    println!("    max sum  = {:.9} at n = {}", max_sum_hi, max_sum_hi_n);
    println!("    max prod = {:.9} at n = {}", max_prod_hi, max_prod_hi_n);
    println!("  danger windows (largest sigma(n') seen):");
    for k in 0..5 {
        let e = 10f64.powi(-(k as i32) - 1);
        println!("    sigma(n) in [1-{:.0e},1) : {:.6}      sigma(n) in [1,1+{:.0e}) : {:.6}",
                 e, win_lo[k], e, win_hi[k]);
    }
}
