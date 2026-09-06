// twoside_conditional.rs -- the conditional near-miss law behind rem:twosided.
//
// A two-cycle needs r(a) = sigma(a) sigma(a') = 1. Proposition nearmiss records the GLOBAL maximum
// of r by decade. This records the CONDITIONAL shape, which is what makes the two-sided obstruction
// visible: given sigma(a) near 1, how large can sigma(a') be?
//
// The answer is that sigma(a') is actively suppressed there. sigma(a) near 1 requires a to carry the
// small primes; gcd(a, a') = 1 then forces a' to avoid them, so a' is built from larger primes and
// its mass is small. This is why the primary pseudoperfect numbers, which satisfy the one-sided
// equation with |sigma(n) - 1| = 1/n, never threaten the barrier: for them a' = a - 1 is prime or
// nearly so and sigma(a') collapses.
//
// Both a and a' are required squarefree, since a cycle has squarefree members.
//
// Build: rustc -O -o twoside_conditional twoside_conditional.rs
// Run:   ./twoside_conditional [N]         (default 8000000)
// Output: one row per bucket of sigma(a), with the count, the mean and max of sigma(a'), and max r.

fn main() {
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(8_000_000);
    let m = n + n / 4 + 16;                 // a' can exceed a, so sieve past n
    let mut spf: Vec<u32> = (0..=m as u32).collect();
    let mut i = 2usize;
    while i * i <= m {
        if spf[i] == i as u32 {
            let mut j = i * i;
            while j <= m { if spf[j] == j as u32 { spf[j] = i as u32; } j += i; }
        }
        i += 1;
    }
    // squarefree factorisation; None if a square factor appears or the value is out of range
    let fac = |mut x: usize| -> Option<Vec<u32>> {
        if x > m { return None; }
        let mut f = Vec::new();
        while x > 1 {
            let p = spf[x];
            let mut c = 0;
            while x % p as usize == 0 { x /= p as usize; c += 1; }
            if c > 1 { return None; }
            f.push(p);
        }
        Some(f)
    };
    const B: usize = 23;                    // buckets for sigma(a) in [0.90, 1.12]
    let mut cnt = [0u64; B];
    let mut sum = [0f64; B];
    let mut mx  = [0f64; B];
    let (mut best_r, mut best_a) = (0f64, 0usize);
    for a in 2..=n {
        let pa = match fac(a) { Some(v) => v, None => continue };
        let s: f64 = pa.iter().map(|&p| 1.0 / p as f64).sum();
        if s <= 0.90 || s >= 1.125 { continue; }
        let ap: usize = pa.iter().map(|&p| a / p as usize).sum();
        let pb = match fac(ap) { Some(v) => v, None => continue };
        let sp: f64 = pb.iter().map(|&q| 1.0 / q as f64).sum();
        let k = (((s - 0.90) * 100.0).round() as usize).min(B - 1);
        cnt[k] += 1; sum[k] += sp; if sp > mx[k] { mx[k] = sp; }
        if s * sp > best_r { best_r = s * sp; best_a = a; }
    }
    println!("N = {}", n);
    println!("sigma(a)  count      mean sigma(a')   max sigma(a')   max r in bucket");
    for k in 0..B {
        if cnt[k] < 100 { continue; }
        let s = 0.90 + k as f64 / 100.0;
        println!("  {:.2}   {:>8}      {:.4}           {:.4}          {:.4}",
                 s, cnt[k], sum[k] / cnt[k] as f64, mx[k], s * mx[k]);
    }
    println!("max r over the window: {:.4} at a = {}", best_r, best_a);
}
