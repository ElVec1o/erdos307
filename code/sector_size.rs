// sector_size.rs -- how many prime sets the sector enumerator would test, by a counting DP over binned mass.
// Build: rustc -O -o sector_size sector_size.rs   Run: ./sector_size <excl> <T> <k> <N> <mmax> <bin>
// Calibrated against the real k=64 run at d=42: predicts 3.49e10 phase-1 sets against 3.69e10 actual.

// Exact-structure sizing: counts the sets the enumerator would actually test.
// Phase 1 analogue (<=1 prime above A_N): k-1 primes from the first N, mass in [T - 1/A_k, T).
// Phase m>=2: k-m primes from the first N, mass in [T - m/A_(N+1), T).
// Binned at `bin`, one bin of slack each side (upper bound on the true count).
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i * i <= n { if n % i == 0 { return false; } i += 1; } true }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let excl: u64 = a[1].parse().unwrap(); let t: f64 = a[2].parse().unwrap();
    let k: usize = a[3].parse().unwrap(); let nn: usize = a[4].parse().unwrap();
    let mmax: usize = a[5].parse().unwrap(); let bin: f64 = a[6].parse().unwrap();
    let mut allowed = vec![]; let mut p = 2u64; while allowed.len() < 5000 { if is_prime(p) && excl % p != 0 { allowed.push(p); } p += 1; }
    let nb = ((t + 0.01) / bin) as usize + 2;
    let mem = (k + 1) as f64 * nb as f64 * 8.0 / 1e9;
    eprintln!("preflight: DP table {:.2} GB", mem); if mem > 6.0 { eprintln!("REFUSED: coarsen bin"); std::process::exit(1); }
    println!("excl={} T={:.12} k={} N={} A_N={} A_(N+1)={} A_k={}", excl, t, k, nn, allowed[nn-1], allowed[nn], allowed[k-1]);
    let jmax = k - 1;
    let mut dp: Vec<Vec<f64>> = vec![vec![0.0; nb]; jmax + 1]; dp[0][0] = 1.0;
    for &q in &allowed[..nn] { let w = ((1.0 / q as f64) / bin) as usize;
        for c in (0..jmax).rev() { let (l, r) = dp.split_at_mut(c + 1);
            for b in 0..nb - w { let v = l[c][b]; if v != 0.0 { r[0][b + w] += v; } } } }
    let mut tot = 0f64;
    for m in 0..=mmax {
        let (j, lo) = if m <= 1 { (k - 1, t - 1.0 / allowed[k-1] as f64) } else { (k - m, t - m as f64 / allowed[nn] as f64) };
        if j > jmax || j == 0 { continue; }
        let blo = ((lo / bin) as usize).saturating_sub(1); let bhi = ((t / bin) as usize + 1).min(nb);
        let c: f64 = dp[j][blo..bhi].iter().sum();
        println!("  {:<10} j={:3}  window [{:.9}, {:.9})  sets ~ {:.4e}", if m <= 1 { "m<=1" } else { "m" }, j, lo, t, c);
        tot += c; if m == 0 { } }
    println!("  TOTAL ~ {:.4e}", tot);
}
