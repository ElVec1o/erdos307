// pairsector_countdp.rs -- independent binned counting DP corroborating pairsector_count.rs (1.8e7).
// Build: rustc -O -o pairsector_countdp pairsector_countdp.rs   Run: ./pairsector_countdp 3e-7

// Level-60 pair sector, exact window, ONE incremental pass.
// U = R u {m}, |R| = 59, m prime > M = max(R), T(R) <= 2 < T(R) + 1/m.
// A tail exists only if T(R) > 2 - 1/M, so with M = max(R): T(R \ {M}) in (2 - 2/M, 2 - 1/M].
// Process primes in increasing order; before adding prime M, dp holds all subsets of primes < M,
// so dp[58] queried at that moment is exactly the 58-subsets below M.  One pass, not one per M.
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i * i <= n { if n % i == 0 { return false; } i += 1; } true }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let bin: f64 = a[1].parse().unwrap();
    let pool: Vec<u64> = (2..1588u64).filter(|&p| is_prime(p)).collect();
    let nb = (2.05 / bin) as usize + 2;
    eprintln!("pool {} primes; DP {:.2} GB; one pass", pool.len(), 59.0 * nb as f64 * 8.0 / 1e9);
    let mut dp: Vec<Vec<f64>> = vec![vec![0.0; nb]; 59]; dp[0][0] = 1.0;
    let mut total = 0f64; let mut rows = 0;
    for &m in &pool {
        // query first: dp currently covers exactly the primes strictly below m
        let lo = 2.0 - 2.0 / m as f64; let hi = 2.0 - 1.0 / m as f64;
        let blo = ((lo / bin) as usize).saturating_sub(1); let bhi = ((hi / bin) as usize + 1).min(nb);
        if blo < bhi { let c: f64 = dp[58][blo..bhi].iter().sum();
            if c > 0.0 { total += c; rows += 1;
                if rows <= 8 || m > 1500 { println!("  M={:5}  T(R\\M) in ({:.7}, {:.7}]  count {:.4e}", m, lo, hi, c); } } }
        // then insert m
        let w = ((1.0 / m as f64) / bin) as usize;
        for c in (0..58).rev() { let (l, r) = dp.split_at_mut(c + 1);
            for b in 0..nb - w { let v = l[c][b]; if v != 0.0 { r[0][b + w] += v; } } }
    }
    println!("TOTAL level-60 pair-sector bases R (exact per-M window): {:.4e}   [{} values of M contribute]", total, rows);
}
