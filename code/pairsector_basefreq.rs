// pairsector_basefreq.rs -- per-prime frequency over all 18,234,653 pair-sector bases (the null), for
// comparison against the survivors of the reciprocity certificate.  The null profile is monotonic in p.

// Per-prime frequency over ALL pair-sector bases (the null), to compare against the survivors.
// A deviation would mean the reciprocity kill is correlated with particular primes.
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i*i <= n { if n % i == 0 { return false; } i += 1; } true }
fn main() {
    let pool: Vec<u64> = (2..1588u64).filter(|&p| is_prime(p)).collect();
    let n = pool.len();
    let inv: Vec<f64> = pool.iter().map(|&p| 1.0/p as f64).collect();
    let mut pre = vec![vec![0.0; 61]; n+1]; let mut suf = vec![vec![0.0; 61]; n+1];
    for i in 0..n { let mut rem: Vec<f64> = inv[i..].to_vec(); rem.sort_by(|a,b| b.partial_cmp(a).unwrap());
        for c in 1..=60 { if c <= rem.len() { pre[i][c] = rem[..c].iter().sum(); suf[i][c] = rem[rem.len()-c..].iter().sum(); } else { pre[i][c] = f64::NEG_INFINITY; suf[i][c] = f64::INFINITY; } } }
    let lo = 2.0 - 1.0/pool[58] as f64 - 1e-12; let hi = 2.0;
    let mut cnt = vec![0u64; n]; let mut total: u64 = 0; let mut sel: Vec<usize> = Vec::with_capacity(60);
    fn dfs(i: usize, need: usize, m: f64, pool: &[u64], inv: &[f64], pre: &[Vec<f64>], suf: &[Vec<f64>],
           lo: f64, hi: f64, n: usize, sel: &mut Vec<usize>, cnt: &mut Vec<u64>, total: &mut u64) {
        if need == 0 {
            let mx = pool[*sel.last().unwrap()];
            if m <= hi + 1e-12 && m > 2.0 - 1.0/mx as f64 - 1e-12 {
                *total += 1; for &s in sel.iter() { cnt[s] += 1; } }
            return; }
        if i + need > n { return; }
        if pre[i][need] < 0.0 || m + pre[i][need] <= lo { return; }
        if m + suf[i][need] > hi + 1e-12 { return; }
        sel.push(i); dfs(i+1, need-1, m + inv[i], pool, inv, pre, suf, lo, hi, n, sel, cnt, total); sel.pop();
        dfs(i+1, need, m, pool, inv, pre, suf, lo, hi, n, sel, cnt, total);
    }
    dfs(0, 59, 0.0, &pool, &inv, &pre, &suf, lo, hi, n, &mut sel, &mut cnt, &mut total);
    println!("total bases {}", total);
    for s in 0..n { if cnt[s] > 0 && cnt[s] < total { println!("{} {:.4}", pool[s], 100.0*cnt[s] as f64/total as f64); } }
}
