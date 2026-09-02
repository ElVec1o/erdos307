// sector_at60_list.rs -- emits every sector whose mass floor is |P u Q| = 60, with the run parameters
// (d, d', k, N) for sector_kexclude.rs phase 1.  Regression: 250 at primes <= 47, omega <= 8; 1,533 at
// primes <= 59, omega <= 10, the former a proper subset of the latter.  All 1,533 clear, 0 survivors.

// How many sectors d can have |P u Q| = 60 at their mass floor?
// At level 60 the support is a 59-prime base with every prime <= 787 (prop:close59) plus a tail, so
// d is squarefree with all prime factors <= 787.  Write K(d) = least k with S_k(d) >= T = d/d',
// S_k(d) the sum of the k smallest reciprocals of primes not dividing d*d'.  The mass floor is
// |P u Q| >= 1 + omega(d) + K(d), and the sector sits AT 60 exactly when omega(d) + K(d) = 59.
// DFS over the primes with pruning: from a partial set S at prime index i, any completion adding t
// further primes has omega = |S| + t and sigma <= sigma(S) + t/p_i, so K >= Kmin(1/(that sigma));
// if |S| + t + Kmin > 59 for every feasible t, the branch dies.
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i * i <= n { if n % i == 0 { return false; } i += 1; } true }
struct Ctx { pool: Vec<u64>, all: Vec<u64>, wmax: usize, hits: std::cell::RefCell<Vec<Vec<u64>>>, nodes: std::cell::Cell<u64> }
// K(d): least k with the k smallest allowed reciprocals summing to >= t
fn kof(all: &[u64], excl: &[u64], t: f64) -> usize {
    let mut s = 0.0; let mut k = 0;
    for &p in all { if excl.contains(&p) { continue; } s += 1.0 / p as f64; k += 1; if s >= t { return k; } }
    usize::MAX
}
fn sigma(s: &[u64]) -> f64 { s.iter().map(|&p| 1.0 / p as f64).sum() }
// arithmetic derivative support of a squarefree product, as primes
fn dprime_support(s: &[u64]) -> Vec<u64> {
    // d' = sum d/p ; we need its prime factors.  Compute d' exactly in u128 when possible.
    let mut d: u128 = 1; for &p in s { d = d.saturating_mul(p as u128); }
    if d == u128::MAX { return vec![]; }
    let mut dp: u128 = 0; for &p in s { dp += d / p as u128; }
    let mut out = vec![]; let mut x = dp; let mut f = 2u128;
    while f * f <= x && f < 1_000_000 { if x % f == 0 { out.push(f as u64); while x % f == 0 { x /= f; } } f += 1; }
    if x > 1 && x < u64::MAX as u128 { out.push(x as u64); }
    out
}
fn dfs(c: &Ctx, i: usize, cur: &mut Vec<u64>) {
    c.nodes.set(c.nodes.get() + 1);
    if !cur.is_empty() {
        let mut excl = cur.clone(); excl.extend(dprime_support(cur));
        let sg = sigma(cur);
        if sg > 0.0 {
            let mut k = kof(&c.all, &excl, 1.0 / sg);
            // parity: d even forces e odd, hence omega(e) even
            if k != usize::MAX && cur[0] == 2 && k % 2 == 1 { k += 1; }
            if k != usize::MAX && cur.len() + k == 59 {
                // emit run parameters: d, d', k, and the least truncation N with m>=1 excluded
                let d: u128 = cur.iter().fold(1u128, |a, &p| a * p as u128);
                let dp: u128 = cur.iter().map(|&p| d / p as u128).sum();
                let mut excl = cur.clone(); excl.extend(dprime_support(cur));
                let av: Vec<u64> = c.all.iter().cloned().filter(|p| !excl.contains(p)).collect();
                if av.len() > k + 2 {
                    let t = d as f64 / dp as f64;
                    let skm1: f64 = av[..k-1].iter().map(|&p| 1.0/p as f64).sum();
                    let mut n = k;
                    while n + 1 < av.len() && skm1 + 1.0/(av[n] as f64) >= t { n += 1; }
                    if skm1 + 1.0/(av[n] as f64) < t {
                        println!("{} {} {} {}", d, dp, k, n);
                        c.hits.borrow_mut().push(cur.clone());
                    }
                }
            }
        }
    }
    if cur.len() >= c.wmax || i >= c.pool.len() { return; }
    // prune: best case sigma from adding t primes starting at index i
    let sg = sigma(cur);
    let mut feasible = false;
    for t in 0..=(c.wmax - cur.len()).min(c.pool.len() - i) {
        let best_sigma = sg + (0..t).map(|j| 1.0 / c.pool[i + j] as f64).sum::<f64>();
        if best_sigma <= 0.0 { continue; }
        let kmin = kof(&c.all, &[], 1.0 / best_sigma);   // ignoring exclusions: a valid lower bound on K
        if kmin != usize::MAX && cur.len() + t + kmin <= 59 { feasible = true; break; }
    }
    if !feasible { return; }
    for j in i..c.pool.len() {
        cur.push(c.pool[j]); dfs(c, j + 1, cur); cur.pop();
    }
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let pcap: u64 = a[1].parse().unwrap(); let wmax: usize = a[2].parse().unwrap();
    let pool: Vec<u64> = (2..=pcap).filter(|&p| is_prime(p)).collect();
    let all: Vec<u64> = (2..20000u64).filter(|&p| is_prime(p)).collect();
    let c = Ctx { pool: pool.clone(), all, wmax, hits: std::cell::RefCell::new(vec![]), nodes: std::cell::Cell::new(0) };
    let mut cur = vec![];
    dfs(&c, 0, &mut cur);
    let h = c.hits.borrow();
    println!("primes <= {} (pool {}), omega <= {}: sectors at exactly 60 = {}   nodes {}",
        pcap, pool.len(), wmax, h.len(), c.nodes.get());
    for x in h.iter().take(3) { println!("   e.g. d = {:?}", x); }
}
