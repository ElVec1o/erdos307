// sector_at60_count.rs -- how many sectors can have |P u Q| = 60 at their mass floor.
// Build: rustc -O -o sector_at60_count sector_at60_count.rs   Run: ./sector_at60_count <prime cap> <omega cap>
// Regression: reproduces the verified 250 at primes <= 47, omega <= 8 (code/sector_at60.gp).

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
    // d' = sum d/p ; we need ALL its prime factors.  A missing factor is unsound in the wrong
    // direction: it never matches a prime in `kof`, so the exclusion set is too small, K(d) too
    // small, and the floor too low -- a sector at 60 could be misread as below 60 and skipped.
    // Trial division alone tops out well before omega(d)=10, where d' exceeds 10^14 and routinely
    // carries a large prime factor, so this factors d' completely with Pollard rho.
    let mut d: u128 = 1; for &p in s { d = d.saturating_mul(p as u128); }
    if d == u128::MAX { panic!("d overflowed u128"); }
    let mut dp: u128 = 0; for &p in s { dp += d / p as u128; }
    // mulmod below is exact only while the modulus stays under 2^64 (it reduces a u128 product of
    // two residues).  d' passes that near omega(d)=13 with primes <= 107, so refuse rather than
    // silently return a wrong factorisation: a missing factor shrinks the exclusion set and lowers
    // the computed floor, which is the unsound direction.
    if dp >= (1u128 << 127) { panic!("d' = {} exceeds 2^127; mulmod would overflow -- widen it before raising omega or the prime cap", dp); }
    let mut out = vec![]; factor_u128(dp, &mut out); out.sort_unstable(); out.dedup(); out
}
fn mulmod(a: u128, b: u128, m: u128) -> u128 {
    // Below 2^64 the u128 product is exact and this is one multiply.  Above it the product would
    // overflow, so fall back to shift-and-add, which needs only m < 2^127 for r + a to fit.  That is
    // what lets the prime cap pass 71: at primes <= 89 with omega(d) = 12, d' is already about
    // 5 x 10^19, over 2^64 = 1.8 x 10^19.
    if m < (1u128 << 64) { return (a % m) * (b % m) % m; }
    let (mut a, mut b, mut r) = (a % m, b % m, 0u128);
    while b > 0 { if b & 1 == 1 { r = (r + a) % m; } a = (a + a) % m; b >>= 1; }
    r
}
fn powmod(mut a: u128, mut e: u128, m: u128) -> u128 {
    let mut r: u128 = 1; a %= m;
    while e > 0 { if e & 1 == 1 { r = mulmod(r, a, m); } a = mulmod(a, a, m); e >>= 1; }
    r
}
fn is_prime_u128(n: u128) -> bool {
    if n < 2 { return false; }
    for p in [2u128,3,5,7,11,13,17,19,23,29,31,37] { if n % p == 0 { return n == p; } }
    let mut d = n - 1; let mut r = 0; while d % 2 == 0 { d /= 2; r += 1; }
    // deterministic for n < 3.3e24 with this witness set
    'w: for a in [2u128,3,5,7,11,13,17,19,23,29,31,37] {
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 1..r { x = mulmod(x, x, n); if x == n - 1 { continue 'w; } }
        return false;
    }
    true
}
fn pollard_rho(n: u128) -> u128 {
    if n % 2 == 0 { return 2; }
    let mut c: u128 = 1;
    loop {
        let (mut x, mut y, mut d) = (2u128, 2u128, 1u128);
        while d == 1 {
            x = (mulmod(x, x, n) + c) % n;
            y = (mulmod(y, y, n) + c) % n; y = (mulmod(y, y, n) + c) % n;
            let diff = if x > y { x - y } else { y - x };
            d = gcd_u128(diff, n);
        }
        if d != n { return d; }
        c += 1;
    }
}
fn gcd_u128(mut a: u128, mut b: u128) -> u128 { while b != 0 { let t = a % b; a = b; b = t; } a }
fn factor_u128(n: u128, out: &mut Vec<u64>) {
    if n <= 1 { return; }
    if is_prime_u128(n) { out.push(n as u64); return; }
    let d = pollard_rho(n);
    factor_u128(d, out); factor_u128(n / d, out);
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
            if k != usize::MAX && cur.len() + k == 59 { c.hits.borrow_mut().push(cur.clone()); }
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
