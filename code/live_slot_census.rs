// live_slot_census.rs -- census of LIVE slots in the decoupled (plus-automatic) family.
//
// prop:form: for squarefree N_0 and prime r not dividing N_0, a Pythagorean pair over N_0 gives a
// representation of 4N_0^2 by Q(s,d) = A s^2 + B d^2 with
//      A = 2N_0 - N_0' = N_0(2 - sigma),     B = E_0 = 2N_0 + N_0' = N_0(2 + sigma),
// and the recovered slot is r = (s^2 - N_0)/B, which must be a positive integer, prime, coprime to
// N_0. The slot r = 1 is the "ghost" and is not admissible.
//
// THRESHOLD (proved here, and the reason the earlier census was empty). A live slot needs r >= 2,
// i.e. s^2 >= N_0(5 + 2 sigma). Positive definiteness gives A s^2 <= 4 N_0^2, i.e.
// s^2 <= 4 N_0/(2 - sigma). Both can hold only if (5 + 2 sigma)(2 - sigma) <= 4, that is
//      2 sigma^2 + sigma - 6 >= 0,   whose positive root is exactly 3/2.
// So a live slot forces sigma(N_0) >= 3/2, hence omega(N_0) >= 10 and N_0 >= Pi_10 = 6469693230,
// since sigma(Pi_9) = 1.498956 < 3/2 <= 1.533439 = sigma(Pi_10). The census of prop:form ran to
// N_0 <= 5e4, below the threshold by a factor 1.3e5, so it could not have found a live slot. This
// program searches the region where one is possible.
//
// The same inequality bounds d tightly, which is what makes the region searchable:
//      B d^2 <= 4N_0^2 - A * N_0(5 + 2 sigma)  =>  d^2 <= N_0 (2 sigma^2 + sigma - 6)/(2 + sigma),
// small when sigma is just above 3/2.
//
// Rule 8: u128 throughout (N_0^2 exceeds u64), no large allocations, progress and a cap.

fn primes_upto(n: usize) -> Vec<u64> {
    let mut s = vec![true; n + 1];
    s[0] = false;
    if n >= 1 { s[1] = false; }
    let mut i = 2;
    while i * i <= n {
        if s[i] { let mut j = i * i; while j <= n { s[j] = false; j += i; } }
        i += 1;
    }
    (2..=n).filter(|&i| s[i]).map(|i| i as u64).collect()
}

fn isqrt(n: u128) -> u128 {
    if n == 0 { return 0; }
    let mut x = (n as f64).sqrt() as u128;
    while x > 0 && x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}

fn is_prime_u128(n: u128) -> bool {
    if n < 2 { return false; }
    for p in [2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 { return n == p; }
    }
    // Miller-Rabin, deterministic for n < 3.3e24 with these bases
    let mut d = n - 1; let mut r = 0;
    while d % 2 == 0 { d /= 2; r += 1; }
    'outer: for a in [2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = 1u128; let mut b = a % n; let mut e = d;
        while e > 0 { if e & 1 == 1 { x = mulmod(x, b, n); } b = mulmod(b, b, n); e >>= 1; }
        if x == 1 || x == n - 1 { continue; }
        for _ in 1..r { x = mulmod(x, x, n); if x == n - 1 { continue 'outer; } }
        return false;
    }
    true
}

/// (a*b) mod m for m < 2^126, via u128 splitting
fn mulmod(a: u128, b: u128, m: u128) -> u128 {
    let mut res = 0u128; let mut a = a % m; let mut b = b;
    while b > 0 { if b & 1 == 1 { res = (res + a) % m; } a = (a * 2) % m; b >>= 1; }
    res
}

fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }

/// check one base N_0 given its prime set; returns Some((s,d,r)) on a live slot
fn check(n0: u128, np: u128, primes: &[u64], hits: &mut u64, tested: &mut u64) -> Option<(u128, u128, u128)> {
    // A = 2N_0 - N_0', B = 2N_0 + N_0'
    if np >= 2 * n0 { return None; }              // sigma >= 2: handled by the barrier, and N_0 >= Pi_59
    let a = 2 * n0 - np;
    let b = 2 * n0 + np;
    let target = 4u128 * n0 * n0;
    // d^2 <= N_0 (2 sigma^2 + sigma - 6)/(2 + sigma), computed integrally:
    // 2 sigma^2 + sigma - 6 = (2 np^2 + np n0 - 6 n0^2)/n0^2, and 2 + sigma = b/n0.
    // so d^2 <= (2 np^2 + np*n0 - 6 n0^2)/(n0 * b) * n0 = (2 np^2 + np*n0 - 6 n0^2)/b
    let num = 2 * np * np + np * n0;
    if num <= 6 * n0 * n0 { return None; }        // sigma < 3/2: no live slot possible
    let dmax2 = (num - 6 * n0 * n0) / b;
    let dmax = isqrt(dmax2);
    for d in 0..=dmax {
        let bd2 = b * d * d;
        if bd2 > target { break; }
        let rem = target - bd2;
        if rem % a != 0 { continue; }
        let s2 = rem / a;
        let s = isqrt(s2);
        if s * s != s2 { continue; }
        *tested += 1;
        if s * s <= n0 { continue; }
        let num_r = s * s - n0;
        if num_r % b != 0 { continue; }
        let r = num_r / b;
        if r <= 1 { continue; }                    // the ghost slot
        if gcd(r, n0) != 1 { continue; }
        if !is_prime_u128(r) { continue; }
        *hits += 1;
        return Some((s, d, r));
    }
    None
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let xmax: u128 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2_000_000_000_000);
    let ps = primes_upto(3000);
    println!("Census of LIVE slots (r prime > 1) in the decoupled family.");
    println!("Threshold proved in the header: a live slot needs sigma(N_0) >= 3/2, hence");
    println!("N_0 >= Pi_10 = 6469693230. Searching squarefree N_0 <= {} with sigma >= 3/2.\n", xmax);

    let mut bases: u64 = 0;
    let mut reps: u64 = 0;
    let mut hits: u64 = 0;
    let mut found: Vec<(u128, u128, u128, u128)> = Vec::new();

    // DFS over increasing primes: state (index, N_0, N_0' as integer, sigma as f64)
    // N_0' = sum over p | N_0 of N_0/p, maintained exactly.
    fn dfs(i: usize, n0: u128, np: u128, sig: f64, xmax: u128, ps: &[u64],
           bases: &mut u64, reps: &mut u64, hits: &mut u64,
           found: &mut Vec<(u128, u128, u128, u128)>) {
        // prune: max mass reachable by multiplying in remaining primes within the bound
        if sig >= 1.5 && n0 > 1 {
            *bases += 1;
            if let Some((s, d, r)) = check(n0, np, ps, hits, reps) {
                println!("  *** LIVE SLOT *** N_0 = {}  s = {}  d = {}  r = {}", n0, s, d, r);
                found.push((n0, s, d, r));
            }
        }
        // optimistic bound: adding the next primes greedily
        let mut opt = sig;
        let mut prod = n0;
        for j in i..ps.len() {
            let p = ps[j] as u128;
            if prod > xmax / p { break; }
            prod *= p;
            opt += 1.0 / p as f64;
            if opt >= 1.5 { break; }
        }
        if opt < 1.5 { return; }
        for j in i..ps.len() {
            let p = ps[j] as u128;
            if n0 > xmax / p { break; }
            let n0b = n0 * p;
            let npb = np * p + n0;         // (N_0 p)' = N_0' p + N_0
            dfs(j + 1, n0b, npb, sig + 1.0 / p as f64, xmax, ps, bases, reps, hits, found);
        }
    }
    dfs(0, 1, 0, 0.0, xmax, &ps, &mut bases, &mut reps, &mut hits, &mut found);

    println!("\nbases with sigma >= 3/2 examined: {}", bases);
    println!("representations of 4N_0^2 found:  {}", reps);
    println!("LIVE slots (r prime > 1):         {}", hits);
    if found.is_empty() {
        println!("\nNo live slot below {}. The region above Pi_10 is now swept too.", xmax);
    }
}
