// plushit_inverted.rs -- omega=2 plus-hits by INVERTING the search.  A semiprime v = pq is a plus-hit
// iff 2(v'+2v)+1 = (2p+1)(2q+1), so instead of scanning v <= N one scans r <= sqrt(7N/3) and factors
// 2r^2+1, sieved in r (2r^2 == -1 mod l has at most two roots per prime).  Cost drops from O(N) to
// about O(sqrt N).  Regression: reproduces all 1,787 omega=2 odd plus-hits below 3e8 exactly, no
// misses and no extras.  At 1e13 it finds 243,129 in 80 s.

// plusfast.rs -- inverted search for omega=2 plus-hits, via 2(v'+2v)+1 = (2p+1)(2q+1).
// A semiprime v = pq is a plus-hit iff 2r^2+1 = (2p+1)(2q+1) for some r, so instead of scanning
// v <= N (cost N) we scan r <= sqrt(2N) (cost sqrt(N)) and factor 2r^2+1.  The values 2r^2+1 are
// factored by SIEVING in r: for each small prime l, 2r^2 == -1 (mod l) has at most two roots, so
// each l touches O(range/l) values.  Memory is O(segment), independent of N.
fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    for &p in &[2u64,3,5,7,11,13,17,19,23,29,31,37] { if n % p == 0 { return n == p; } }
    let mut d = n - 1; let mut s = 0; while d % 2 == 0 { d /= 2; s += 1; }
    'w: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37] {
        let mut x = 1u128; let mut b = a as u128 % n as u128; let mut e = d;
        while e > 0 { if e & 1 == 1 { x = x * b % n as u128; } b = b * b % n as u128; e >>= 1; }
        if x == 1 || x == (n - 1) as u128 { continue; }
        for _ in 1..s { x = x * x % n as u128; if x == (n - 1) as u128 { continue 'w; } }
        return false;
    }
    true
}
fn rho(n: u128) -> Option<u128> {
    if n % 2 == 0 { return Some(2); }
    let mut c = 1u128;
    while c < 20 {
        let (mut x, mut y, mut d) = (2u128, 2u128, 1u128);
        let f = |v: u128| (v.wrapping_mul(v).wrapping_add(c)) % n;
        let mut steps = 0u64;
        while d == 1 && steps < 4_000_000 {
            x = f(x); y = f(f(y));
            let diff = if x > y { x - y } else { y - x };
            d = gcd(diff.max(1), n); steps += 1;
        }
        if d != 1 && d != n { return Some(d); }
        c += 1;
    }
    None
}
fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let nlim: u128 = args[1].parse().unwrap();          // bound on v
    let seg: usize = 1 << 20;
    // r^2 = 2v + (p+q) exactly, and p+q <= 3 + N/3 when p = 3, so r^2 <= 2N + N/3 + 3.
    // Using sqrt(2N) truncates the top of the range (28 of 1787 missed in the regression).
    let rmax: u64 = (((7.0 / 3.0) * nlim as f64 + 8.0).sqrt() as u64) + 2;
    // small primes for the sieve
    let bnd: u64 = 3_000_000;
    let mut sieve = vec![true; (bnd + 1) as usize];
    sieve[0] = false; sieve[1] = false;
    let mut i = 2usize; while i * i <= bnd as usize { if sieve[i] { let mut j = i*i; while j <= bnd as usize { sieve[j] = false; j += i; } } i += 1; }
    let small: Vec<u64> = (2..=bnd).filter(|&p| sieve[p as usize]).collect();
    // for each small prime l, roots of 2r^2 + 1 == 0 (mod l)
    let mut roots: Vec<(u64, Vec<u64>)> = vec![];
    for &l in &small {
        if l == 2 { if (2*1+1) % 2 == 0 {} continue; }
        let mut rs = vec![];
        // brute force roots for small l, Tonelli not needed at this size if l is small; use direct scan for l < 200
        if l < 200 { for r in 0..l { if (2*r*r + 1) % l == 0 { rs.push(r); } } }
        else {
            // r^2 == -inv(2) (mod l); test via Euler then Tonelli-Shanks
            let inv2 = (l + 1) / 2;                 // inverse of 2 mod l
            let a = (l - inv2 % l) % l;             // -1/2 mod l
            // Euler criterion
            let mut x = 1u128; let mut b = a as u128; let mut e = (l - 1) / 2;
            while e > 0 { if e & 1 == 1 { x = x * b % l as u128; } b = b * b % l as u128; e >>= 1; }
            if x == 1 {
                // Tonelli-Shanks
                let mut q = l - 1; let mut s = 0; while q % 2 == 0 { q /= 2; s += 1; }
                if s == 1 {
                    let mut r0 = 1u128; let mut b2 = a as u128; let mut e2 = (l + 1) / 4;
                    while e2 > 0 { if e2 & 1 == 1 { r0 = r0 * b2 % l as u128; } b2 = b2 * b2 % l as u128; e2 >>= 1; }
                    rs.push(r0 as u64); rs.push(l - r0 as u64);
                } else {
                    let mut z = 2u64; loop {
                        let mut x2 = 1u128; let mut b3 = z as u128; let mut e3 = (l - 1) / 2;
                        while e3 > 0 { if e3 & 1 == 1 { x2 = x2 * b3 % l as u128; } b3 = b3 * b3 % l as u128; e3 >>= 1; }
                        if x2 == (l - 1) as u128 { break; } z += 1; }
                    let powm = |mut b: u128, mut e: u64| { let mut r = 1u128; b %= l as u128; while e > 0 { if e & 1 == 1 { r = r * b % l as u128; } b = b * b % l as u128; e >>= 1; } r };
                    let mut m = s; let mut c = powm(z as u128, q); let mut t = powm(a as u128, q);
                    let mut r0 = powm(a as u128, (q + 1) / 2);
                    while t != 1 {
                        let mut i2 = 0; let mut tt = t; while tt != 1 { tt = tt * tt % l as u128; i2 += 1; }
                        let mut bb = c; for _ in 0..(m - i2 - 1) { bb = bb * bb % l as u128; }
                        m = i2; c = bb * bb % l as u128; t = t * c % l as u128; r0 = r0 * bb % l as u128;
                    }
                    rs.push(r0 as u64); rs.push(l - r0 as u64);
                }
            }
        }
        rs.sort(); rs.dedup();
        if !rs.is_empty() { roots.push((l, rs)); }
    }
    eprintln!("rmax {}  small primes with roots {}", rmax, roots.len());
    let mut hits: u64 = 0;
    let mut lo: u64 = 2;
    while lo <= rmax {
        let hi = (lo + seg as u64 - 1).min(rmax);
        let len = (hi - lo + 1) as usize;
        let mut rem: Vec<u128> = (lo..=hi).map(|r| 2u128*(r as u128)*(r as u128) + 1).collect();
        let mut fac: Vec<Vec<u64>> = vec![vec![]; len];
        for (l, rs) in &roots {
            for &rr in rs {
                let mut start = if rr >= lo % l { lo + (rr - lo % l) } else { lo + l - (lo % l - rr) };
                while start <= hi {
                    let idx = (start - lo) as usize;
                    while rem[idx] % (*l as u128) == 0 { rem[idx] /= *l as u128; fac[idx].push(*l); }
                    start += l;
                }
            }
        }
        for idx in 0..len {
            let r = lo + idx as u64;
            let mut divs: Vec<u128> = vec![1];
            for &p in &fac[idx] { let mut nd = divs.clone(); for d in &divs { nd.push(d * p as u128); } nd.sort(); nd.dedup(); divs = nd; }
            if rem[idx] > 1 {
                // split the cofactor fully; skipping composite cofactors loses hits whose 2r^2+1 has
                // two factors above the sieve bound (28 of 1787 in the regression range).
                let mut stack = vec![rem[idx]]; let mut ps: Vec<u128> = vec![]; let mut ok = true;
                while let Some(c) = stack.pop() {
                    if c == 1 { continue; }
                    if c <= u64::MAX as u128 && is_prime_u64(c as u64) { ps.push(c); continue; }
                    match rho(c) { Some(g) => { stack.push(g); stack.push(c / g); }, None => { ok = false; break; } }
                }
                if !ok { continue; }
                for p in ps { let mut nd = divs.clone(); for d in &divs { nd.push(d * p); } nd.sort(); nd.dedup(); divs = nd; }
            }
            let n = 2u128*(r as u128)*(r as u128) + 1;
            for &x in &divs {
                if x * x > n { break; }
                let y = n / x;
                if x * y != n || x < 7 { continue; }
                if (x - 1) % 2 != 0 || (y - 1) % 2 != 0 { continue; }
                let p = (x - 1) / 2; let q = (y - 1) / 2;
                if p == q || p < 3 { continue; }
                if p > u64::MAX as u128 || q > u64::MAX as u128 { continue; }
                if !is_prime_u64(p as u64) || !is_prime_u64(q as u64) { continue; }
                let v = p * q;
                if v > nlim { continue; }
                hits += 1;
                println!("HIT v={} p={} q={} r={}", v, p, q, r);
            }
        }
        lo = hi + 1;
    }
    eprintln!("omega=2 plus-hits with v <= {}: {}", nlim, hits);
}
