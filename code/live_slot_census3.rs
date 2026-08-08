// live_slot_census3.rs -- live-slot census with the d-loop replaced by a congruence solve.
//
// THE IDEA. The census tests whether A s^2 + B d^2 = 4 N_0^2 with A = 2N_0 - N_0', B = 2N_0 + N_0'.
// Version 2 looped over d <= dmax ~ 0.24 sqrt(N_0) and tested divisibility. That is unnecessary:
// since 2 N_0 = N_0' (mod A),
//      4 N_0^2 = N_0'^2  and  B = 2 N_0' (mod A),
// so  A | 4N_0^2 - B d^2  <=>  A | N_0' (N_0' - 2 d^2).
// Let h be the part of A coprime to N_0'. Then a solution forces
//      2 d^2 = N_0'   (mod h),
// a quadratic congruence, which is SOLVED rather than searched: factor h, take square roots modulo
// each prime power, and combine by CRT. Cost falls from O(sqrt N_0) to O(h^{1/4}) for the
// factorisation, which is the whole speedup.
//
// Two facts keep it clean. gcd(N_0', h) = 1 by construction, so c = N_0' * inv2 is a unit mod h and
// no degenerate roots arise. And if h is even then N_0' is odd, so 2 d^2 = N_0' (mod 2) is
// unsolvable and the base dies at once.
//
// Correctness: the congruence is EQUIVALENT to the divisibility, so no candidate is lost; every
// surviving d is then verified against the original equation directly, so no false positive can
// survive either. h = 1 makes the congruence vacuous, and those bases fall back to the loop.
//
// MEMORY (Rule 8): O(1). Prime tables of 38 KB, recursion depth under 20, a handful of roots per
// base. No allocation grows with the range, so there is no OOM risk at any bound.
// Progress, ETA, atomic checkpoint, resume, as in version 2.
//
// Usage: ./live_slot_census3 <xmax> [resume_count]

use std::io::Write;

fn primes_upto(n: usize) -> Vec<u32> {
    let mut s = vec![true; n + 1];
    s[0] = false; if n >= 1 { s[1] = false; }
    let mut i = 2;
    while i * i <= n {
        if s[i] { let mut j = i * i; while j <= n { s[j] = false; j += i; } }
        i += 1;
    }
    (2..=n).filter(|&i| s[i]).map(|i| i as u32).collect()
}

fn isqrt(n: u128) -> u128 {
    if n == 0 { return 0; }
    let mut x = (n as f64).sqrt() as u128 + 2;
    loop { let y = (x + n / x) / 2; if y >= x { break; } x = y; }
    while x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}

fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }

/// modular inverse of a mod m (gcd(a,m) = 1), by extended Euclid on i128
fn inv_mod(a: u128, m: u128) -> u128 {
    let (mut old_r, mut r) = (a as i128, m as i128);
    let (mut old_s, mut s) = (1i128, 0i128);
    while r != 0 {
        let q = old_r / r;
        let tr = old_r - q * r; old_r = r; r = tr;
        let ts = old_s - q * s; old_s = s; s = ts;
    }
    let mi = m as i128;
    (((old_s % mi) + mi) % mi) as u128
}

/// direct u128 modmul: safe while m < 2^63, which holds for every bound we use
#[inline(always)]
fn mm(a: u128, b: u128, m: u128) -> u128 { (a * b) % m }

fn powm(mut b: u128, mut e: u128, m: u128) -> u128 {
    let mut r = 1u128; b %= m;
    while e > 0 { if e & 1 == 1 { r = mm(r, b, m); } b = mm(b, b, m); e >>= 1; }
    r
}

fn is_prime(n: u128) -> bool {
    if n < 2 { return false; }
    for p in [2u128,3,5,7,11,13,17,19,23,29,31,37] { if n % p == 0 { return n == p; } }
    let mut d = n - 1; let mut r = 0;
    while d % 2 == 0 { d /= 2; r += 1; }
    'o: for a in [2u128,3,5,7,11,13,17,19,23,29,31,37] {
        let mut x = powm(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 1..r { x = mm(x, x, n); if x == n - 1 { continue 'o; } }
        return false;
    }
    true
}

/// Brent-Pollard rho
fn rho(n: u128) -> u128 {
    if n % 2 == 0 { return 2; }
    let mut c = 1u128;
    loop {
        let f = |x: u128| (mm(x, x, n) + c) % n;
        let (mut x, mut y, mut d) = (2u128, 2u128, 1u128);
        while d == 1 {
            x = f(x); y = f(f(y));
            d = gcd(if x > y { x - y } else { y - x }, n);
        }
        if d != n { return d; }
        c += 1;
    }
}

fn factor(mut n: u128, small: &[u32], out: &mut Vec<(u128, u32)>) {
    out.clear();
    for &p in small {
        let p = p as u128;
        if p * p > n { break; }
        if n % p == 0 { let mut e = 0; while n % p == 0 { n /= p; e += 1; } out.push((p, e)); }
    }
    let mut stack = vec![n];
    while let Some(m) = stack.pop() {
        if m == 1 { continue; }
        if is_prime(m) {
            if let Some(t) = out.iter_mut().find(|t| t.0 == m) { t.1 += 1; } else { out.push((m, 1)); }
            continue;
        }
        let d = rho(m);
        stack.push(d); stack.push(m / d);
    }
}

/// Tonelli-Shanks: sqrt of a mod odd prime p, assuming a is a QR
fn sqrt_mod_p(a: u128, p: u128) -> Option<u128> {
    let a = a % p;
    if a == 0 { return Some(0); }
    if powm(a, (p - 1) / 2, p) != 1 { return None; }
    if p % 4 == 3 { return Some(powm(a, (p + 1) / 4, p)); }
    let mut q = p - 1; let mut s = 0;
    while q % 2 == 0 { q /= 2; s += 1; }
    let mut z = 2u128;
    while powm(z, (p - 1) / 2, p) != p - 1 { z += 1; }
    let mut m = s; let mut c = powm(z, q, p);
    let mut t = powm(a, q, p); let mut r = powm(a, (q + 1) / 2, p);
    while t != 1 {
        let mut i = 0; let mut t2 = t;
        while t2 != 1 { t2 = mm(t2, t2, p); i += 1; if i == m { return None; } }
        let b = powm(c, 1u128 << (m - i - 1), p);
        m = i; c = mm(b, b, p); t = mm(t, c, p); r = mm(r, b, p);
    }
    Some(r)
}

/// sqrt of a mod p^e by Hensel lifting (p odd, gcd(a,p)=1)
fn sqrt_mod_pe(a: u128, p: u128, e: u32) -> Option<u128> {
    let mut r = sqrt_mod_p(a, p)?;
    let mut pk = p;
    for _ in 1..e {
        let pk1 = pk * p;
        // lift: r' = r - (r^2 - a) * inv(2r) mod p^{k+1}
        let f = ((mm(r, r, pk1) + pk1) - (a % pk1)) % pk1;
        let inv2r = powm(mm(2, r, pk1), pk1 / p * (p - 1) - 1, pk1); // Euler inverse
        r = ((r + pk1) - mm(f, inv2r, pk1)) % pk1;
        pk = pk1;
    }
    Some(r)
}

struct Stats { bases: u64, dead_even: u64, dead_qr: u64, solved: u64, fallback: u64, reps: u64, live: u64 }

fn check(n0: u128, np: u128, small: &[u32], st: &mut Stats, fac: &mut Vec<(u128, u32)>)
    -> Option<(u128, u128, u128)> {
    if np >= 2 * n0 { return None; }
    let a = 2 * n0 - np;
    let b = 2 * n0 + np;
    let num = 2 * np * np + np * n0;
    if num <= 6 * n0 * n0 { return None; }          // sigma < 3/2 (prop:liveslot)
    let dmax = isqrt((num - 6 * n0 * n0) / b);
    let t4 = 4 * n0 * n0;

    // verify one candidate d against the original equation
    let mut test = |d: u128, st: &mut Stats| -> Option<(u128, u128, u128)> {
        if d > dmax { return None; }
        let bd2 = b * d * d;
        if bd2 > t4 { return None; }
        let rem = t4 - bd2;
        if rem % a != 0 { return None; }
        let s2 = rem / a;
        let s = isqrt(s2);
        if s * s != s2 { return None; }
        st.reps += 1;
        if s * s <= n0 { return None; }
        let nr = s * s - n0;
        if nr % b != 0 { return None; }
        let r = nr / b;
        if r <= 1 || gcd(r, n0) != 1 || !is_prime(r) { return None; }
        st.live += 1;
        Some((s, d, r))
    };

    // h = part of A coprime to N_0'
    let mut h = a;
    loop { let g = gcd(h, np); if g == 1 || h == 1 { break; } h /= g; }
    if h == 1 {                                       // congruence vacuous: fall back
        st.fallback += 1;
        for d in 0..=dmax { if let Some(v) = test(d, st) { return Some(v); } }
        return None;
    }
    if h % 2 == 0 { st.dead_even += 1; return None; }  // 2d^2 = odd mod 2 is unsolvable

    // c = N_0' * inv2 mod h, a unit
    let inv2 = (h + 1) / 2;
    let c = mm(np % h, inv2, h);
    factor(h, small, fac);
    // roots mod each prime power, then CRT
    let mut roots: Vec<u128> = vec![0];
    let mut modulus: u128 = 1;
    for &(q, e) in fac.iter() {
        let qe = q.pow(e);
        let r0 = match sqrt_mod_pe(c % qe, q, e) { Some(r) => r, None => { st.dead_qr += 1; return None; } };
        let cand = if r0 == 0 { vec![0] } else { vec![r0, qe - r0] };
        let mut nr = Vec::with_capacity(roots.len() * cand.len());
        for &x in roots.iter() {
            for &y in cand.iter() {
                // CRT combine x mod modulus with y mod qe, by inverse rather than search
                let diff = ((y % qe) + qe - (x % qe)) % qe;
                let t = mm(diff, inv_mod(modulus % qe, qe), qe);
                nr.push(x + modulus * t);
            }
        }
        roots = nr;
        modulus *= qe;
        if roots.len() > 4096 { break; }
    }
    st.solved += 1;
    for &d0 in roots.iter() {
        let mut d = d0;
        while d <= dmax { if let Some(v) = test(d, st) { return Some(v); } d += modulus; if modulus == 0 { break; } }
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn dfs(i: usize, n0: u128, np: u128, sig: f64, xmax: u128, dp: &[u32], small: &[u32],
       st: &mut Stats, resume: u64, t0: &std::time::Instant, last: &mut std::time::Instant,
       fac: &mut Vec<(u128, u32)>, xs: &str) {
    if sig >= 1.5 && n0 > 1 {
        st.bases += 1;
        if st.bases > resume {
            if let Some((s, d, r)) = check(n0, np, small, st, fac) {
                println!("\n  *** LIVE SLOT *** N_0 = {}  s = {}  d = {}  r = {}", n0, s, d, r);
                let _ = std::io::stdout().flush();
            }
        }
        if last.elapsed().as_secs_f64() > 20.0 {
            let el = t0.elapsed().as_secs_f64();
            eprint!("\r  bases {}  dead(even) {}  dead(QR) {}  solved {}  fallback {}  reps {}  live {}  {:.0}/s  {:.1}m   ",
                    st.bases, st.dead_even, st.dead_qr, st.solved, st.fallback, st.reps, st.live,
                    st.bases.saturating_sub(resume) as f64 / el.max(1e-9), el / 60.0);
            let _ = std::io::stderr().flush();
            if let Ok(mut f) = std::fs::File::create("live_slot_census3.progress.tmp") {
                let _ = writeln!(f, "xmax {} bases_done {} dead_even {} dead_qr {} solved {} fallback {} reps {} live {} elapsed_s {:.0}",
                                 xs, st.bases, st.dead_even, st.dead_qr, st.solved, st.fallback, st.reps, st.live, el);
                let _ = std::fs::rename("live_slot_census3.progress.tmp", "live_slot_census3.progress");
            }
            *last = std::time::Instant::now();
        }
    }
    let mut opt = sig; let mut prod = n0;
    for j in i..dp.len() {
        let p = dp[j] as u128;
        if prod > xmax / p { break; }
        prod *= p; opt += 1.0 / p as f64;
        if opt >= 1.5 { break; }
    }
    if opt < 1.5 { return; }
    for j in i..dp.len() {
        let p = dp[j] as u128;
        if n0 > xmax / p { break; }
        dfs(j + 1, n0 * p, np * p + n0, sig + 1.0 / p as f64, xmax, dp, small, st, resume, t0, last, fac, xs);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let xmax: u128 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1_000_000_000_000_000);
    let resume: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    let dp = primes_upto(3000);
    let small = primes_upto(200_000);
    eprintln!("live-slot census v3 (congruence solve), xmax = {}, resume {}", xmax, resume);
    let mut st = Stats { bases: 0, dead_even: 0, dead_qr: 0, solved: 0, fallback: 0, reps: 0, live: 0 };
    let mut fac: Vec<(u128, u32)> = Vec::with_capacity(16);
    let t0 = std::time::Instant::now();
    let mut last = std::time::Instant::now();
    let xs = format!("{}", xmax);
    dfs(0, 1, 0, 0.0, xmax, &dp, &small, &mut st, resume, &t0, &mut last, &mut fac, &xs);
    println!("\n\nxmax = {}", xmax);
    println!("  bases with sigma >= 3/2 : {}", st.bases);
    println!("  dead, h even            : {}", st.dead_even);
    println!("  dead, non-residue       : {}", st.dead_qr);
    println!("  congruence solved       : {}", st.solved);
    println!("  fallback loops (h = 1)  : {}", st.fallback);
    println!("  representations found   : {}", st.reps);
    println!("  LIVE slots (r prime >1) : {}", st.live);
    println!("  elapsed {:.2} min", t0.elapsed().as_secs_f64() / 60.0);
}
