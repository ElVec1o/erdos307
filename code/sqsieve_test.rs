// sqsieve_test.rs — Rule 3 test of the square-sieve attack on A9.
//
// A9 <=> #{m <= Z : m' - 2m is a perfect square} = o(Z). Heath-Brown's square sieve needs the
// character sums  S(r) = sum_{m <= N, sqfree, (m,r)=1} ( (m'-2m) / r )  to exhibit cancellation,
// for r prime and for r = pq. If they do not, the sieve cannot run and the attack is dead before
// any theory is written.
//
// Also tested: the claimed factorisation ( (m'-2m)/r ) = (m/r) * ((sigma_r(m)-2)/r), which is what
// makes the Gauss-sum expansion decouple into a MULTIPLICATIVE sum over m.
//
// Build: rustc -O -o sqsieve_test sqsieve_test.rs
fn jacobi(mut a: i64, mut n: i64) -> i64 {
    if n <= 0 || n % 2 == 0 { return 0; }
    a = ((a % n) + n) % n;
    let mut t = 1i64;
    while a != 0 {
        while a % 2 == 0 { a /= 2; let r = n % 8; if r == 3 || r == 5 { t = -t; } }
        std::mem::swap(&mut a, &mut n);
        if a % 4 == 3 && n % 4 == 3 { t = -t; }
        a %= n;
    }
    if n == 1 { t } else { 0 }
}
fn inv(a: i64, p: i64) -> i64 { // p prime
    let (mut b, mut e, mut r) = (a % p, p - 2, 1i64);
    while e > 0 { if e & 1 == 1 { r = r * b % p; } b = b * b % p; e >>= 1; }
    r
}
fn main() {
    let lim: usize = 50_000_000;
    let mut spf = vec![0u32; lim + 1];
    for i in 2..=lim { if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } }
    let mut der = vec![0i64; lim + 1]; let mut sf = vec![false; lim + 1]; sf[1] = true;
    for n in 2..=lim {
        let p = spf[n] as usize; let q = n / p;
        if q % p == 0 || !sf[q] { continue; }
        sf[n] = true; der[n] = if q > 1 { der[q] * p as i64 + q as i64 } else { 1 };
    }
    let n = lim as f64;
    println!("N = {:e}   sqrt(N) = {:.3e}\n", n, n.sqrt());
    println!("{:>8} {:>14} {:>12} {:>12}   {}", "r", "S(r)", "|S|/N", "|S|/sqrt(N)", "verdict");
    for &r in &[101i64, 1009, 10007, 100003, 101*1009, 1009*10007] {
        let mut s = 0i64; let mut cnt = 0u64; let mut factor_bad = 0u64;
        for m in 2..=lim {
            if !sf[m] { continue; }
            let mm = m as i64;
            if mm % r == 0 { continue; }
            let v = der[m] - 2 * mm;
            let j = jacobi(v, r);
            s += j; cnt += 1;
            // verify the factorisation on a sample, prime r only
            if cnt % 5_000_000 == 0 && (r == 101 || r == 1009 || r == 10007 || r == 100003) {
                let mut sig = 0i64; let mut t = m;
                while t > 1 { let p = spf[t] as i64; sig = (sig + inv(p % r, r)) % r; while t % (p as usize) == 0 { t /= p as usize; } }
                let lhs = jacobi(v, r);
                let rhs = jacobi(mm, r) * jacobi((sig - 2 % r + 2 * r) % r, r);
                if lhs != rhs { factor_bad += 1; }
            }
        }
        let a = (s.abs() as f64) / n;
        let b = (s.abs() as f64) / n.sqrt();
        let verdict = if b < 20.0 { "CANCELS (sqrt-size)" } else if a < 0.01 { "cancels (o(N))" } else { "NO CANCELLATION" };
        println!("{:>8} {:>14} {:>12.2e} {:>12.1}   {}{}", r, s, a, b, verdict,
                 if factor_bad > 0 { "  [FACTORISATION FAILED]" } else { "" });
    }
    println!("\n  Square sieve needs cancellation for r prime AND r = pq. Sqrt-size sums are ideal.");
}
