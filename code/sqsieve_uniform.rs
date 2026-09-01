// sqsieve_uniform.rs -- how does the square-sieve character sum scale in the modulus r?
//
// When this was written cor:a9rate reached only N loglog N (log N)^{-1/4}; it is now proved at
// N (loglog N)^{1/2+d} (log N)^{-1/4} via lem:swdirect.  rem:rateexponent identifies why the
// exponent is set by the floor N (log N)^{-1/2} in Montgomery's form of Halasz, which holds however
// large the pretentious distance grows. The measured sums are of size sqrt(N), incomparably
// stronger. What the SIEVE can deliver depends entirely on how T_r(N) grows with r, so measure it:
//
//     T_r(N) = sum_{m <= N, mu^2(m)=1, (m,r)=1} ( (m' - 2m) / r ).
//
// If |T_r| << r^A N^{1/2+o(1)}, the square sieve yields #{m <= N : m'-2m = square} << N^{1-delta}
// with delta = 1/(2(2A+1)). A = 0 gives delta = 1/2, i.e. exactly the N^{1/2+o(1)} that CRUX-A9
// asked for. So the exponent A is the whole question, and it is measurable.
fn jacobi(mut a: i64, mut n: i64) -> i64 {
    if n <= 0 || n % 2 == 0 { return 0; }
    a = ((a % n) + n) % n; let mut t = 1i64;
    while a != 0 {
        while a % 2 == 0 { a /= 2; let r = n % 8; if r == 3 || r == 5 { t = -t; } }
        std::mem::swap(&mut a, &mut n);
        if a % 4 == 3 && n % 4 == 3 { t = -t; }
        a %= n;
    }
    if n == 1 { t } else { 0 }
}
fn main() {
    let lim: usize = 40_000_000;
    let mut spf = vec![0u32; lim + 1];
    let mut i = 2usize;
    while i <= lim { if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } i += 1; }
    let mut der = vec![0i64; lim + 1]; let mut sf = vec![false; lim + 1]; sf[1] = true;
    for n in 2..=lim { let p = spf[n] as usize; let q = n / p;
        if q % p == 0 || !sf[q] { continue; }
        sf[n] = true; der[n] = if q > 1 { der[q] * p as i64 + q as i64 } else { 1 }; }
    let n = lim as f64; let sq = n.sqrt();
    println!("N = {:e}, sqrt(N) = {:.3e}\n", n, sq);
    println!("{:>12} {:>8} {:>14} {:>12} {:>14}", "r", "type", "T_r(N)", "|T|/sqrt(N)", "|T|/(sqrt(r*N))");
    let rs: Vec<(i64, &str)> = vec![
        (101, "prime"), (1009, "prime"), (10007, "prime"), (100003, "prime"),
        (1000003, "prime"), (10000019, "prime"),
        (101 * 1009, "pq"), (1009 * 10007, "pq"), (10007 * 100003, "pq"), (100003 * 1000003, "pq"),
        (3 * 5 * 7 * 11, "sqfree"), (101 * 103 * 107, "sqfree"),
    ];
    let mut maxa: f64 = -9.0;
    for (r, kind) in rs {
        let mut s = 0i64;
        for m in 2..=lim {
            if !sf[m] { continue; }
            let mm = m as i64;
            if mm % r == 0 { continue; }
            s += jacobi(der[m] - 2 * mm, r);
        }
        let a = (s.abs() as f64) / sq;
        let b = (s.abs() as f64) / (sq * (r as f64).sqrt());
        // implied exponent A from |T| = r^A sqrt(N)
        let aexp = if s != 0 { a.ln() / (r as f64).ln() } else { -9.0 };
        if aexp > maxa { maxa = aexp; }
        println!("{:>12} {:>8} {:>14} {:>12.2} {:>14.4}   (implied A = {:+.3})", r, kind, s, a, b, aexp);
    }
    println!("\n  largest implied A over these moduli: {:+.3}", maxa);
    println!("  delta = 1/(2(2A+1)) with A = 0  ->  N^(1/2), the CRUX-A9 target.");
}
