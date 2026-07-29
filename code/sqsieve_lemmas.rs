// sqsieve_lemmas.rs — the three ingredients of the square-sieve proof of A9.
//
// L2 is the heart. T(r) = sum_m ((m'-2m)/r) is expanded by Gauss sums into multiplicative sums
//     h_t(m) = (m/r) * e_r(t * sigma_r(m)),   sigma_r(m) = sum_{p|m} p^{-1} mod r,
// which is multiplicative on squarefree m because sigma_r is additive over distinct primes.
// Halasz gives o(N) unless h_t pretends to be a Dirichlet character; h_t(p) depends only on
// p mod r, and u -> e_r(t/u) is NOT multiplicative for t != 0, so no character is approached.
// Tested here: (a) the factorisation identity EXHAUSTIVELY, (b) the size of sum_m h_t(m),
// (c) the local density #{m : p^2 | (m'-2m)} against N/p^2.
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
fn pw(mut b: i64, mut e: i64, p: i64) -> i64 { let mut r = 1i64; b %= p; while e > 0 { if e & 1 == 1 { r = r*b % p; } b = b*b % p; e >>= 1; } r }
fn main() {
    let lim: usize = 30_000_000;
    let mut spf = vec![0u32; lim+1];
    for i in 2..=lim { if spf[i]==0 { let mut j=i; while j<=lim { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } }
    let mut der = vec![0i64; lim+1]; let mut sf = vec![false; lim+1]; sf[1]=true;
    for n in 2..=lim { let p=spf[n] as usize; let q=n/p; if q%p==0 || !sf[q] { continue; } sf[n]=true;
        der[n] = if q>1 { der[q]*p as i64 + q as i64 } else { 1 }; }
    let nf = lim as f64;

    // ---- (a) factorisation identity, EXHAUSTIVE over all squarefree m ----
    println!("(a) identity ((m'-2m)/r) = (m/r)*((sigma_r(m)-2)/r), exhaustive over m <= 3e7:");
    for &r in &[101i64, 1009, 10007] {
        let mut bad = 0u64; let mut chk = 0u64;
        // sigma_r via a sieve: additive over distinct primes
        let mut sig = vec![0i64; lim+1];
        for i in 2..=lim { if spf[i] as usize == i { let iv = pw((i as i64) % r, r-2, r); if (i as i64) % r != 0 {
            let mut j=i; while j<=lim { sig[j] = (sig[j] + iv) % r; j+=i; } } } }
        for m in 2..=lim {
            if !sf[m] { continue; }
            let mm = m as i64; if mm % r == 0 { continue; }
            // skip m with a prime factor = r (sigma_r undefined there)
            let mut t = m; let mut has = false;
            while t > 1 { let p = spf[t] as i64; if p % r == 0 { has = true; } while t % (p as usize) == 0 { t /= p as usize; } }
            if has { continue; }
            chk += 1;
            let lhs = jacobi(der[m] - 2*mm, r);
            let rhs = jacobi(mm, r) * jacobi(((sig[m] - 2) % r + r) % r, r);
            if lhs != rhs { bad += 1; }
        }
        println!("    r = {:<7} checked {:>9}   violations {}", r, chk, bad);
    }

    // ---- (b) size of the multiplicative sums sum_m h_t(m) ----
    println!("\n(b) |sum_m h_t(m)| / N   (Halasz predicts o(N); t=0 is the plain character):");
    let r = 1009i64;
    let mut sig = vec![0i64; lim+1];
    for i in 2..=lim { if spf[i] as usize == i && (i as i64) % r != 0 { let iv = pw((i as i64)%r, r-2, r);
        let mut j=i; while j<=lim { sig[j] = (sig[j] + iv) % r; j+=i; } } }
    for &t in &[0i64, 1, 2, 17, 500] {
        let (mut re, mut im) = (0f64, 0f64);
        for m in 2..=lim {
            if !sf[m] { continue; }
            let mm = m as i64; if mm % r == 0 { continue; }
            let c = jacobi(mm, r) as f64;
            let ang = 2.0*std::f64::consts::PI*((t*sig[m]) % r) as f64 / r as f64;
            re += c*ang.cos(); im += c*ang.sin();
        }
        println!("    t = {:<4} |sum| = {:>12.0}   /N = {:.2e}", t, (re*re+im*im).sqrt(), (re*re+im*im).sqrt()/nf);
    }

    // ---- (c) local density #{m : p^2 | (m'-2m)} vs N/p^2 ----
    println!("\n(c) #{{m <= N : p^2 | (m'-2m)}} against the predicted N/p^2:");
    for &p in &[5i64, 7, 11, 13, 101] {
        let p2 = p*p; let mut c = 0u64; let mut tot = 0u64;
        for m in 2..=lim { if !sf[m] { continue; } tot += 1;
            if (der[m] - 2*(m as i64)).rem_euclid(p2) == 0 { c += 1; } }
        println!("    p = {:<4} count {:>9}   ratio to (#sqfree)/p^2 = {:.3}", p, c, c as f64 / (tot as f64 / p2 as f64));
    }
}
