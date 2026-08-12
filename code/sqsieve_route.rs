// sqsieve_route.rs -- can hyp:sq come from GRH via the Fourier/Gauss route? Decisive test.
//
// The route: alpha(u) = (u/r) e_r(t/u) is a function on (Z/r)^*, so expand it over characters,
// alpha = sum_chi ahat(chi) chi. Then the Dirichlet series of the multiplicative h_t factors as
// prod_chi L(s,chi)^{ahat(chi)}, and GRH would give analyticity in Re s > 1/2, hence sqrt(N).
//
// The obstruction is the PRINCIPAL coefficient. ahat(chi_0) = (1/phi(r)) sum_u (u/r) e_r(t/u).
//
// CORRECTED after adversarial review (and superseded by lem:charcancel, whose repaired proof turns
// on exactly this sum). It is NOT a Salie sum and its modulus is NOT 2 sqrt(r): a Salie sum needs
// both e_q(ma) and e_q(na^-1), and here m = 0. Substituting v = u^-1 and using (u^-1|r) = (u|r)
// turns it into the GAUSS sum, so |S(t)| = sqrt(r) EXACTLY when gcd(t,r) = 1 and 0 otherwise, and
// |ahat(chi_0)| = sqrt(r)/(r-1) ~ 1/sqrt(r), half the value claimed here previously. Measured:
// r = 1009 gives |S| = 31.76476 = sqrt(1009), not 63.52952; r = 10007 gives 100.03499, not 200.07.
// The factor-2 discrepancy was visible in this program's own printed output and went unnoticed.
//
// The CONCLUSION is unaffected: the coefficient is small but NOT ZERO either way. A nonzero principal coefficient leaves a zeta-type branch point at s = 1
// contributing about N (log N)^{|ahat(chi_0)| - 1}, which is vastly larger than sqrt(N).
//
// So the route can only work if the individual multiplicative sums really are of that size, with
// the observed sqrt(N) in T_r arising from cancellation ACROSS t. This measures which it is.
fn jacobi(mut a: i64, mut n: i64) -> i64 {
    if n <= 0 || n % 2 == 0 { return 0; }
    a = ((a % n) + n) % n; let mut t = 1i64;
    while a != 0 {
        while a % 2 == 0 { a /= 2; let r = n % 8; if r == 3 || r == 5 { t = -t; } }
        std::mem::swap(&mut a, &mut n);
        if a % 4 == 3 && n % 4 == 3 { t = -t; }
        a %= n; }
    if n == 1 { t } else { 0 }
}
fn pw(mut b: i64, mut e: i64, p: i64) -> i64 { let mut r = 1i64; b %= p; while e > 0 { if e & 1 == 1 { r = r*b % p; } b = b*b % p; e >>= 1; } r }
fn main() {
    let lim: usize = 30_000_000;
    let mut spf = vec![0u32; lim+1];
    let mut i = 2usize;
    while i <= lim { if spf[i]==0 { let mut j=i; while j<=lim { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } i+=1; }
    let mut der = vec![0i64; lim+1]; let mut sf = vec![false; lim+1]; sf[1]=true;
    for n in 2..=lim { let p=spf[n] as usize; let q=n/p; if q%p==0||!sf[q] {continue;} sf[n]=true;
        der[n]= if q>1 {der[q]*p as i64+q as i64} else {1}; }
    let nf = lim as f64; let sq = nf.sqrt(); let lg = nf.ln();
    for &r in &[1009i64, 10007] {
        // Gauss sum S(t) = sum_u (u/r) e_r(t/u) = (t|r) tau(chi), and ahat(chi_0) = S(t)/(r-1)
        let mut sig = vec![0i64; lim+1];
        for p in 2..=lim { if spf[p] as usize == p && (p as i64)%r != 0 {
            let iv = pw((p as i64)%r, r-2, r); let mut j=p; while j<=lim { sig[j]=(sig[j]+iv)%r; j+=p; } } }
        println!("r = {}   sqrt(N) = {:.0}", r, sq);
        for &t in &[1i64, 2, 7] {
            // Gauss sum (mislabelled "Salie" in earlier versions; see the header)
            let (mut sre, mut sim) = (0f64, 0f64);
            for u in 1..r { let inv = pw(u, r-2, r);
                let ang = 2.0*std::f64::consts::PI*((t*inv)%r) as f64 / r as f64;
                let j = jacobi(u, r) as f64; sre += j*ang.cos(); sim += j*ang.sin(); }
            let salie = (sre*sre+sim*sim).sqrt();
            let ahat0 = salie/((r-1) as f64);
            // the multiplicative sum itself
            let (mut re, mut im) = (0f64, 0f64);
            for m in 2..=lim { if !sf[m] {continue;} let mm=m as i64; if mm%r==0 {continue;}
                let c = jacobi(mm, r) as f64;
                let ang = 2.0*std::f64::consts::PI*((t*sig[m])%r) as f64 / r as f64;
                re += c*ang.cos(); im += c*ang.sin(); }
            let s = (re*re+im*im).sqrt();
            let pred = nf * lg.powf(ahat0 - 1.0);          // zeta-pole prediction
            println!("  t={:<3} |Gauss|={:.1} (sqrt r = {:.1})  ahat0={:.4}   |sum h_t| = {:.3e}",
                     t, salie, (r as f64).sqrt(), ahat0, s);
            println!("        zeta-pole prediction N (log N)^(ahat0 - 1) = {:.3e}   ratio measured/pred = {:.4}",
                     pred, s/pred);
            println!("        |sum h_t| / sqrt(N) = {:.2}", s/sq);
        }
        println!();
    }
    println!("  If measured << prediction, the zeta-pole is NOT the obstruction and the route is open.");
    println!("  If measured ~ prediction, the individual sums are far above sqrt(N) and the observed");
    println!("  sqrt(N) in T_r comes from cancellation ACROSS t, which the decomposition destroys.");
}
