// sqsieve_bilinear.rs -- the estimate that skips the multiplicative decomposition.
//
// prop:routeclosed showed the Gauss expansion destroys the cancellation. This route avoids it.
// Since sigma_r is ADDITIVE, writing m = de gives
//     ((m'-2m)/r) = (d/r)(e/r) * K(sigma_r(d), sigma_r(e)),   K(u,v) = ((u+v-2)/r),
// a genuine BILINEAR form. K is Toeplitz in u+v, so diagonalising by additive characters gives
// singular values |f-hat(xi)| * r = (1/sqrt r) * r = sqrt(r) -- the operator norm is a Gauss sum,
// ||K|| = sqrt(r), with NO multiplicative structure used. Cauchy-Schwarz then gives
//     |T_r| <= sqrt(r) * ||A||_2 * ||B||_2,   A(u) = sum_{d~D, sigma_r(d)=u} (d/r).
//
// Everything now rests on ||A||_2, and the crude bound |A(u)| <= n_u reduces the whole question to
// an UNSIGNED pair count,
//     P(D,r) := #{(d,d') ~ D : sigma_r(d) = sigma_r(d') mod r}   ?<<   D^2/r + D.
// Unsigned counts are far friendlier than signed cancellation. This measures whether that shape
// holds. If it does, |T_r| << (sqrt(rN) + N/sqrt r) N^o(1), i.e. A = 1/2 in hyp:sq, which by
// thm:condpower yields an UNCONDITIONAL N^{3/4+o(1)} -- a power saving over N/(log N)^{1/4}.
fn pw(mut b: i64, mut e: i64, p: i64) -> i64 { let mut r=1i64; b%=p; while e>0 { if e&1==1 {r=r*b%p;} b=b*b%p; e>>=1; } r }
fn main() {
    let lim: usize = 20_000_000;
    let mut spf = vec![0u32; lim+1];
    let mut i=2usize; while i<=lim { if spf[i]==0 { let mut j=i; while j<=lim { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } i+=1; }
    let mut sf = vec![false; lim+1]; sf[1]=true;
    for n in 2..=lim { let p=spf[n] as usize; let q=n/p; if q%p==0||!sf[q] {continue;} sf[n]=true; }
    println!("{:>10} {:>10} {:>16} {:>16} {:>14}", "r", "D", "pair count P", "D^2/r + D", "ratio");
    for &r in &[1009i64, 10007, 100003] {
        let mut sig = vec![0u32; lim+1];
        for p in 2..=lim { if spf[p] as usize==p && (p as i64)%r!=0 {
            let iv = pw((p as i64)%r, r-2, r) as u32;
            let mut j=p; while j<=lim { sig[j]=((sig[j] as i64 + iv as i64)%r) as u32; j+=p; } } }
        for &d in &[1_000_000usize, 5_000_000, 20_000_000] {
            // n_u = #{ m <= d squarefree, (m,r)=1 : sigma_r(m) = u }; pair count = sum n_u^2
            let mut nu = vec![0u64; r as usize];
            for m in 2..=d { if sf[m] && (m as i64)%r!=0 { nu[sig[m] as usize] += 1; } }
            let pairs: u128 = nu.iter().map(|&x| (x as u128)*(x as u128)).sum();
            let df = d as f64; let pred = df*df/(r as f64) + df;
            println!("{:>10} {:>10} {:>16} {:>16.0} {:>14.4}", r, d, pairs, pred, pairs as f64/pred);
        }
    }
    println!("\n  ratio ~1 => sigma_r equidistributes in the second moment, the chain closes,");
    println!("  and |T_r| << (sqrt(rN) + N/sqrt r) N^o(1) gives A = 1/2 and an UNCONDITIONAL N^{{3/4}}.");
}
