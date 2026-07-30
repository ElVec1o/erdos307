fn pw(mut b:i64, mut e:i64, m:i64)->i64{let mut r=1i64;b%=m;while e>0{if e&1==1{r=r*b%m;}b=b*b%m;e>>=1;}r}
fn main(){
    // I6 EXAMPLES BATTERY for the forcing mechanism.
    // CLAIM: for r prime, r not dividing a, and a squarefree:  r | a'  <=>  sigma_r(a) = 0 mod r,
    // where sigma_r(a) = sum_{p|a} p^{-1} mod r. This is a CHECKABLE congruence on the support of a
    // that FORCES r into the factorisation of a'. If true it converts "hope a' factors well" into
    // "impose congruences on P".
    // Battery: (1) trivial instance, (2) the motivating instance, (3) a NON-example the criterion
    // must exclude, (4) exhaustive check over a real range.
    let lim = 3_000_000usize;
    let mut spf=vec![0u32;lim+1];
    let mut i=2usize; while i<=lim { if spf[i]==0 { let mut j=i; while j<=lim { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } i+=1; }
    let mut sf=vec![false;lim+1]; sf[1]=true; let mut der=vec![0i64;lim+1];
    for n in 2..=lim { let p=spf[n] as usize; let q=n/p; if q%p==0||!sf[q] {continue;} sf[n]=true;
        der[n]= if q>1 {der[q]*p as i64+q as i64} else {1}; }
    let sig_r = |n:usize, r:i64| -> i64 { let mut t=n; let mut s=0i64;
        while t>1 { let p=spf[t] as i64; s=(s+pw(p%r,r-2,r))%r; let pu=p as usize; while t%pu==0 {t/=pu;} } s };
    let mut checked=0u64; let mut viol=0u64; let (mut yes,mut no)=(0u64,0u64);
    for &r in &[3i64,5,7,11,13,101,1009] {
        for n in 2..=lim {
            if !sf[n] {continue;}
            if (n as i64)%r==0 {continue;}
            checked+=1;
            let lhs = der[n] % r == 0;
            let rhs = sig_r(n,r) == 0;
            if lhs!=rhs { viol+=1; }
            if lhs {yes+=1;} else {no+=1;}
        }
    }
    println!("(4) exhaustive: {} pairs (n,r) checked, VIOLATIONS {}", checked, viol);
    println!("    r | a' held in {} cases, failed in {}  (so the criterion is not vacuous either way)", yes, no);
    // (1) trivial, (2) motivating, (3) non-example
    let show=|n:usize,r:i64|{ println!("    n={:<8} a'={:<12} r={:<5} sigma_r={:<5} r|a': {}", n, der[n], r, sig_r(n,r), der[n]%r==0); };
    println!("(1) trivial      :"); show(6,5);
    println!("(2) motivating   :"); show(30,31); show(210,247%1000);
    println!("(3) NON-example  :"); show(6,7);
}
