fn main(){
    // HOLE HUNT on the Heath-Brown route, per Rule 16. Two suspects:
    // (a) (a_m/r) = (sign/r)(k_m/r) requires gcd(s_m, r) = 1, where a_m = +-s^2 k_m. If p | s_m but
    //     p does not divide k_m then (a_m/r) = 0 while (k_m/r) != 0: the identity FAILS for that m.
    //     How many m are affected, i.e. how often is a_m NOT squarefree?
    // (b) Heath-Brown needs ODD squarefree n. Our k_m can be even. How often?
    let lim = 5_000_000usize; let cap = 20_000_000usize;
    let mut spf = vec![0u32; cap+1];
    let mut i=2usize; while i<=cap { if spf[i]==0 { let mut j=i; while j<=cap { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } i+=1; }
    let mut der = vec![0i64; lim+1]; let mut sf = vec![false; lim+1]; sf[1]=true;
    for n in 2..=lim { let p=spf[n] as usize; let q=n/p; if q%p==0||!sf[q] {continue;} sf[n]=true;
        der[n]= if q>1 {der[q]*p as i64+q as i64} else {1}; }
    let (mut tot, mut nonsq, mut evenk, mut big_s) = (0u64,0u64,0u64,0u64);
    for m in 2..=lim { if !sf[m] {continue;} let a = der[m]-2*(m as i64);
        let mut aa = a.unsigned_abs() as usize; if aa==0||aa>cap {continue;} tot+=1;
        let (mut k, mut s) = (1u64, 1u64);
        while aa>1 { let p=spf[aa] as usize; let mut e=0; while aa%p==0 {aa/=p; e+=1;}
            if e%2==1 { k*=p as u64; } for _ in 0..(e/2) { s*=p as u64; } }
        if s>1 { nonsq+=1; }
        if s>1000 { big_s+=1; }
        if k%2==0 { evenk+=1; }
    }
    println!("squarefree m <= {} with 0 < |a_m| <= {}: {}", lim, cap, tot);
    println!("(a) a_m NOT squarefree (s_m > 1) : {}  ({:.2}%)   s_m > 1000 : {} ({:.4}%)",
             nonsq, 100.0*nonsq as f64/tot as f64, big_s, 100.0*big_s as f64/tot as f64);
    println!("    -> the identity (a/r)=(sign/r)(k/r) needs gcd(s,r)=1; for r = pq with p,q ~ N^{{1/2}}");
    println!("       and s_m mostly small, p | s_m is rare, but it must be handled by Mobius over d | r.");
    println!("(b) kernel k_m EVEN : {}  ({:.2}%)", evenk, 100.0*evenk as f64/tot as f64);
    println!("    -> Heath-Brown needs odd squarefree; the factor (2/r) depends on r mod 8, so the");
    println!("       moduli must be split into classes mod 8. Standard, but it must be written.");
}
