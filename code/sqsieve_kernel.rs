fn main(){
    // Heath-Brown's quadratic large sieve needs sum_k |b_k|^2 where b_k collects the m whose
    // a_m = m' - 2m has squarefree KERNEL k. That quantity is an unsigned pair count:
    //     sum_k |b_k|^2 <= #{(m,m') : kernel(a_m) = kernel(a_m')} = #{(m,m') : a_m a_m' = square}.
    // If this is N^{1+o(1)} the large sieve gives  sum_{r~R}|T_r|^2 << N^eps (R+N) N,
    // and with P = N^{1/2} the square sieve then yields N^{1/2+eps} -- the CRUX-A9 target.
    let lim = 10_000_000usize; let cap = 40_000_000usize;
    let mut spf = vec![0u32; cap+1];
    let mut i=2usize; while i<=cap { if spf[i]==0 { let mut j=i; while j<=cap { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } i+=1; }
    let mut der = vec![0i64; lim+1]; let mut sf = vec![false; lim+1]; sf[1]=true;
    for n in 2..=lim { let p=spf[n] as usize; let q=n/p; if q%p==0||!sf[q] {continue;} sf[n]=true;
        der[n]= if q>1 {der[q]*p as i64+q as i64} else {1}; }
    // squarefree kernel of |a|, for |a| <= cap
    let kernel = |mut a: usize| -> u64 { let mut k=1u64; while a>1 { let p=spf[a] as usize; let mut e=0;
        while a%p==0 { a/=p; e+=1; } if e%2==1 { k*= p as u64; } } k };
    let mut cnt: std::collections::HashMap<u64,u64> = std::collections::HashMap::new();
    let mut used=0u64; let mut skipped=0u64;
    for m in 2..=lim { if !sf[m] {continue;} let a = der[m]-2*(m as i64);
        let aa = a.unsigned_abs() as usize;
        if aa==0 || aa>cap { skipped+=1; continue; }
        // keep the sign as part of the key: (kernel, sign)
        let k = kernel(aa) * 2 + if a<0 {1} else {0};
        *cnt.entry(k).or_insert(0)+=1; used+=1; }
    let pairs: u128 = cnt.values().map(|&v| (v as u128)*(v as u128)).sum();
    println!("m <= {} squarefree, |a_m| <= {}: used {}  (skipped {})", lim, cap, used, skipped);
    println!("distinct (kernel,sign) values : {}", cnt.len());
    println!("sum_k |b_k|^2 (pair count)    : {}", pairs);
    println!("  ratio to N (= used)         : {:.3}", pairs as f64 / used as f64);
    let mut top: Vec<_> = cnt.iter().map(|(&k,&v)|(v,k)).collect(); top.sort_unstable_by(|a,b| b.cmp(a));
    println!("  largest multiplicity        : {}  (a value repeated that often)", top[0].0);
    println!("\n  ratio ~1 => sum_k |b_k|^2 << N^{{1+o(1)}}, the large sieve applies, N^{{1/2}} follows.");
}
