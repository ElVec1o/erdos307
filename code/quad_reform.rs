fn main(){
    let lim: usize = 3_000_000;
    let mut spf = vec![0u32; lim+1];
    for i in 2..=lim { if spf[i]==0 { let mut j=i; while j<=lim { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } }
    let mut der = vec![0i128; lim+1]; let mut sf = vec![false; lim+1]; sf[1]=true;
    let mut big = vec![0u32; lim+1];
    for n in 2..=lim {
        let p = spf[n] as usize; let m = n/p;
        if m%p==0 || !sf[m] { continue; }
        sf[n]=true;
        der[n] = if m>1 { der[m]*p as i128 + m as i128 } else { 1 };
        big[n] = if m>1 && big[m]>p as u32 { big[m] } else { p as u32 };
    }
    // identity: for squarefree M with omega>=2, p=P+(M), m=M/p, k=2m-m', then M'-2M = m - p*k
    let (mut tested, mut bad) = (0u64, 0u64);
    for mm in 6..=lim {
        if !sf[mm] { continue; }
        let p = big[mm] as i128; let m = (mm as i128)/p;
        if m < 2 { continue; }
        let k = 2*der[m as usize].max(0)*0 + 2*m - der[m as usize];
        let lhs = der[mm] - 2*(mm as i128);
        if lhs != m - p*k { bad += 1; }
        tested += 1;
    }
    println!("identity  M'-2M = m - p*k  (p=P+(M), m=M/p, k=2m-m'):");
    println!("  squarefree M<=3e6 with omega>=2: {} tested, {} violations", tested, bad);
    println!("\n=> on the minus layer M'-2M = d^2 >= 0, so  m = p*k + d^2 :");
    println!("   for FIXED (p,k) the cofactor m runs over values of the QUADRATIC d^2 + pk.");
}
