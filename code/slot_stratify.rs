fn main(){
    // Stratification of the divisibility set at e=2 by the slot p = (m-c)/k, k = 2m-m'.
    // Claim: m lies in stratum p  <=>  p*m' = (2p-1)*m + c, i.e. m is in the generalized line
    // L(p, 2p-1, c) of prop:groupoid. And sigma(m) = 2 - (m-c)/(p m), so stratum p forces
    // sigma(m) >= 2 - 1/p (up to c/m), hence omega(m) >= omega_min(2 - 1/p) and m >= Pi(...).
    let lim: usize = 20_000_000;
    let mut spf = vec![0u32; lim+1];
    for i in 2..=lim { if spf[i]==0 { let mut j=i; while j<=lim { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } }
    let mut der = vec![0i64; lim+1]; let mut sf = vec![false; lim+1]; sf[1]=true;
    for n in 2..=lim {
        let p=spf[n] as usize; let q=n/p;
        if q%p==0 || !sf[q] { continue; }
        sf[n]=true; der[n] = if q>1 { der[q]*p as i64 + q as i64 } else { 1 };
    }
    let mut bad=0u64; let mut tot=0u64;
    let mut maxp=0i64; let mut byp=std::collections::BTreeMap::new();
    for c in -400i64..=400 {
        for m in 2..=lim {
            if !sf[m] { continue; }
            let k = 2*(m as i64) - der[m];
            if k==0 { continue; }
            let num = m as i64 - c;
            if num % k != 0 { continue; }
            let p = num/k;
            if p==0 || m as i64==c { continue; }
            tot+=1;
            // the stratification identity
            if p*der[m] != (2*p-1)*(m as i64) + c { bad+=1; }
            if p>maxp { maxp=p; }
            *byp.entry(p).or_insert(0u64)+=1;
        }
    }
    println!("e=2 divisibility members (|c|<=400, m<=2e7): {}", tot);
    println!("stratification identity  p*m' = (2p-1)m + c : violations {}", bad);
    println!("largest slot p observed: {}", maxp);
    println!("members by slot p: {:?}", byp.iter().take(8).collect::<Vec<_>>());
    println!("\n  stratum p forces sigma(m) >= 2 - 1/p; p=1 is the slope-ONE line m' = m + c.");
}
