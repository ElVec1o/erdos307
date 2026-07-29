fn main(){
    // Sprint on property P. The slot p(m) = (c-m)/(m'-em) is an integer only when
    // (m'-em) | (c-m). QUESTION: does INTEGRALITY alone produce the observed thinness,
    // or is PRIMALITY of the slot doing the work?
    //   - if integrality alone is O(log Z): property P (a prime-counting bound) is NOT needed,
    //     and the dream lemma reduces to a divisibility count.
    //   - if integrality is large: property P is unavoidable.
    let lim: usize = 20_000_000;
    let mut spf = vec![0u32; lim+1];
    for i in 2..=lim { if spf[i]==0 { let mut j=i; while j<=lim { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } }
    let mut der = vec![0i64; lim+1]; let mut sf = vec![false; lim+1]; sf[1]=true;
    let mut big = vec![0u32; lim+1];
    for n in 2..=lim {
        let p=spf[n] as usize; let m=n/p;
        if m%p==0 || !sf[m] { continue; }
        sf[n]=true;
        der[n] = if m>1 { der[m]*p as i64 + m as i64 } else { 1 };
        big[n] = if m>1 && big[m]>p as u32 { big[m] } else { p as u32 };
    }
    fn isp(n:i64)->bool{ if n<2 {return false;} if n%2==0 {return n==2;} let mut i=3i64; while i*i<=n { if n%i==0 {return false;} i+=2;} true }
    println!("{:<16} {:>12} {:>12} {:>12}  {}", "line (e,c)", "integral", "int+prime", "int+p>P+(m)", "= actual members");
    for &(e,c) in &[(1i64,-1i64),(1,1),(2,-1),(2,1),(2,-4)] {
        let (mut integ, mut ip, mut full) = (0u64,0u64,0u64);
        for m in 2..=lim {
            if !sf[m] { continue; }
            let den = der[m] - e*(m as i64);
            if den == 0 { continue; }
            let num = c - (m as i64);
            if num % den != 0 { continue; }
            let p = num/den;
            if p <= 1 { continue; }
            integ += 1;
            if isp(p) { ip += 1; if p > big[m] as i64 { full += 1; } }
        }
        println!("({:>2},{:>3})        {:>12} {:>12} {:>12}", e, c, integ, ip, full);
    }
    println!("\n  log Z = {:.1};  Z^(1/2) = {:.0}", (lim as f64).ln(), (lim as f64).sqrt());
}
