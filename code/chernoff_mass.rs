fn main(){
    let lim = 100_000_000usize;
    let mut is = vec![true; lim+1];
    let mut i=2; while i*i<=lim { if is[i] { let mut j=i*i; while j<=lim { is[j]=false; j+=i; } } i+=1; }
    let pr: Vec<f64> = (2..=lim).filter(|&x| is[x]).map(|x| x as f64).collect();
    // g(t) = -t x + sum_p ln(1 + (e^{t/p}-1)/p), convex in t. Ternary search.
    let g = |t: f64, x: f64| -> f64 {
        let mut s = -t*x;
        for &p in &pr {
            let u = t/p;
            if u > 40.0 { s += u - p.ln() + (1.0 + (p-1.0)*(-u).exp()).ln(); }
            else { s += (u.exp_m1()/p).ln_1p(); }
        }
        s
    };
    for &x in &[1.0f64, 1.5, 2.0] {
        let (mut lo, mut hi) = (1.0f64, 1e9f64);
        for _ in 0..80 {
            let m1 = lo + (hi-lo)/3.0; let m2 = hi - (hi-lo)/3.0;
            if g(m1,x) < g(m2,x) { hi = m2; } else { lo = m1; }
        }
        let t = 0.5*(lo+hi); let v = g(t,x);
        println!("density{{ sigma >= {:.1} }} <= exp({:.1}) = 10^{:.1}    (t* = {:.3e})",
                 x, v, v/std::f64::consts::LN_10, t);
    }
    println!("\n  compare: 1/Pi_59 = 10^-112.9, the barrier. Squarefree m with sigma(m) >= 2 need m >= Pi_59.");
}
