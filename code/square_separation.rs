fn main(){
    // toy base S: a few primes. D = prod S, N = cofactor sum, B = N - 2D, A = N + 2D.
    // Tail family S u {q}: minus-square is  d^2 = B q + D, so q = (d^2 - D)/B.
    // Claim: along d = d0 + tB (the classes with B | d^2 - D), q is a QUADRATIC in t:
    //        q(t) = (d0^2 - D)/B + 2 d0 t + B t^2.
    for s in [vec![2u64,3,5,7], vec![2,3,5,7,11], vec![3,5,7,11,13]] {
        let d_: i128 = s.iter().map(|&x| x as i128).product();
        let n_: i128 = s.iter().map(|&x| d_ / x as i128).sum();
        let b_ = n_ - 2*d_;
        if b_ == 0 { continue; }
        let bb = b_.abs();
        // find d0 with bb | d0^2 - D
        let mut found = None;
        for d0 in 1..bb.min(200000) {
            if (d0*d0 - d_) % bb == 0 { found = Some(d0); break; }
        }
        match found {
            None => println!("S={:?}: D={} N={} B={}  -> no d0 with B | d^2-D in range", s, d_, n_, b_),
            Some(d0) => {
                let c0 = (d0*d0 - d_)/bb;
                let mut ok = true;
                for t in 0..8i128 {
                    let d = d0 + t*bb;
                    let q_direct = (d*d - d_)/bb;
                    let q_poly = c0 + 2*d0*t + bb*t*t;
                    if (d*d - d_) % bb != 0 || q_direct != q_poly { ok = false; }
                }
                println!("S={:?}: D={} N={} B={}  d0={}  q(t) = {} + {}t + {}t^2   quadratic-identity: {}",
                         s, d_, n_, b_, d0, c0, 2*d0, bb, if ok {"HOLDS"} else {"FAILS"});
            }
        }
    }
}
