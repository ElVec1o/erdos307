// minimise_structured.rs — completing the minimisation beyond subset enumeration (prefix-sum version).
//
// full_minimisation.rs enumerated all subsets of the first n primes and the minimum kept falling as
// n grew (195.9 / 188.9 / 181.7 at n = 14/16/18), so the optimum lies past reach of 2^n. Its SHAPE
// was clear: S is odd primes (2 handed to Q, since 1/2 is half of Q's mass budget) minus a couple of
// small exclusions. Search that structure directly, with prefix sums so each candidate is O(log).
//
// Bound (rem:sectorsquared): a >= max(Pi_S, Pi_min(S)/sigma(S)),  N >= a^2 sigma(S),
// Pi_min(S) = least product of primes OUTSIDE S with reciprocal sum >= 1/sigma(S).
//
// Build: rustc -O -o minimise_structured minimise_structured.rs

fn primes_upto(n: usize) -> Vec<u64> {
    let mut is = vec![true; n + 1]; is[0] = false; is[1] = false;
    let mut i = 2; while i * i <= n { if is[i] { let mut j = i * i; while j <= n { is[j] = false; j += i; } } i += 1; }
    (2..=n).filter(|&x| is[x]).map(|x| x as u64).collect()
}

fn main() {
    let pr = primes_upto(5_000_000);
    let n = pr.len();
    let l10 = std::f64::consts::LN_10;
    // prefix sums over ALL primes
    let mut ps = vec![0f64; n + 1];      // sum 1/p
    let mut pl = vec![0f64; n + 1];      // sum ln p
    for i in 0..n { ps[i + 1] = ps[i] + 1.0 / pr[i] as f64; pl[i + 1] = pl[i] + (pr[i] as f64).ln(); }

    let small_idx: Vec<usize> = (0..n).filter(|&i| pr[i] < 100).collect();

    // evaluate: S = odd primes with index in [1, xi] minus exclusions (indices in excl)
    let eval = |xi: usize, excl: &[usize]| -> Option<(f64, f64, usize)> {
        let mut sig = ps[xi + 1] - ps[1];                 // primes p_1..p_xi (skip index 0 = prime 2)
        let mut logs = pl[xi + 1] - pl[1];
        for &e in excl { if e >= 1 && e <= xi { sig -= 1.0 / pr[e] as f64; logs -= (pr[e] as f64).ln(); } else { return None; } }
        if sig <= 0.0 { return None; }
        let target = 1.0 / sig;
        // Q greedy: 2 first, then excluded primes ascending, then primes after xi
        let mut acc = 1.0 / 2.0; let mut lg = (2f64).ln(); let mut k = 1usize;
        let mut ex = excl.to_vec(); ex.sort();
        for &e in &ex {
            if acc >= target { break; }
            acc += 1.0 / pr[e] as f64; lg += (pr[e] as f64).ln(); k += 1;
        }
        if acc < target {
            // need primes after index xi: least m with ps[m] - ps[xi+1] >= target - acc
            let need = target - acc;
            let base = ps[xi + 1];
            let mut lo = xi + 1; let mut hi = n;
            if ps[n] - base < need { return None; }
            while lo < hi { let mid = (lo + hi) / 2; if ps[mid] - base >= need { hi = mid; } else { lo = mid + 1; } }
            lg += pl[lo] - pl[xi + 1]; k += lo - (xi + 1); acc += ps[lo] - base;
        }
        let log_a = logs.max(lg - sig.ln());
        Some(((2.0 * log_a + sig.ln()) / l10, sig, k))
    };

    let mut best = (f64::MAX, 0usize, Vec::new(), 0f64, 0usize);
    for xi in 1..n {
        if pr[xi] > 200_000 { break; }
        // no exclusion
        if let Some((v, s, k)) = eval(xi, &[]) { if v < best.0 { best = (v, xi, vec![], s, k); } }
        // one exclusion
        for &e in &small_idx { if e >= 1 && e <= xi {
            if let Some((v, s, k)) = eval(xi, &[e]) { if v < best.0 { best = (v, xi, vec![pr[e]], s, k); } } } }
        // two exclusions
        for ii in 0..small_idx.len() { for jj in (ii + 1)..small_idx.len() {
            let (e1, e2) = (small_idx[ii], small_idx[jj]);
            if e1 >= 1 && e2 <= xi {
                if let Some((v, s, k)) = eval(xi, &[e1, e2]) { if v < best.0 { best = (v, xi, vec![pr[e1], pr[e2]], s, k); } } } } }
    }
    let (v, xi, ex, sig, k) = best;
    println!("STRUCTURED MINIMISATION (S = odd primes <= X, minus <=2 exclusions)\n");
    println!("minimum  log10 N >= {:.1}", v);
    println!("  X = {}   exclusions = {:?}   sigma(S) = {:.5}   |Q| >= {}", pr[xi], ex, sig, k);
    println!("\n  known barrier thm:barrier : log10 N >= 112.9");
    println!("  -> {}", if v > 112.9 { "IMPROVES the known barrier" } else { "does NOT improve" });

    // control: S = ALL primes <= X (2 in S)
    let mut b2 = f64::MAX; let mut x2 = 0usize;
    for xi in 0..n {
        if pr[xi] > 200_000 { break; }
        let mut sig = ps[xi + 1]; let logs = pl[xi + 1];
        if sig <= 0.0 { continue; }
        let target = 1.0 / sig;
        let base = ps[xi + 1];
        if ps[n] - base < target { continue; }
        let mut lo = xi + 1; let mut hi = n;
        while lo < hi { let mid = (lo + hi) / 2; if ps[mid] - base >= target { hi = mid; } else { lo = mid + 1; } }
        let lg = pl[lo] - pl[xi + 1];
        let log_a = logs.max(lg - sig.ln());
        let v = (2.0 * log_a + sig.ln()) / l10;
        if v < b2 { b2 = v; x2 = xi; }
        sig = sig;
    }
    println!("\ncontrol, S = ALL primes <= X (2 in S): min log10 N >= {:.1} at X = {}", b2, pr[x2]);
}
