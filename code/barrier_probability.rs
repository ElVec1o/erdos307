// barrier_probability.rs -- the heuristic constant of prop:nearmiss IS the barrier.
//
// A two-cycle needs sigma(a)sigma(a') = 1, hence by AM-GM sigma(a) + sigma(a') >= 2. So the density
// f(1) of r = sigma(a)sigma(a') at 1 is supported inside the event
//
//      B :  sigma(a) + sigma(a') >= 2,
//
// and f(1) = P(B) * (conditional density of r at 1 given B), the second factor being O(1). P(B) is a
// TAIL PROBABILITY, not a density, so it is robust to the grid in a way a density is not: refining
// the grid or extending the prime range moves it by a little, not by orders of magnitude. That is
// what makes it computable where a direct estimate of f(1) is not.
//
// The model is the one prop:anticorr validated: for random squarefree a, P(p | a) = 1/(p+1), and
// given a the derivative a' behaves like a random integer coprime to a, so P(p | a') = 1/(p+1) too.
// The two are exclusive, so each prime lands in a, in a', or in neither, and
//
//      sigma(a) + sigma(a') = sum over {p in a or a'} of 1/p,   P(p in a or a') = 2/(p+1).
//
// This is a ONE-dimensional large-deviation computation: exactly the reason it converges.
//
// Reported: P(sigma(a) >= 1), which prop:anticorr's companion sieve measured at 0.0420 and which
// therefore validates the DP, and P(B), which calibrates the heuristic.

fn primes_upto(n: usize) -> Vec<usize> {
    let mut s = vec![true; n + 1];
    s[0] = false;
    if n >= 1 { s[1] = false; }
    let mut i = 2;
    while i * i <= n {
        if s[i] { let mut j = i * i; while j <= n { s[j] = false; j += i; } }
        i += 1;
    }
    (2..=n).filter(|&i| s[i]).collect()
}

/// P(sum over included p of 1/p >= target), where p is included with probability `prob(p)`.
/// Grid of `nb` bins spanning [0, smax]; mass beyond smax is accumulated in the last bin, which is
/// correct here because we only ever ask for an upper tail.
fn tail_prob(nb: usize, smax: f64, pmax: usize, target: f64, double: bool) -> f64 {
    let h = smax / nb as f64;
    let ps = primes_upto(pmax);
    let mut g = vec![0.0f64; nb];
    g[0] = 1.0;
    for &p in &ps {
        let q = if double { 2.0 / (p as f64 + 1.0) } else { 1.0 / (p as f64 + 1.0) };
        let stay = 1.0 - q;
        let d = (1.0 / p as f64) / h;
        let d0 = d.floor() as usize;
        let frac = d - d0 as f64;
        for i in (0..nb).rev() {
            let m = g[i];
            if m == 0.0 { continue; }
            g[i] = m * stay;
            let a = (i + d0).min(nb - 1);
            let b = (i + d0 + 1).min(nb - 1);
            g[a] += m * q * (1.0 - frac);
            g[b] += m * q * frac;
        }
    }
    let t0 = (target / h).ceil() as usize;
    g[t0.min(nb - 1)..].iter().sum()
}

fn main() {
    println!("The heuristic constant, computed rather than sampled.");
    println!("Model (validated by prop:anticorr): each prime lands in a, in a', or in neither,");
    println!("with P(p|a) = P(p|a') = 1/(p+1). A two-cycle forces sigma(a)+sigma(a') >= 2.\n");

    println!("VALIDATION: P(sigma(a) >= 1), against the measured density 0.0420");
    println!("   bins    pmax        P(sigma(a) >= 1)");
    for &(nb, pmax) in &[(20000usize, 10000usize), (40000, 100000), (80000, 1000000)] {
        let p = tail_prob(nb, 4.0, pmax, 1.0, false);
        println!("  {:>6}  {:>8}        {:.6}", nb, pmax, p);
    }
    println!();

    println!("THE BARRIER EVENT: P(sigma(a) + sigma(a') >= 2)");
    println!("   bins    pmax        P(B)");
    let mut last = 0.0;
    for &(nb, pmax) in &[(20000usize, 10000usize), (40000, 100000), (80000, 1000000)] {
        let p = tail_prob(nb, 4.0, pmax, 2.0, true);
        println!("  {:>6}  {:>8}        {:.6e}", nb, pmax, p);
        last = p;
    }
    println!();

    let delta = 3721148.0 / 1e7;
    println!("P(B) = {:.4e}. Since f(1) = P(B) * O(1), the expected count is", last);
    println!("   E(X) ~ f(1) * delta * log X  with delta = {:.4},", delta);
    println!("so E(X) reaches 1 near log X = 1/(delta*f(1)), i.e. X near 10^{:.3e}",
             (1.0 / (delta * last)) / std::f64::consts::LN_10);
    println!();
    println!("For contrast the proved barrier is 10^112.9, and E(10^112.9) is about {:.2e}.",
             last * delta * 112.9 * std::f64::consts::LN_10);
    println!();
    println!("HEURISTIC, and a model computation. The point is not the digits but the order:");
    println!("the constant prop:nearmiss calls unmeasurable is the barrier's own probability,");
    println!("which is why it is small, and it is small enough that the expected count stays");
    println!("far below 1 at every scale any argument or search will ever reach.");
}
