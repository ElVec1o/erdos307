// calibrate_f1.rs -- compute the heuristic constant f(1) that prop:nearmiss calls unmeasurable.
//
// A two-cycle is exactly r(a) = sigma(a)sigma(a') = 1, and the expected-count heuristic is
//      E(#{a <= X : a'' = a}) ~ f(1) * delta * log X,
// where f is the limiting density of r and delta = 0.3721 is the density of the admissible class.
// prop:nearmiss shows f(1) cannot be SAMPLED, because the region r >= 1 lies above 10^112.9. It can
// still be COMPUTED from a model, and prop:anticorr already validated the model that is needed:
// given a, the derivative a' behaves like a random integer coprime to a (measured/predicted ratio
// 0.65, 0.82, 0.91, 0.92, 0.95, 1.01 at sigma(a) >= 0, 0.5, 0.9, 1.0, 1.2, 1.3, so the model is
// good exactly in the regime a solution inhabits).
//
// The model. For a random squarefree a, P(p | a) = 1/(p+1). Given a, a' is coprime to a and
// P(q | a') = 1/q for q not dividing a. So each prime p independently lands in one of three states:
//
//      p | a        with probability  1/(p+1)
//      p | a'       with probability  (p/(p+1)) * (1/p) = 1/(p+1)
//      neither      with probability  1 - 2/(p+1)
//
// The two masses are then sigma(a) = sum over {p -> a} of 1/p and sigma(a') = sum over {p -> a'} of
// 1/p, built from DISJOINT sets by independent choices. So the joint law of (sigma(a), sigma(a')) is
// an exact 2-D convolution of per-prime three-point laws: no sampling, and no independence
// assumption between the two coordinates beyond the model itself. This is what makes the tail
// r ~ 1 reachable, where Monte Carlo is hopeless (it needs ~60 primes >= 7 to divide a at once).
//
// Then, with h the grid step,
//      f_r(1) = integral over x of f_{X,Y}(x, 1/x) * (1/x) dx.
//
// Rule 8: single-threaded, one buffer, bounded memory, progress and ETA. Rule 7: this is a model
// computation, so the output is HEURISTIC and is labelled as such; grid refinement is reported so
// the discretisation error is visible rather than assumed.

const SMAX: f64 = 3.0; // sigma never exceeds this in the relevant range

fn primes_upto(n: usize) -> Vec<usize> {
    let mut sieve = vec![true; n + 1];
    sieve[0] = false;
    if n >= 1 { sieve[1] = false; }
    let mut i = 2;
    while i * i <= n {
        if sieve[i] { let mut j = i * i; while j <= n { sieve[j] = false; j += i; } }
        i += 1;
    }
    (2..=n).filter(|&i| sieve[i]).collect()
}

/// Joint law of (sigma(a), sigma(a')) on a grid of `nb` bins of width `h`, primes up to `pmax`.
/// Returns the grid (row-major, index x*nb + y) holding probability MASS per cell.
fn joint(nb: usize, h: f64, pmax: usize, verbose: bool) -> Vec<f64> {
    let ps = primes_upto(pmax);
    let mut g = vec![0.0f64; nb * nb];
    g[0] = 1.0;
    let t0 = std::time::Instant::now();
    for (k, &p) in ps.iter().enumerate() {
        let q = 1.0 / (p as f64 + 1.0);      // P(p -> a) = P(p -> a') = 1/(p+1)
        let stay = 1.0 - 2.0 * q;
        let d = (1.0 / p as f64) / h;        // shift in bins, as a real number
        let d0 = d.floor() as usize;
        let frac = d - d0 as f64;            // linear interpolation between adjacent bins
        if d0 + 1 >= nb { continue; }
        // descending order so the update can be done in place
        for xi in (0..nb).rev() {
            for yi in (0..nb).rev() {
                let m = g[xi * nb + yi];
                if m == 0.0 { continue; }
                g[xi * nb + yi] = m * stay;
                // p -> a : shift x
                if xi + d0 + 1 < nb {
                    g[(xi + d0) * nb + yi] += m * q * (1.0 - frac);
                    g[(xi + d0 + 1) * nb + yi] += m * q * frac;
                }
                // p -> a' : shift y
                if yi + d0 + 1 < nb {
                    g[xi * nb + yi + d0] += m * q * (1.0 - frac);
                    g[xi * nb + yi + d0 + 1] += m * q * frac;
                }
            }
        }
        if verbose && (k % 25 == 0 || k + 1 == ps.len()) {
            let el = t0.elapsed().as_secs_f64();
            let frac_done = (k + 1) as f64 / ps.len() as f64;
            eprint!("\r  prime {}/{} (p={})  {:.1}%  ETA {:.0}s    ",
                    k + 1, ps.len(), p, 100.0 * frac_done, el / frac_done - el);
        }
    }
    if verbose { eprintln!(); }
    g
}

/// f_r(1) = integral f(x, 1/x) (1/x) dx, from the mass grid.
fn density_of_r_at_1(g: &[f64], nb: usize, h: f64) -> f64 {
    let mut acc = 0.0;
    // x runs over the bins; y = 1/x must be inside the grid
    for xi in 0..nb {
        let x = (xi as f64 + 0.5) * h;
        if x < 1.0 / SMAX { continue; }     // then 1/x is off the grid
        let y = 1.0 / x;
        let yi = (y / h) as usize;
        if yi >= nb { continue; }
        let dens = g[xi * nb + yi] / (h * h);   // mass per cell -> density
        acc += dens * (1.0 / x) * h;
    }
    acc
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let pmax: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(2000);
    println!("Calibrating f(1), the density of r = sigma(a)sigma(a') at 1.");
    println!("Model: each prime p goes to a, to a', or to neither, with probabilities");
    println!("1/(p+1), 1/(p+1), 1-2/(p+1). Validated by prop:anticorr in the relevant regime.");
    println!("Primes up to {}.\n", pmax);

    let delta = 3721148.0 / 1e7; // measured density of the admissible class, code/region_shape.rs
    println!("  grid step h      bins     f(1)          first cycle near 10^K, K =");
    println!("  ------------------------------------------------------------------");
    let mut last = 0.0;
    for &nb in &[1500usize, 2000, 3000] {
        let h = SMAX / nb as f64;
        let g = joint(nb, h, pmax, nb >= 3000);
        let f1 = density_of_r_at_1(&g, nb, h);
        let k = if f1 > 0.0 { (1.0 / (delta * f1)) / std::f64::consts::LN_10 } else { f64::INFINITY };
        println!("  {:.6}   {:>6}   {:.6e}   {:>12.1}", h, nb, f1, k);
        last = f1;
        // sanity: total mass and the mean of sigma(a')
        let tot: f64 = g.iter().sum();
        let mut mean_y = 0.0;
        for xi in 0..nb { for yi in 0..nb { mean_y += g[xi * nb + yi] * (yi as f64 + 0.5) * h; } }
        println!("      (total mass {:.6}, E[sigma(a')] = {:.4}; unconditional measured 0.2035)",
                 tot, mean_y);
    }
    println!();
    println!("f(1) ~ {:.4e}  =>  E(X) ~ f(1)*delta*log X with delta = {:.4}", last, delta);
    println!("first two-cycle expected near 10^{:.0}",
             (1.0 / (delta * last)) / std::f64::consts::LN_10);
    println!();
    println!("HEURISTIC. This is a model computation, not a measurement and not a proof.");
}
