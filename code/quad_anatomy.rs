// quad_anatomy.rs — the large deviation the minus layer needs, measured.
//
// rem:quadratic: on the minus layer m = pk + d^2, so for fixed (p,k) the cofactor runs over
// values of f(d) = d^2 + c, c = pk. The layer needs f(d) to carry mass sigma ~ 2, i.e. ~58
// prime factors concentrated on the small primes. How far out in the tail is that?
//
// STRUCTURAL POINT the sieve makes visible: l | f(d) forces d^2 = -c (mod l), so ONLY primes
// with (-c | l) = +1 can ever divide a value. Half the primes are unavailable -- but WHICH half
// depends on c, and c is at the solution's disposal, so an adversarial c can admit all the small
// primes (this is the quadratic-residue filter cor:qr in polynomial clothes, density 2^-omega).
//
// So we measure both regimes:
//   GENERIC c  -- a random-ish modulus;
//   FRIENDLY c -- chosen so every prime up to a bound is admissible (the adversarial best case).
// and compare the mass distribution of f(d) against random integers of the same size.
//
// Method: sieve over d (not over values). For each prime l <= B with a root of d^2 = -c, add 1/l
// to sigma_B(f(d)) at those residues. Mass lives on small primes, so sigma_B is the right proxy.
//
// Build: rustc -O -o quad_anatomy quad_anatomy.rs
// Run:   ./quad_anatomy [D B]     default 2_000_000 100_000

fn primes_upto(n: usize) -> Vec<u64> {
    let mut is = vec![true; n + 1]; is[0] = false; if n >= 1 { is[1] = false; }
    let mut i = 2; while i * i <= n { if is[i] { let mut j = i * i; while j <= n { is[j] = false; j += i; } } i += 1; }
    (2..=n).filter(|&x| is[x]).map(|x| x as u64).collect()
}
// solutions of x^2 = a (mod p), p odd prime, via Tonelli-Shanks (p small so brute force is fine)
fn sqrt_mod(a: u64, p: u64) -> Option<u64> {
    let a = a % p;
    if a == 0 { return Some(0); }
    for x in 1..p { if (x * x) % p == a { return Some(x); } }
    None
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let d_max: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2_000_000);
    let b: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100_000);
    let pr = primes_upto(b);

    // FRIENDLY c: want (-c | l) = +1 for every small l, i.e. -c a QR mod l.
    // Take c = -x^2 * (something)? Simplest: c such that -c is a perfect square times 1 -> c = -1
    // is not allowed (need c > 0). Search small c with the most admissible primes below 200.
    let small: Vec<u64> = pr.iter().cloned().filter(|&p| p < 200).collect();
    let mut best_c = 1u64; let mut best_cnt = 0usize;
    for c in 1..20000u64 {
        let cnt = small.iter().filter(|&&p| sqrt_mod((p - c % p) % p, p).is_some()).count();
        if cnt > best_cnt { best_cnt = cnt; best_c = c; }
    }
    println!("friendliest c < 20000 for primes < 200: c = {}  ({} of {} primes admissible)",
             best_c, best_cnt, small.len());

    for &(label, c) in &[("generic  c=1009", 1009u64), ("friendly c=best", best_c)] {
        let c = if label.starts_with("friendly") { best_c } else { c };
        let mut sigma = vec![0f64; d_max + 1];
        let mut omega = vec![0u32; d_max + 1];
        let mut admissible = 0usize;
        for &p in &pr {
            // roots of d^2 = -c mod p
            let target = ((p - (c % p)) % p) as u64;
            let r = match sqrt_mod(target, p) { Some(r) => r, None => continue };
            admissible += 1;
            let mut roots: Vec<u64> = vec![r];
            if p - r != r { roots.push(p - r); }          // dedupe r == p-r (p=2, and r=0)
            for r0 in roots {
                let mut d = r0 as usize;
                if d == 0 { d = p as usize; }
                while d <= d_max { sigma[d] += 1.0 / p as f64; omega[d] += 1; d += p as usize; }
            }
        }
        // distribution
        let mut mean = 0f64; let mut mx = 0f64; let mut mx_at = 0usize;
        let (mut n1, mut n15, mut n2) = (0u64, 0u64, 0u64);
        let mut mean_om = 0f64; let mut mx_om = 0u32;
        for d in 1..=d_max {
            mean += sigma[d]; mean_om += omega[d] as f64;
            if sigma[d] > mx { mx = sigma[d]; mx_at = d; }
            if omega[d] > mx_om { mx_om = omega[d]; }
            if sigma[d] > 1.0 { n1 += 1; }
            if sigma[d] > 1.5 { n15 += 1; }
            if sigma[d] > 2.0 { n2 += 1; }
        }
        mean /= d_max as f64; mean_om /= d_max as f64;
        println!("\n{}  (primes <= {} admissible: {} of {})", label, b, admissible, pr.len());
        println!("   mean sigma_B(f(d)) = {:.4}   max = {:.4} at d = {}", mean, mx, mx_at);
        println!("   mean omega_B       = {:.2}    max omega_B = {}", mean_om, mx_om);
        println!("   P[sigma > 1] = {:.3e}   P[sigma > 1.5] = {:.3e}   P[sigma > 2] = {:.3e}",
                 n1 as f64 / d_max as f64, n15 as f64 / d_max as f64, n2 as f64 / d_max as f64);
    }

    // control: same statistic for RANDOM integers (all primes admissible, density 1/p)
    let mut sigma = vec![0f64; d_max + 1];
    let mut omega = vec![0u32; d_max + 1];
    for &p in &pr {
        let mut n = p as usize;
        while n <= d_max { sigma[n] += 1.0 / p as f64; omega[n] += 1; n += p as usize; }
    }
    let (mut mean, mut mx, mut n1, mut n15, mut n2, mut mean_om) = (0f64, 0f64, 0u64, 0u64, 0u64, 0f64);
    for n in 1..=d_max {
        mean += sigma[n]; mean_om += omega[n] as f64;
        if sigma[n] > mx { mx = sigma[n]; }
        if sigma[n] > 1.0 { n1 += 1; } if sigma[n] > 1.5 { n15 += 1; } if sigma[n] > 2.0 { n2 += 1; }
    }
    mean /= d_max as f64; mean_om /= d_max as f64;
    println!("\nCONTROL: random integers n <= {} (every prime available)", d_max);
    println!("   mean sigma_B(n) = {:.4}   max = {:.4}   mean omega_B = {:.2}", mean, mx, mean_om);
    println!("   P[sigma > 1] = {:.3e}   P[sigma > 1.5] = {:.3e}   P[sigma > 2] = {:.3e}",
             n1 as f64 / d_max as f64, n15 as f64 / d_max as f64, n2 as f64 / d_max as f64);
}
