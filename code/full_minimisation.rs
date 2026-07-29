// full_minimisation.rs — the full minimisation of the cycle-condition bound.
//
// For a two-cycle, b = a' = a*sigma(a) EXACTLY and sigma(b) = 1/sigma(a), with P (a's primes)
// and Q (b's primes) disjoint. Writing P = S u {one free large prime} -- S the small primes of
// a, the free prime letting a grow without changing sigma(a) -- one gets
//
//     b >= Pi_min(S) := least product of primes OUTSIDE S with reciprocal sum >= 1/sigma(S),
//     a  = b/sigma(a) >= Pi_min(S)/sigma(S),
//     N  = a*b = a^2 sigma(a) >= Pi_min(S)^2 / sigma(S).
//
// rem:sectorsquared computed this along initial segments S = {2,3,5,...} only. Here we minimise
// over ALL subsets S of the small primes: omitting a small prime from S leaves it available to Q,
// which can shrink Pi_min sharply, so initial segments need not be optimal.
//
// Reported: the minimum, the optimal S, and -- as a control -- whether S = first j primes is ever
// ADMISSIBLE at all (it needs Pi_S * sigma(S) >= Pi_min(S), i.e. a's own size to cover b).
//
// Build: rustc -O -o full_minimisation full_minimisation.rs
// Run:   ./full_minimisation [NSMALL]     default 18 (subsets of the first NSMALL primes)

fn primes_upto(n: usize) -> Vec<f64> {
    let mut is = vec![true; n + 1]; is[0] = false; is[1] = false;
    let mut i = 2; while i * i <= n { if is[i] { let mut j = i * i; while j <= n { is[j] = false; j += i; } } i += 1; }
    (2..=n).filter(|&x| is[x]).map(|x| x as f64).collect()
}

fn main() {
    let nsmall: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(18);
    let pr = primes_upto(2_000_000);
    let l10 = std::f64::consts::LN_10;

    let mut best = (f64::MAX, 0usize, 0f64, 0usize);   // (log10 N, mask, sigma, |Q|)
    let mut admissible_initial = Vec::new();

    for mask in 1usize..(1 << nsmall) {
        // S = subset of the first nsmall primes
        let mut sig = 0f64; let mut log_s = 0f64;
        for i in 0..nsmall { if mask >> i & 1 == 1 { sig += 1.0 / pr[i]; log_s += pr[i].ln(); } }
        if sig <= 0.0 { continue; }
        let target = 1.0 / sig;
        // Pi_min: greedily take the smallest primes NOT in S until the mass reaches target
        let mut acc = 0f64; let mut log_min = 0f64; let mut k = 0usize; let mut ok = false;
        for (i, &p) in pr.iter().enumerate() {
            if i < nsmall && (mask >> i & 1) == 1 { continue; }        // in S: unavailable to Q
            acc += 1.0 / p; log_min += p.ln(); k += 1;
            if acc >= target { ok = true; break; }
        }
        if !ok { continue; }
        // a contains S, so a >= Pi_S; and b = a*sigma >= Pi_min gives a >= Pi_min/sigma.
        let log_a = log_s.max(log_min - sig.ln());
        let log_n = 2.0 * log_a + sig.ln();
        if log_n / l10 < best.0 { best = (log_n / l10, mask, sig, k); }
        // control: is S itself (no free prime) admissible?  needs Pi_S * sigma >= Pi_min
        if log_s + sig.ln() >= log_min {
            admissible_initial.push((mask, sig, (2.0 * log_s + sig.ln()) / l10));
        }
    }

    let (logn, mask, sig, k) = best;
    let mut set = Vec::new();
    for i in 0..nsmall { if mask >> i & 1 == 1 { set.push(pr[i] as u64); } }
    println!("FULL MINIMISATION over all subsets of the first {} primes\n", nsmall);
    println!("minimum  log10 N >= {:.1}", logn);
    println!("  attained at S = {:?}   (sigma(S) = {:.5}, |Q| >= {})", set, sig, k);
    println!("  general barrier thm:barrier: log10 N >= 112.9");
    println!("  -> {} the known barrier", if logn > 112.9 { "IMPROVES" } else { "does NOT improve" });

    println!("\ncontrol: subsets S admissible WITHOUT a free large prime (Pi_S sigma >= Pi_min): {}",
             admissible_initial.len());
    if admissible_initial.is_empty() {
        println!("  none -- so a's primes cannot all be small: every cycle needs a large prime in P");
    } else {
        let mn = admissible_initial.iter().fold(f64::MAX, |m, x| m.min(x.2));
        println!("  least log10 N among them: {:.1}", mn);
    }
}
