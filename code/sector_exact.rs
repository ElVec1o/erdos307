// sector_exact.rs — sector barriers that USE b = a', not just the mass split.
//
// prop:sectorbarrier bounded N split by split from the masses alone. But a cycle also forces
// b = a' EXACTLY, i.e. b = a*sigma(a). That is a strong extra constraint and it changes the
// bounds by orders of magnitude:
//
//   * sigma(b) = 1/sigma(a)  (cross-match), so b needs k primes, k = least count of primes
//     DISJOINT from P whose reciprocals reach 1/sigma(a); hence b >= Pi_k (that product).
//   * but b = a*sigma(a), so  a >= Pi_k / sigma(a),  and  N = a*b = a^2 sigma(a).
//
// So N >= max(Pi_j, Pi_k/sigma(a))^2 * sigma(a), where j = |P|. The naive split bound missed
// the square: it allowed b to be large without forcing a to grow with it.
//
// For each |P| = j we take a = 2 * (j-1 smallest odd primes) EXCEPT that one prime of a may be
// arbitrarily large -- that is the configuration minimising N, since sigma(a) is then set by the
// small primes while a itself can grow to meet the constraint.
//
// Build: rustc -O -o sector_exact sector_exact.rs

fn primes_upto(n: usize) -> Vec<f64> {
    let mut is = vec![true; n + 1]; is[0] = false; is[1] = false;
    let mut i = 2; while i * i <= n { if is[i] { let mut j = i * i; while j <= n { is[j] = false; j += i; } } i += 1; }
    (2..=n).filter(|&x| is[x]).map(|x| x as f64).collect()
}

fn main() {
    let pr = primes_upto(400_000);
    let odd: Vec<f64> = pr.iter().cloned().filter(|&p| p > 2.0).collect();
    let l10 = std::f64::consts::LN_10;

    println!("sector bounds USING b = a' (b = a*sigma(a)), not the mass split alone\n");
    println!("{:>4} {:>10} {:>10} {:>7} {:>13} {:>15} {:>15}",
             "|P|", "sigma(a)", "sigma(b)", "|Q|>=", "log10 Pi_k", "log10 a >=", "log10 N >=");

    let mut best = (f64::MAX, 0usize);
    for j in 2..=14usize {
        // a = 2 * (j-2 smallest odd primes) * (one free large prime), so sigma(a) is set by the
        // small part; the free prime lets a grow without changing sigma(a) much.
        let small_odd = j.saturating_sub(2);
        let mut sa = 0.5; let mut log_small = (2f64).ln();
        for i in 0..small_odd { sa += 1.0 / odd[i]; log_small += odd[i].ln(); }
        let sb = 1.0 / sa;
        // b's primes: disjoint from a's, so drawn from odd primes after the small ones used
        let mut acc = 0f64; let mut logpi = 0f64; let mut k = 0usize; let mut ok = false;
        for i in small_odd..odd.len() {
            acc += 1.0 / odd[i]; logpi += odd[i].ln(); k += 1;
            if acc >= sb { ok = true; break; }
        }
        if !ok { println!("{:>4} {:>10.4} {:>10.4}   (unreachable with available odd primes)", j, sa, sb); continue; }
        // a >= max(small part, Pi_k / sigma(a))    [b = a sigma(a) >= Pi_k]
        let log_a = log_small.max(logpi - sa.ln());
        let log_n = 2.0 * log_a + sa.ln();
        println!("{:>4} {:>10.4} {:>10.4} {:>7} {:>13.1} {:>15.1} {:>15.1}",
                 j, sa, sb, k, logpi / l10, log_a / l10, log_n / l10);
        if log_n / l10 < best.0 { best = (log_n / l10, j); }
    }
    println!("\ncheapest sector: |P| = {} at log10 N >= {:.1}", best.1, best.0);
    println!("naive split bound (prop:sectorbarrier, masses only): log10 N >= 112.9");
    println!("\n=> imposing b = a' squares the cost: the bound is quadratic in Pi_k, because b large");
    println!("   forces a = b/sigma(a) large too. Every sector is far dearer than the mass split alone");
    println!("   suggests, and the |P|=3 sector of the composite mechanism is no exception.");
}
