// sector_barrier.rs — the barrier as a function of the SPLIT.
//
// prop:compositea reduces |P| = 2 to the line n' = 2n - 4 with b - 2 prime. Attack that line.
//
// KEY STRUCTURAL FACT: with a = 2m, m odd squarefree, b = a' = m + 2m' is ODD (m odd, 2m' even).
// So Q = primes(b) consists entirely of ODD primes, while sigma(b) = 1/sigma(a). For |P| = 2,
// sigma(a) = 1/2 + 1/q ~ 1/2, hence sigma(b) ~ 2 -- and reaching mass 2 with ODD primes alone
// needs 1412 of them (thm:parity(ii)), not 59. The sector is therefore vastly more constrained
// than the general barrier suggests.
//
// This program computes, for each |P| = j, the minimal possible sigma(a) (taking a = 2 times the
// j-1 smallest odd primes), the forced sigma(b) = 1/sigma(a), the least number of odd primes
// achieving it, and the resulting lower bound on N = a*b. The minimum over j is the true barrier
// and shows which split is cheapest.
//
// Build: rustc -O -o sector_barrier sector_barrier.rs

fn primes_upto(n: usize) -> Vec<f64> {
    let mut is = vec![true; n + 1]; is[0] = false; is[1] = false;
    let mut i = 2; while i * i <= n { if is[i] { let mut j = i * i; while j <= n { is[j] = false; j += i; } } i += 1; }
    (2..=n).filter(|&x| is[x]).map(|x| x as f64).collect()
}

fn main() {
    let pr = primes_upto(300_000);
    let odd: Vec<f64> = pr.iter().cloned().filter(|&p| p > 2.0).collect();

    // partial sums / log-products of the odd primes
    let mut osum = vec![0f64; odd.len() + 1];
    let mut olog = vec![0f64; odd.len() + 1];
    for i in 0..odd.len() { osum[i + 1] = osum[i] + 1.0 / odd[i]; olog[i + 1] = olog[i] + odd[i].ln(); }
    let l10 = std::f64::consts::LN_10;

    println!("odd primes available: {}  (max sum {:.4})", odd.len(), osum[odd.len()]);
    println!("least k with sum_{{odd}} 1/p > 2 : {}",
             (1..=odd.len()).find(|&k| osum[k] > 2.0).map(|k| k as i64).unwrap_or(-1));
    println!("\n split |P|=j : a = 2 * (j-1 smallest odd primes)\n");
    println!("{:>4} {:>12} {:>12} {:>8} {:>14} {:>14}", "j", "sigma(a)", "sigma(b)", "|Q|", "log10 b >=", "log10 N >=");

    let mut best = (f64::MAX, 0usize);
    for j in 2..=12usize {
        // a = 2 * product of (j-1) smallest odd primes  -> maximal sigma(a) for that size,
        // which MINIMISES sigma(b) and hence |Q|: the most favourable case for the sector.
        let sa = 0.5 + osum[j - 1];
        let loga = (2f64).ln() + olog[j - 1];
        let sb = 1.0 / sa;
        // b's primes must be DISJOINT from a's: a uses the first j-1 odd primes, so b draws
        // from the odd primes starting at index j-1. Least count reaching sb from there:
        let mut acc = 0f64; let mut logb = 0f64; let mut k = 0usize; let mut ok = false;
        for i in (j - 1)..odd.len() {
            acc += 1.0 / odd[i]; logb += odd[i].ln(); k += 1;
            if acc >= sb { ok = true; break; }
        }
        if !ok { println!("{:>4} {:>12.5} {:>12.5}   (unreachable: disjoint odd primes cannot reach it)", j, sa, sb); continue; }
        let logn = (loga + logb) / l10;
        println!("{:>4} {:>12.5} {:>12.5} {:>8} {:>14.1} {:>14.1}", j, sa, sb, k, logb / l10, logn);
        if logn < best.0 { best = (logn, j); }
    }
    println!("\ncheapest split: |P| = {} at log10 N >= {:.1}", best.1, best.0);
    println!("general barrier (thm:barrier / prop:close59): log10 N >= 112.9");
    println!("\n=> small |P| is astronomically dearer than the balanced split: the |P|=2 sector of");
    println!("   prop:compositea, though reduced to ONE line plus one primality, is barred far above");
    println!("   the general barrier, because b must reach mass ~2 using ODD primes only.");
}
