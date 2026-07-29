// no_place.rs — does ANY place of Q admit the function-field descent?
//
// prop:ffsunit/rem:ffplaces isolated the mechanism of prop:ff-pyth: a single place whose
// (discrete) valuation the derivative STRICTLY LOWERS. Over F_q[t] that is the place at
// infinity, deg D(a) <= deg a - 1. By Ostrowski the places of Q are exactly the p-adic ones
// and the archimedean one, so the question "can the function-field proof transfer?" is a
// finite classification, not a matter of ingenuity. This program exhibits the failure at both
// kinds of place.
//
//   ARCHIMEDEAN: |D(n)| = n sigma(n) > n whenever sigma(n) > 1 -- the derivative EXPANDS.
//   p-ADIC:      for p | n (n squarefree) v_p(D(n)) = 0 < 1 = v_p(n)   -- lowers;
//                but there are n with p ∤ n and p | D(n)                -- raises.
//                So no uniform contraction at any p.
//
// Build: rustc -O -o no_place no_place.rs
// Run:   ./no_place [LIMIT]      (default 2_000_000)

fn main() {
    let lim: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(2_000_000);

    let mut spf: Vec<u32> = vec![0; lim + 1];
    for i in 2..=lim {
        if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } }
    }
    let mut der: Vec<u64> = vec![0; lim + 1];
    let mut sf: Vec<bool> = vec![false; lim + 1];
    sf[1] = true;
    for n in 2..=lim {
        let p = spf[n] as usize; let m = n / p;
        if m % p == 0 || !sf[m] { sf[n] = false; continue; }
        sf[n] = true;
        der[n] = if m > 1 { der[m] * p as u64 + m as u64 } else { 1 };
    }

    // ---- archimedean: derivative expands on a positive proportion ----
    let (mut expand, mut contract, mut tot) = (0u64, 0u64, 0u64);
    let mut first_expand = 0usize;
    for n in 2..=lim {
        if !sf[n] { continue; }
        tot += 1;
        if der[n] > n as u64 { expand += 1; if first_expand == 0 { first_expand = n; } }
        else { contract += 1; }
    }
    println!("ARCHIMEDEAN place  |D(n)| vs |n|  over {} squarefree n <= {}:", tot, lim);
    println!("   expands (sigma > 1): {} ({:.2}%)   contracts: {} ({:.2}%)   first expander: n = {}",
             expand, 100.0 * expand as f64 / tot as f64, contract,
             100.0 * contract as f64 / tot as f64, first_expand);
    println!("   => no contraction, and |.| is not ultrametric in any case.\n");

    // ---- p-adic: both directions occur, so no uniform contraction ----
    println!("p-ADIC places  v_p(D(n)) vs v_p(n)  (squarefree n):");
    println!("{:>5} {:>28} {:>28}", "p", "lowers (p|n, v: 1 -> 0)", "RAISES (p∤n, v: 0 -> >=1)");
    for &p in &[2usize, 3, 5, 7, 11, 13, 101] {
        let mut low = 0u64; let mut raise = 0u64;
        let mut ex_low = 0usize; let mut ex_raise = 0usize;
        for n in 2..=lim {
            if !sf[n] { continue; }
            let vn = if n % p == 0 { 1 } else { 0 };
            let vd = if der[n] % p as u64 == 0 { 1 } else { 0 };   // >=1 suffices
            if vn == 1 && vd == 0 { low += 1; if ex_low == 0 { ex_low = n; } }
            if vn == 0 && vd >= 1 { raise += 1; if ex_raise == 0 { ex_raise = n; } }
        }
        println!("{:>5} {:>18} (e.g. {:>5}) {:>18} (e.g. {:>5})", p, low, ex_low, raise, ex_raise);
    }
    println!("\n   => at every p the derivative lowers v_p on multiples of p but RAISES it elsewhere:");
    println!("      no place of Q gives a uniform strict descent. By Ostrowski these are all the");
    println!("      places, so the mechanism of prop:ff-pyth is unavailable over Q by classification.");
}
