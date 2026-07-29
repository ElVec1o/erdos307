// critical_set.rs — how big is the self-similar critical set?
//
// prop:massbound says a line member M = p*P*n needs an admissible second prime
//     P+(n) < P < 2/(e - sigma(n)) + O(|c|/n),
// and that window is NONEMPTY only if
//
//     e - sigma(n)  <  2 / P+(n) ,      integer form   P+(n) * (e n - n')  <  2 n .   (*)
//
// Call S_e the set of squarefree n satisfying (*). It is exactly the condition the
// cofactor m itself satisfies one level up: the constraint is SELF-SIMILAR, so the whole
// line count is governed by |S_e ∩ [1,Y]|.
//
// THE DECISIVE QUESTION for the density face of the wall: is |S_e ∩ [1,Y]| << Y^(1/2+o(1))?
// If yes, the minus-layer square-root bound follows along this route. This program measures
// the growth exponent directly.
//
// Build: rustc -O -o critical_set critical_set.rs
// Run:   ./critical_set [LIMIT]     (default 100_000_000)

fn threshold() {
    // Where does S_2 turn on? Need sigma(n) > 2 - 2/P+(n), and sigma(n) <= sum_{q<=P+(n)} 1/q,
    // so the least admissible largest prime is the least p with sum_{q<=p} 1/q > 2 - 2/p.
    let n = 5000usize;
    let mut is = vec![true; n + 1]; is[0] = false; is[1] = false;
    let mut i = 2; while i * i <= n { if is[i] { let mut j = i * i; while j <= n { is[j] = false; j += i; } } i += 1; }
    let pr: Vec<usize> = (2..=n).filter(|&x| is[x]).collect();
    let (mut s, mut lp) = (0f64, 0f64);
    for k in 0..pr.len() {
        s += 1.0 / pr[k] as f64; lp += (pr[k] as f64).ln();
        if s > 2.0 - 2.0 / pr[k] as f64 {
            let l10 = lp / std::f64::consts::LN_10;
            println!("THRESHOLD: least p with sum_{{q<=p}}1/q > 2 - 2/p is p = {} (the {}-th prime)", pr[k], k + 1);
            println!("  so n in S_2 has omega(n) >= {}, P+(n) >= {}, n >= primorial = 10^{:.2}", k + 1, pr[k], l10);
            let logm = l10 + (pr[k+1] as f64).log10() + (pr[k+2] as f64).log10();
            let mut l59 = 0f64; for j in 0..59 { l59 += (pr[j] as f64).ln(); }
            println!("  => minus-layer hit M = p*P*n > 10^{:.2}   (standard barrier Pi_59 = 10^{:.2})",
                     logm, l59 / std::f64::consts::LN_10);
            return;
        }
    }
}

fn main() {
    threshold();
    let lim: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(100_000_000);

    // linear sieve carrying: largest prime factor, derivative, squarefree flag
    let mut big: Vec<u32> = vec![0; lim + 1];      // largest prime factor
    let mut der: Vec<u64> = vec![0; lim + 1];      // arithmetic derivative (squarefree only)
    let mut sfree: Vec<bool> = vec![true; lim + 1];
    let mut spf: Vec<u32> = vec![0; lim + 1];
    for i in 2..=lim {
        if spf[i] == 0 {
            let mut j = i;
            while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; }
        }
    }
    der[1] = 0; big[1] = 0;
    for n in 2..=lim {
        let p = spf[n] as usize;
        let m = n / p;
        if m % p == 0 { sfree[n] = false; continue; }
        if !sfree[m] { sfree[n] = false; continue; }
        // n = p*m squarefree, gcd(p,m)=1: n' = p*m' + m
        der[n] = der[m] * p as u64 + m as u64;
        big[n] = if big[m] > p as u32 { big[m] } else { p as u32 };
    }

    println!("{:>4} {:>12} {:>14} {:>14} {:>10} {:>10}",
             "e", "Y", "|S_e ∩ [1,Y]|", "sqrt(Y)", "exponent", "vs 1/2");
    for &e in &[2u64, 3] {
        let mut cnt: u64 = 0;
        let mut marks: Vec<(usize, u64)> = Vec::new();
        let mut next_mark = 100_000usize;
        for n in 2..=lim {
            if !sfree[n] { continue; }
            let en = e * n as u64;
            let d = der[n];
            if d >= en { continue; }                      // sigma(n) >= e : outside
            // (*)  P+(n) * (e n - n') < 2 n
            if (big[n] as u128) * ((en - d) as u128) < 2u128 * n as u128 { cnt += 1; }
            if n == next_mark {
                marks.push((n, cnt));
                next_mark = if next_mark >= lim { lim + 1 } else { (next_mark * 10).min(lim) };
            }
        }
        marks.push((lim, cnt));
        for (y, c) in &marks {
            let expo = if *c > 1 { (*c as f64).ln() / (*y as f64).ln() } else { 0.0 };
            println!("{:>4} {:>12} {:>14} {:>14.0} {:>10.4} {:>10}",
                     e, y, c, (*y as f64).sqrt(), expo,
                     if expo < 0.5 { "BELOW" } else { "above" });
        }
    }
}
