// slot_massbound.rs — the MASS-DEFECT BOUND on the second-largest prime.
//
// For a member M of the line M' = eM + c, write p = P+(M), m = M/p, P = P+(m), n = m/P.
// The determined slot is p = (c - m)/(m' - em) (prop:groupoid), and p > P holds by
// definition. Unwinding that single inequality, with sigma(m) = sigma(n) + 1/P:
//
//     P (e - sigma(m)) < 1 - c/m          [from p > P]
//     P (e - sigma(n)) < 2 - c/m          [since sigma(m) = sigma(n) + 1/P]
//
// and clearing denominators (sigma(n) = n'/n, m = Pn) gives the exact integer form
//
//     P^2 (e n - n')  <  2 P n - c .                                   (MASS-DEFECT BOUND)
//
// So the SECOND-largest prime of M is bounded by (essentially) twice the reciprocal of the
// mass defect e - sigma(n) of the remaining cofactor: a prime bounded by a mass. For lines
// with small |c| -- the near-critical slope-two lines that carry the minus layer -- this
// reads P < 2/(e - sigma(n)) + O(|c|/n), coupling prime size to mass defect directly.
//
// This program verifies the bound exhaustively (every squarefree M with omega >= 3 lies on
// its own line, c := M' - eM, so the bound must hold universally), and measures how tight
// it is -- the tightness is what decides whether it can drive a counting argument.
//
// Build: rustc -O -o slot_massbound slot_massbound.rs
// Run:   ./slot_massbound [LIMIT]        (default 10_000_000)

fn main() {
    let lim: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(10_000_000);

    // smallest-prime-factor sieve, u32 (4 bytes/entry, flat footprint)
    let mut spf: Vec<u32> = (0..=lim as u32).collect();
    let mut i = 2usize;
    while i * i <= lim {
        if spf[i] == i as u32 {
            let mut j = i * i;
            while j <= lim { if spf[j] == j as u32 { spf[j] = i as u32; } j += i; }
        }
        i += 1;
    }

    // squarefree flag + derivative + largest prime, all from the spf chain
    let sf = |mut x: usize| -> Option<(u64, u32)> {   // (derivative, largest prime)
        if x < 2 { return Some((0, 0)); }
        let mut d: u64 = 0; let mut prod: u64 = 1; let mut last = 0u32; let mut big = 0u32;
        // n' = sum n/p ; build by walking distinct primes
        let mut primes: Vec<u32> = Vec::with_capacity(10);
        while x > 1 {
            let p = spf[x];
            if p == last { return None; }             // repeated factor: not squarefree
            last = p; if p > big { big = p; }
            primes.push(p); prod *= p as u64;
            x /= p as usize;
        }
        for &p in &primes { d += prod / p as u64; }
        Some((d, big))
    };

    for &e in &[1u64, 2, 3] {
        let mut tested: u64 = 0;
        let mut skipped: u64 = 0;
        let mut viol: u64 = 0;
        let mut viol_sigma: u64 = 0;
        // tightness: how often is the bound within a factor 2 / 10 / 100 of equality
        let (mut t2, mut t10, mut t100) = (0u64, 0u64, 0u64);
        let mut worst_ratio = 0.0f64;

        for mm in 6..=lim {
            let (dm, p) = match sf(mm) { Some(v) => v, None => continue };
            if p == 0 { continue; }
            let m = mm / p as usize;                      // cofactor
            if m < 2 { continue; }
            let (dm2, bigp) = match sf(m) { Some(v) => v, None => continue };
            if bigp == 0 { continue; }
            let n = m / bigp as usize;                    // cofactor of the cofactor
            if n < 1 { continue; }
            let (dn, _) = match sf(n) { Some(v) => v, None => continue };
            if n == 1 { continue; }                       // need omega(M) >= 3
            // HYPOTHESIS of the bound: sigma(m) < e  (automatic for e=2 below Pi_59)
            if (dm2 as i128) >= e as i128 * m as i128 { skipped += 1; continue; }
            tested += 1;

            let c: i128 = dm as i128 - e as i128 * mm as i128;      // M lies on its own line
            let pp = bigp as i128;
            let lhs: i128 = pp * pp * (e as i128 * n as i128 - dn as i128);
            let rhs: i128 = 2 * pp * n as i128 - c;

            // sigma(n) < e   <=>   n' < e n
            if !((dn as i128) < e as i128 * n as i128) { viol_sigma += 1; }
            if !(lhs < rhs) { viol += 1; }

            if lhs > 0 {
                let r = rhs as f64 / lhs as f64;
                if r < 2.0 { t2 += 1; }
                if r < 10.0 { t10 += 1; }
                if r < 100.0 { t100 += 1; }
                if r > worst_ratio { worst_ratio = r; }
            }
        }
        println!("e = {}: tested {} (skipped {} with sigma(m) >= e, outside the hypothesis) M<= {}",
                 e, tested, skipped, lim);
        println!("   MASS-DEFECT BOUND  P^2 (e n - n') < 2 P n - c : violations {}", viol);
        println!("   sigma(n) < e                                  : violations {}", viol_sigma);
        println!("   tightness (rhs/lhs):  <2: {:.1}%   <10: {:.1}%   <100: {:.1}%   max {:.3e}",
                 100.0 * t2 as f64 / tested as f64,
                 100.0 * t10 as f64 / tested as f64,
                 100.0 * t100 as f64 / tested as f64, worst_ratio);
    }
}
