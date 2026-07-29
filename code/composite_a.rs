// composite_a.rs — the composite-a mechanism, and its search.
//
// prop:family gave an explicit Pythagorean family but was PERMANENTLY on rung -1: its a is
// prime, so a' = 1 and a' = b is impossible. A cycle needs a COMPOSITE with a' = b. Take the
// smallest composite shape carrying the right mass, a = 2m with m odd squarefree. Then
//
//     a' = (2m)' = m + 2m' =: b,     and the cycle condition is    b' = a = 2m.
//
// So, with sigma(a) = 1/2 + sigma(m) ~ 1/2 and sigma(b) ~ 2 (their product being 1):
//
//     #307 with 2 | a   <=>   exists odd squarefree m with b = m + 2m' squarefree, coprime
//                             to 2m, and b' = 2m.
//
// For m = q PRIME this specialises to b = q + 2 with b' = 2b - 4: a single line, c = -4.
// Unlike prop:family this mechanism lands on rung k = 0 -- it IS the cycle -- so it is barred
// only by SCALE (sigma(b) = 2 - 4/b forces omega(b) >= 58), not by structure.
//
// This program searches the reduction directly and reports the nearest misses.
//
// Build: rustc -O -o composite_a composite_a.rs
// Run:   ./composite_a [LIMIT]      default 20_000_000   (m ranges over odd squarefree <= LIMIT)

fn main() {
    let lim: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(20_000_000);

    let mut spf = vec![0u32; lim + 1];
    for i in 2..=lim { if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } }
    let mut der = vec![0i64; lim + 1];
    let mut sf = vec![false; lim + 1]; sf[1] = true;
    for n in 2..=lim {
        let p = spf[n] as usize; let q = n / p;
        if q % p == 0 || !sf[q] { continue; }
        sf[n] = true;
        der[n] = if q > 1 { der[q] * p as i64 + q as i64 } else { 1 };
    }
    // derivative of b, which may exceed lim: factor on the fly
    let deriv_big = |mut x: i64| -> Option<i64> {
        if x < 2 { return None; }
        let mut ps: Vec<i64> = Vec::new();
        let mut d = 2i64;
        while d * d <= x {
            if x % d == 0 {
                x /= d;
                if x % d == 0 { return None; }        // not squarefree
                ps.push(d);
            }
            d += if d == 2 { 1 } else { 2 };
        }
        if x > 1 { ps.push(x); }
        let prod: i64 = ps.iter().product();
        Some(ps.iter().map(|&p| prod / p).sum())
    };
    fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a } else { gcd(b, a % b) } }

    let (mut tested, mut hits) = (0u64, 0u64);
    let mut best_gap = i64::MAX; let mut best_m = 0i64;
    let mut prime_case = 0u64;
    for m in (3..=lim).step_by(2) {
        if !sf[m] { continue; }
        let mi = m as i64;
        let b = mi + 2 * der[m];
        if b < 2 { continue; }
        if gcd(b, 2 * mi) != 1 { continue; }
        tested += 1;
        let db = match deriv_big(b) { Some(v) => v, None => continue };
        let gap = (db - 2 * mi).abs();
        if gap < best_gap { best_gap = gap; best_m = mi; }
        if db == 2 * mi {
            hits += 1;
            println!("  *** CYCLE: m = {}  a = 2m = {}  b = {}  (b' = {} = a)", mi, 2 * mi, b, db);
        }
        if spf[m] as usize == m { prime_case += 1; }   // m prime: the b' = 2b-4 line
    }
    println!("\ncomposite-a reduction  b = m + 2m',  need b' = 2m");
    println!("  odd squarefree m <= {} with b coprime to 2m: {} tested ({} with m prime)", lim, tested, prime_case);
    println!("  cycles found: {}", hits);
    println!("  nearest miss: |b' - 2m| = {} at m = {}", best_gap, best_m);
    println!("\n  (sigma(b) = 2 - 4/b on the m-prime line forces omega(b) >= 58, so the");
    println!("   reduction is barred by SCALE, not structure -- unlike prop:family's rung -1.)");
}
