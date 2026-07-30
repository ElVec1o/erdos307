// a10_nearmiss.rs -- the near-miss spectrum of #307. A10 attacked from the POSITIVE side.
//
// Every result in this project so far bounds the NO direction: barriers, density zero, closures.
// The positive direction has never been measured. #307 asks for a with a'' = a exactly; the
// natural quantitative shadow of that is the DEFECT
//        d(a) = a'' - a,
// defined whenever a and a' are both squarefree. A solution is d(a) = 0. The heuristic count of
// solutions below X is ~ c log X, arising as sum_a 1/a: for each a the value a'' is a determined
// integer of size ~a, so it lands on a with "probability" ~1/a. That heuristic makes a sharp
// prediction this program can test: the smallest |d(a)| for a <= X should fall like a constant,
// NOT like X, because near-misses accumulate. If instead min|d| grows with X, the heuristic that
// underwrites "solutions exist" is wrong, and A10's expected answer flips.
//
// Build: rustc -O -o a10_nearmiss a10_nearmiss.rs
// Memory: one u32 spf table over [0, LIM]; nothing else scales.
fn main() {
    let a_max: usize = 10_000_000;
    let lim: usize = 40_000_000;            // a' can exceed a; sieve far enough to factor it
    eprintln!("sieving spf to {} ({} MB)...", lim, 4 * (lim + 1) / 1_048_576);
    let mut spf = vec![0u32; lim + 1];
    let mut i = 2usize;
    while i <= lim {
        if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } }
        i += 1;
    }
    // derivative of a squarefree n, using spf; returns None if n is not squarefree
    let deriv = |mut n: usize| -> Option<u128> {
        if n == 1 { return Some(0); }
        let orig = n as u128;
        let mut d: u128 = 0;
        while n > 1 {
            let p = spf[n] as usize;
            n /= p;
            if n % p == 0 { return None; }          // not squarefree
            d += orig / p as u128;
        }
        Some(d)
    };
    let mut best_abs: u128 = u128::MAX; let mut best_a = 0usize;
    let mut best_rel: f64 = f64::MAX;   let mut best_rel_a = 0usize;
    let mut exact = 0u64;
    let mut checked = 0u64; let mut both_sf = 0u64;
    // near-miss spectrum: how many a have |d(a)| <= a^theta
    let mut spectrum = [0u64; 11];
    for a in 2..=a_max {
        let da = match deriv(a) { Some(v) => v, None => continue };
        checked += 1;
        if da == 0 || da as usize > lim { continue; }
        let dda = match deriv(da as usize) { Some(v) => v, None => continue };
        both_sf += 1;
        let d = if dda >= a as u128 { dda - a as u128 } else { a as u128 - dda };
        if d == 0 { exact += 1; println!("*** TWO-CYCLE: a = {}  a' = {}  a'' = {}", a, da, dda); }
        if d > 0 && d < best_abs { best_abs = d; best_a = a; }
        let rel = d as f64 / a as f64;
        if d > 0 && rel < best_rel { best_rel = rel; best_rel_a = a; }
        // theta buckets
        let la = (a as f64).ln();
        if d > 0 {
            let th = (d as f64).ln() / la;
            let b = (th * 10.0).floor().max(0.0).min(10.0) as usize;
            spectrum[b] += 1;
        }
    }
    println!("\na <= {}: {} squarefree, {} with a' squarefree too", a_max, checked, both_sf);
    println!("EXACT two-cycles found: {}   (barrier says 0 below 1e112.9)", exact);
    println!("\nsmallest nonzero |a'' - a| : {}  at a = {}", best_abs, best_a);
    println!("smallest relative defect   : {:.3e}  at a = {}", best_rel, best_rel_a);
    println!("\nnear-miss spectrum, count of a with |d| ~ a^theta:");
    for b in 0..11 {
        if spectrum[b] > 0 {
            println!("   theta in [{:.1},{:.1}) : {}", b as f64 / 10.0, (b + 1) as f64 / 10.0, spectrum[b]);
        }
    }
}
