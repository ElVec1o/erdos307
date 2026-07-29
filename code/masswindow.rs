// masswindow.rs — the two-sided mass window for minus-layer supports.
//
// For a minus-layer hit N (N' - 2N = d^2) write p = P+(N), m = N/p, k = 2m - m'. Leibniz
// gives N' = p m' + m, so
//     d^2 = N' - 2N = p(m' - 2m) + m = m - p k ,
// hence d^2 >= 0 forces p k <= m, and dividing sigma(N) - 2 = d^2/N = (m - pk)/(pm):
//
//     sigma(N)  =  2 + 1/P+(N)  -  k/m ,      k = 2m - m' >= 1 .
//
// So every minus-layer support obeys the TWO-SIDED window
//
//     2  <  sigma(U)  <  2 + 1/max(U) ,    equivalently    sigma(U \ {max U})  <  2 .
//
// The upper half is new: the barrier supplies only sigma > 2. This program measures how much
// the upper half prunes the level-59 candidate list of prop:close59 (39 forced primes <= 167
// plus 20 chosen from (167,787], those with sigma > 2 numbering 49,961).
//
// Build: rustc -O -o masswindow masswindow.rs

fn main() {
    // primes to 800
    let n = 800usize;
    let mut is = vec![true; n + 1]; is[0] = false; is[1] = false;
    let mut i = 2; while i * i <= n { if is[i] { let mut j = i * i; while j <= n { is[j] = false; j += i; } } i += 1; }
    let primes: Vec<usize> = (2..=n).filter(|&x| is[x]).collect();

    let t = |ps: &[usize]| -> f64 { ps.iter().map(|&p| 1.0 / p as f64).sum() };
    let t60: f64 = t(&primes[..60]);
    let t58: f64 = t(&primes[..58]);

    let forced: Vec<usize> = primes.iter().cloned().filter(|&p| t60 - 1.0 / p as f64 > 2.0 - 1e-15).collect();
    let forced: Vec<usize> = primes.iter().cloned().filter(|&p| p <= 167).collect();
    let pool: Vec<usize> = primes.iter().cloned()
        .filter(|&p| p > 167 && t58 + 1.0 / p as f64 > 2.0).collect();
    let k = 59 - forced.len();
    let base = t(&forced);
    println!("forced {} primes (<= {}), pool {} primes [{}..{}], choose {}",
             forced.len(), forced[forced.len() - 1], pool.len(), pool[0], pool[pool.len() - 1], k);

    let pf: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    // suffix sums for pruning
    let mut suf = vec![0.0f64; pool.len() + 1];
    for i in (0..pool.len()).rev() { suf[i] = suf[i + 1] + pf[i]; }

    let mut total: u64 = 0;          // sigma > 2                     (prop:close59's 49,961)
    let mut window: u64 = 0;         // 2 < sigma < 2 + 1/max         (the new condition)
    let mut min_margin = f64::MAX;   // how close to the upper edge does a survivor get
    let mut chosen: Vec<usize> = Vec::with_capacity(k);

    fn dfs(i: usize, need: usize, cur: f64, pool: &[usize], pf: &[f64], suf: &[f64],
           base: f64, chosen: &mut Vec<usize>, total: &mut u64, window: &mut u64,
           min_margin: &mut f64) {
        if need == 0 {
            let sigma = base + cur;
            if sigma > 2.0 {
                *total += 1;
                let mx = *chosen.last().unwrap();          // pool is ascending: last chosen is max
                let upper = 2.0 + 1.0 / mx as f64;
                if sigma < upper {
                    *window += 1;
                    let marg = upper - sigma;
                    if marg < *min_margin { *min_margin = marg; }
                }
            }
            return;
        }
        if i + need > pool.len() { return; }
        if base + cur + (suf[i] - suf[i + need]) <= 2.0 { return; }   // best possible
        chosen.push(pool[i]);
        dfs(i + 1, need - 1, cur + pf[i], pool, pf, suf, base, chosen, total, window, min_margin);
        chosen.pop();
        dfs(i + 1, need, cur, pool, pf, suf, base, chosen, total, window, min_margin);
    }

    dfs(0, k, 0.0, &pool, &pf, &suf, base, &mut chosen, &mut total, &mut window, &mut min_margin);

    println!("\nlevel-59 admissible supports (sigma > 2)          : {}", total);
    println!("also satisfying sigma < 2 + 1/max(U)  [NEW WINDOW] : {}", window);
    println!("pruned by the upper half of the window             : {}  ({:.2}%)",
             total - window, 100.0 * (total - window) as f64 / total as f64);
    println!("tightest surviving margin (upper - sigma)          : {:.3e}", min_margin);
}
