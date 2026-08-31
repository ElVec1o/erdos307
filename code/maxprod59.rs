// Maximum product of an admissible 59-element support (mass > 2). Feeds the level-61 height:
// thm:frame determines the two remaining primes from the split, with alpha, beta <= 4 D^2 / Delta.
fn main() {
    let forced39: Vec<u64> = vec![2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
        73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167];
    let pool: Vec<u64> = vec![173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,
        263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,
        359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,
        457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,
        569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,
        659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,
        769,773,787];
    let thr: f64 = 2.0 - forced39.iter().map(|&p| 1.0 / p as f64).sum::<f64>();
    let base_log: f64 = forced39.iter().map(|&p| (p as f64).log10()).sum();
    let inv: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    let lg: Vec<f64> = pool.iter().map(|&p| (p as f64).log10()).collect();
    let (mut best, mut worst, mut n) = (f64::MIN, f64::MAX, 0u64);

    fn go(i: usize, need: usize, cur: f64, acc: f64, inv: &Vec<f64>, lg: &Vec<f64>,
          thr: f64, best: &mut f64, worst: &mut f64, n: &mut u64) {
        if need == 0 {
            if cur >= thr - 1e-15 {
                *n += 1;
                if acc > *best { *best = acc; }
                if acc < *worst { *worst = acc; }
            }
            return;
        }
        if i >= inv.len() { return; }
        let bestrem: f64 = inv[i..].iter().take(need).sum();
        if cur + bestrem < thr - 1e-15 { return; }
        go(i + 1, need - 1, cur + inv[i], acc + lg[i], inv, lg, thr, best, worst, n);
        go(i + 1, need, cur, acc, inv, lg, thr, best, worst, n);
    }
    go(0, 20, 0.0, 0.0, &inv, &lg, thr, &mut best, &mut worst, &mut n);
    println!("admissible 59-element supports: {}", n);
    println!("log10 prod : min {:.3}   max {:.3}", base_log + worst, base_log + best);
    let d = base_log + best;
    println!();
    println!("thm:frame at level 61: alpha, beta <= 4 D^2 / Delta <= 4 D^2 for Delta >= 1");
    println!("  log10 alpha <= {:.2}", 2.0 * d + (4.0f64).log10());
    println!("  log10 prod U <= {:.2}", d + 2.0 * (2.0 * d + (4.0f64).log10()));
}
