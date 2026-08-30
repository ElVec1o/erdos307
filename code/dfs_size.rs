// How big is the Sixty.lean DFS tree? This decides whether kernel `decide` can replace
// `native_decide` on `dfs_run`.
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
    println!("pool {} primes, thr = {:.12}", pool.len(), thr);

    // prefix sums of the largest available reciprocals
    let inv: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    let (mut nodes, mut leaves, mut checks) = (0u64, 0u64, 0u64);

    fn go(i: usize, need: usize, cur: f64, inv: &Vec<f64>, thr: f64,
          nodes: &mut u64, leaves: &mut u64, checks: &mut u64) {
        *nodes += 1;
        if need == 0 { *leaves += 1; if cur >= thr - 1e-15 { *checks += 1; } return; }
        if i >= inv.len() { return; }
        // best possible from the remaining, taking the `need` largest reciprocals available
        let best: f64 = inv[i..].iter().take(need).sum();
        if cur + best < thr - 1e-15 { return; }
        go(i + 1, need - 1, cur + inv[i], inv, thr, nodes, leaves, checks);
        go(i + 1, need, cur, inv, thr, nodes, leaves, checks);
    }
    go(0, 20, 0.0, &inv, thr, &mut nodes, &mut leaves, &mut checks);
    println!("DFS nodes visited : {}", nodes);
    println!("leaves reached    : {}", leaves);
    println!("nsqB checks (admissible supports) : {}", checks);
}
