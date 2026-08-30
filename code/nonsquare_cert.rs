// Replace the Nat.sqrt test in Sixty.lean's DFS by a modular non-residue certificate.
//
// plusVal(l) = sum_p (prod l / p) + 2 * prod l is enormous (~10^130), and `Nat.sqrt` on it is
// structural recursion the Lean kernel must unfold ~430 times per leaf. But n mod m needs no big
// arithmetic at all: prod/p is the product of the OTHER primes, so everything reduces mod m.
// If n is a non-residue mod m then n is not a square. This finds a small covering set of moduli.

fn main() {
    let forced: Vec<u64> = vec![2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
        73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167];
    let pool: Vec<u64> = vec![173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,
        263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,
        359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,
        457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,
        569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,
        659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,
        769,773,787];
    let thr: f64 = 2.0 - forced.iter().map(|&p| 1.0 / p as f64).sum::<f64>();
    let inv: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();

    // collect the admissible supports
    let mut supports: Vec<Vec<u64>> = Vec::new();
    fn go(i: usize, need: usize, cur: f64, chosen: &mut Vec<u64>, pool: &Vec<u64>,
          inv: &Vec<f64>, thr: f64, out: &mut Vec<Vec<u64>>) {
        if need == 0 { if cur >= thr - 1e-15 { out.push(chosen.clone()); } return; }
        if i >= pool.len() { return; }
        let best: f64 = inv[i..].iter().take(need).sum();
        if cur + best < thr - 1e-15 { return; }
        chosen.push(pool[i]);
        go(i + 1, need - 1, cur + inv[i], chosen, pool, inv, thr, out);
        chosen.pop();
        go(i + 1, need, cur, chosen, pool, inv, thr, out);
    }
    go(0, 20, 0.0, &mut Vec::new(), &pool, &inv, thr, &mut supports);
    println!("admissible supports: {}", supports.len());

    // n mod m, computed without any big arithmetic
    let val_mod = |l: &Vec<u64>, m: u64| -> u64 {
        let mut prod: u64 = 1;
        for &p in l { prod = prod * (p % m) % m; }
        let mut s: u64 = 0;
        for &p in l {
            let mut q: u64 = 1;
            for &r in l { if r != p { q = q * (r % m) % m; } }
            s = (s + q) % m;
        }
        (s + 2 * prod) % m
    };
    let squares = |m: u64| -> Vec<bool> {
        let mut v = vec![false; m as usize];
        for k in 0..m { v[(k * k % m) as usize] = true; }
        v
    };

    let mut cands: Vec<u64> = vec![8, 16, 32, 64, 9, 27, 25, 49, 121, 169];
    for p in [3u64,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
              101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199] {
        cands.push(p);
    }
    let mut uncovered: Vec<usize> = (0..supports.len()).collect();
    let mut chosen_mods: Vec<u64> = Vec::new();

    while !uncovered.is_empty() && chosen_mods.len() < 40 {
        let (mut best_m, mut best_hit) = (0u64, 0usize);
        for &m in &cands {
            if chosen_mods.contains(&m) { continue; }
            let sq = squares(m);
            let mut hit = 0usize;
            for &i in &uncovered {
                let mut full = forced.clone(); full.extend(&supports[i]);
                if !sq[val_mod(&full, m) as usize] { hit += 1; }
            }
            if hit > best_hit { best_hit = hit; best_m = m; }
        }
        if best_hit == 0 { break; }
        let sq = squares(best_m);
        uncovered.retain(|&i| {
            let mut full = forced.clone(); full.extend(&supports[i]);
            sq[val_mod(&full, best_m) as usize]
        });
        chosen_mods.push(best_m);
        println!("  modulus {:3} covers {:6} more; remaining {}", best_m, best_hit, uncovered.len());
    }
    println!("\nchosen moduli: {:?}", chosen_mods);
    println!("supports still uncovered: {}", uncovered.len());
    if !uncovered.is_empty() {
        let mut full = forced.clone(); full.extend(&supports[uncovered[0]]);
        println!("  example uncovered support: {:?}", supports[uncovered[0]]);
        let _ = full;
    }
}
