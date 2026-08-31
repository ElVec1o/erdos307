// I3 phenomenon gate: the pairing chi(n) = sigma(n) sigma(D(n)) that a two-cycle must set to 1.
// Sieve squarefree n <= X, compute D(n) = n * sum_{p|n} 1/p, keep those with D(n) squarefree, and
// record max, mean, and the maximiser. Prediction is frozen in the research log before this runs.
fn main() {
    let x: usize = 200_000_000;
    let mut spf = vec![0u32; x + 1];
    for i in 2..=x {
        if spf[i] == 0 { let mut j = i; while j <= x { if spf[j] == 0 { spf[j] = i as u32; } j += i; } }
    }
    let sq = |mut n: usize, spf: &Vec<u32>| -> bool {
        while n > 1 { let p = spf[n] as usize; n /= p; if n % p == 0 { return false; } }
        true
    };
    // milestones so we can see M(X) grow
    let marks: Vec<usize> = vec![10_000_000, 25_000_000, 50_000_000, 100_000_000, 200_000_000];
    let mut mi = 0usize;
    let (mut best, mut bestn) = (0.0f64, 0usize);
    let (mut sum, mut cnt) = (0.0f64, 0u64);
    let mut over_one = 0u64;

    for n in 2..=x {
        if !sq(n, &spf) { continue; }
        // sigma(n) and D(n)
        let (mut m, mut s, mut d) = (n, 0.0f64, 0u64);
        while m > 1 { let p = spf[m] as usize; m /= p; s += 1.0 / p as f64; d += (n / p) as u64; }
        if d as usize > x || !sq(d as usize, &spf) { continue; }
        let (mut k, mut s2) = (d as usize, 0.0f64);
        while k > 1 { let p = spf[k] as usize; k /= p; s2 += 1.0 / p as f64; }
        let chi = s * s2;
        cnt += 1; sum += chi;
        if chi > 1.0 { over_one += 1; }
        if chi > best { best = chi; bestn = n; }
        if mi < marks.len() && n == marks[mi] {
            println!("  X = {:>11}   M(X) = {:.6}   argmax n = {:<10}   mean chi = {:.6}   n counted = {}",
                     n, best, bestn, sum / cnt as f64, cnt);
            mi += 1;
        }
    }
    println!("\nfinal: M = {:.6} at n = {}", best, bestn);
    let mut f = bestn; let mut fs = Vec::new();
    while f > 1 { let p = spf[f] as usize; f /= p; fs.push(p); }
    println!("argmax factorisation: {:?}", fs);
    println!("mean chi = {:.6}   (sum_p 1/p^2 = 0.452247)", sum / cnt as f64);
    println!("pairs with chi > 1 : {}", over_one);
}
