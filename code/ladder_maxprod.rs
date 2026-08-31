// Case B of the level-61 height: the bottom 59 carry mass < 2. Then every element obeys the mass
// ladder u_j <= (61-j+1)/(2 - sum_{i<j} 1/u_i), and we need the largest product such a chain can
// have. Branch and bound on increasing prime chains, maximising the log-product.
fn primes_upto(n: u64) -> Vec<u64> {
    let mut s = vec![true; (n + 1) as usize];
    let (mut v, mut i) = (Vec::new(), 2u64);
    while i <= n {
        if s[i as usize] { v.push(i); let mut j = i * i; while j <= n { s[j as usize] = false; j += i; } }
        i += 1;
    }
    v
}
fn main() {
    let k = 61usize;
    let p = primes_upto(3000);
    let lg: Vec<f64> = p.iter().map(|&x| (x as f64).log10()).collect();
    let mut best = f64::MIN;
    // dfs over positions 1..=59 choosing increasing primes obeying the ladder
    fn go(pos: usize, start: usize, mass: f64, acc: f64, p: &Vec<u64>, lg: &Vec<f64>,
          k: usize, best: &mut f64) {
        if pos > 59 { if mass < 2.0 && acc > *best { *best = acc; } return; }
        let rem = 2.0 - mass;
        if rem <= 0.0 { return; }                       // ladder needs a positive residual
        let bound = (k - pos + 1) as f64 / rem;
        // optimistic completion: every remaining position takes the largest prime under `bound`
        let mut hi = start;
        while hi < p.len() && (p[hi] as f64) <= bound { hi += 1; }
        if hi <= start { return; }                       // no admissible prime here
        let opt = acc + (60 - pos) as f64 * lg[hi - 1];
        if opt <= *best { return; }
        for idx in (start..hi).rev() {
            go(pos + 1, idx + 1, mass + 1.0 / p[idx] as f64, acc + lg[idx], p, lg, k, best);
        }
    }
    go(1, 0, 0.0, 0.0, &p, &lg, k, &mut best);
    println!("case B (bottom 59 of mass < 2, level 61):");
    println!("  max log10 prod(S_59) under the ladder = {:.3}", best);
    let d = best;
    println!();
    println!("  u_60 <= 2D            -> log10 <= {:.2}", d + (2.0f64).log10());
    println!("  u_61 <= 1.11 * D*u_60 -> log10 <= {:.2}", 2.0*d + (2.22f64).log10());
    println!("  log10 prod U          <= {:.2}", d + (d + (2.0f64).log10()) + (2.0*d + (2.22f64).log10()));
}
