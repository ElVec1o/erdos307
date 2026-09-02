// deriv_trajectory.rs — Erdős #307 / arithmetic-derivative experiment.
//
// For every squarefree n ≤ N, computes the "proto-cycle product"
//      mp(n) = mass(n) · mass(n'),   mass(m) = Σ_{p|m} 1/p,   n' = Σ_{p|n} n/p,
// which equals D²(n)/n and is exactly the #307 condition (mp = 1 ⇔ a 2-cycle a=n, b=n').
// Tracks the MAX mp by decade (does the champion climb toward 1, or stall = a ceiling?),
// and exhaustively flags any exact 2-cycle (D(D(n)) = n).  Honest experiment: let the data speak.
//
// Build:  rustc -O -o deriv_trajectory deriv_trajectory.rs
// Run:    ./deriv_trajectory 1000000000 10000000        (N, segment size)  -- prints progress+ETA

use std::env;
use std::time::Instant;

fn main() {
    let a: Vec<String> = env::args().collect();
    let n: u64 = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(1_000_000_000);
    let seg: u64 = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(10_000_000);

    // base primes up to sqrt(N)
    let root = ((n as f64).sqrt() as u64) + 2;
    let mut comp = vec![false; (root + 1) as usize];
    let mut primes: Vec<u64> = Vec::new();
    for i in 2..=root {
        if !comp[i as usize] {
            primes.push(i);
            let mut j = i * i;
            while j <= root { comp[j as usize] = true; j += i; }
        }
    }
    let small: Vec<u64> = primes.iter().cloned().take_while(|&p| p <= 5000).collect();

    // self-test: D(2*3*5)=31, D(15)=8, D(2156595)=1711424 (the 3e6 champion)
    assert_eq!(full_deriv(30, &primes), 31);
    assert_eq!(full_deriv(15, &primes), 8);
    assert_eq!(full_deriv(2156595, &primes), 1711424);
    eprintln!("self-test ok; primes≤√N: {}, small primes: {}", primes.len(), small.len());

    let start = Instant::now();
    let mut best_mp = 0.0f64;
    let (mut best_a, mut best_b) = (0u64, 0u64);
    let mut bucket = vec![0.0f64; 21]; // bucket[k] = max mp for n in (10^(k-1), 10^k]
    let mut exact = 0u64;

    let mut lo = 2u64;
    while lo <= n {
        let hi = (lo + seg - 1).min(n);
        let len = (hi - lo + 1) as usize;
        let mut rem: Vec<u64> = (lo..=hi).collect();
        let mut mass = vec![0.0f64; len];
        let mut deriv = vec![0u64; len];
        let mut sqfree = vec![true; len];

        for &p in &primes {
            if p * p > hi { break; }
            let mut j = ((lo + p - 1) / p) * p;
            while j <= hi {
                let i = (j - lo) as usize;
                if rem[i] % p == 0 {
                    mass[i] += 1.0 / (p as f64);
                    deriv[i] += (lo + i as u64) / p;
                    rem[i] /= p;
                    if rem[i] % p == 0 { sqfree[i] = false; while rem[i] % p == 0 { rem[i] /= p; } }
                }
                j += p;
            }
        }
        for i in 0..len {
            let nn = lo + i as u64;
            if rem[i] > 1 { // leftover prime > sqrt
                mass[i] += 1.0 / (rem[i] as f64);
                deriv[i] += nn / rem[i];
            }
            if !sqfree[i] || nn < 2 { continue; }
            let b = deriv[i];
            if b <= 1 || b == nn { continue; }
            // mass(b) from small primes (+ one large leftover ~0)
            let mut mb = 0.0f64; let mut r = b;
            for &p in &small {
                if p * p > r { break; }
                if r % p == 0 { mb += 1.0 / (p as f64); while r % p == 0 { r /= p; } }
            }
            if r > 1 { mb += 1.0 / (r as f64); }
            let mp = mass[i] * mb;
            // decade bucket
            let mut k = 0usize; let mut pw = 10u64;
            while pw < nn && k < 19 { pw = pw.saturating_mul(10); k += 1; }
            if mp > bucket[k] { bucket[k] = mp; }
            if mp > best_mp { best_mp = mp; best_a = nn; best_b = b; }
            // exact-cycle check for serious candidates
            if mp > 0.90 {
                if full_deriv(b, &primes) == nn { exact += 1; println!("\n*** EXACT 2-CYCLE: {} <-> {} ***", nn, b); }
            }
        }
        let frac = hi as f64 / n as f64;
        let el = start.elapsed().as_secs_f64();
        eprint!("\r  {:.1}%  n={}  best mp={:.4} (a={})  ETA {:.0}s     ",
                frac * 100.0, hi, best_mp, best_a, el / frac - el);
        lo = hi + 1;
    }
    eprintln!();
    println!("\n=== arithmetic-derivative proto-cycle trajectory, N = {} ===", n);
    println!("exact 2-cycles found: {}", exact);
    println!("global champion: mass-product = {:.5}   a = {}   b = a' = {}", best_mp, best_a, best_b);
    println!("max mass-product by decade (cumulative):");
    let mut run = 0.0f64;
    for k in 1..bucket.len() {
        if bucket[k] > run { run = bucket[k]; }
        if 10u64.checked_pow(k as u32).map_or(true, |v| v <= n.saturating_mul(10)) && bucket[k] > 0.0 {
            println!("  n ≤ 10^{:<2}: {:.4}", k, run);
        }
    }
    println!("(climb continuing → existence-plausible to this scale; stall → a real ceiling.)");
}

fn full_deriv(n: u64, primes: &[u64]) -> u64 {
    let mut b = n; let mut d = 0u64;
    for &p in primes {
        if p * p > b { break; }
        if b % p == 0 { d += n / p; while b % p == 0 { b /= p; } }
    }
    if b > 1 { d += n / b; }
    d
}
