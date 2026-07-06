// descended_hunt.rs — hunt for a 2-cycle of the DESCENDED operator of Remark rem:descent.
//
// The descended operator D acts on odd squarefree m = prod P:
//     D(m) = sum_{p | m} t_p * (m/p),
// where for a SPLIT prime p = x^2 + y^2 (p ≡ 1 mod 4, x odd, y even) the value
//     t_p ∈ {±2x, ±2y}     (Frobenius traces of y^2 = x^3 - x and its twists, CM by Z[i]),
// and for an INERT prime q ≡ 3 mod 4 the value  ε_q ∈ {±1}.
//
// A 2-cycle is a pair m ≠ m' with D(m) = m' and D(m') = m, both odd squarefree, coprime
// (proved), each with an odd number of primes ≡ 3 mod 4 (parity: D(m) is odd iff #inert odd).
// #307's 59-prime barrier does NOT apply here (values ~2√p, mass reaches 2 with 4 primes),
// so small solutions are possible. The paper searched m ≤ 1e9, ω ≤ 8, and found none;
// this program pushes ω = 4..6 with a configurable prime pool BEYOND that box.
//
// Build:  rustc -O -o descended_hunt descended_hunt.rs
// Run:    ./descended_hunt [OMEGA_MIN OMEGA_MAX P_MIN P_MAX LO_LOG10 HI_LOG10]
//   defaults: 4 6 3 600 9 12   (ω 4..6, odd primes in [3,600], product in [1e9, 1e12])
//
// Prints ETA / progress every few seconds and writes any hit + a resume marker to
// descended_hunt.out.  A HIT is a genuine descended 2-cycle — the first known, if it exists.

use std::env;
use std::fs::OpenOptions;
use std::io::Write;
use std::time::Instant;

fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    for &p in &[2u64,3,5,7,11,13,17,19,23,29,31,37] {
        if n % p == 0 { return n == p; }
    }
    // Miller-Rabin, deterministic for u64
    let mut d = n - 1; let mut r = 0;
    while d % 2 == 0 { d /= 2; r += 1; }
    'w: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37] {
        let mut x = mod_pow(a % n, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..r-1 { x = mod_mul(x, x, n); if x == n - 1 { continue 'w; } }
        return false;
    }
    true
}
fn mod_mul(a: u64, b: u64, m: u64) -> u64 { ((a as u128 * b as u128) % m as u128) as u64 }
fn mod_pow(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64; a %= m;
    while e > 0 { if e & 1 == 1 { r = mod_mul(r, a, m); } a = mod_mul(a, a, m); e >>= 1; }
    r
}

// Pollard rho
fn pollard_rho(n: u64) -> u64 {
    if n % 2 == 0 { return 2; }
    let mut c = 1u64;
    loop {
        let f = |x: u64| (mod_mul(x, x, n) + c) % n;
        let (mut x, mut y, mut d) = (2u64, 2u64, 1u64);
        while d == 1 { x = f(x); y = f(f(y)); d = gcd(if x > y { x - y } else { y - x }, n); }
        if d != n { return d; }
        c += 1;
    }
}
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }

// factor into sorted primes; returns None if a repeated factor (not squarefree)
fn factor_squarefree(mut n: u64) -> Option<Vec<u64>> {
    let mut fs = Vec::new();
    // small trial
    for &p in &[3u64,5,7,11,13,17,19,23,29,31,37,41,43,47] {
        if n % p == 0 { n /= p; if n % p == 0 { return None; } fs.push(p); }
    }
    // rho for the rest
    let mut stack = vec![n];
    while let Some(m) = stack.pop() {
        if m == 1 { continue; }
        if is_prime_u64(m) { fs.push(m); continue; }
        let d = pollard_rho(m);
        stack.push(d); stack.push(m / d);
    }
    fs.sort_unstable();
    for w in fs.windows(2) { if w[0] == w[1] { return None; } }
    Some(fs)
}

// the allowed descended values for a prime p (as i128, includes signs)
fn values(p: u64) -> Vec<i128> {
    if p % 4 == 3 { return vec![1, -1]; }
    // split: p = x^2 + y^2, x odd, y even
    let mut y = 0u64;
    while y * y <= p {
        let x2 = p - y * y;
        let x = (x2 as f64).sqrt() as u64;
        for xx in [x.saturating_sub(1), x, x + 1] {
            if xx * xx == x2 && xx % 2 == 1 {
                let (xi, yi) = (xx as i128, y as i128);
                return vec![2 * xi, -2 * xi, 2 * yi, -2 * yi];
            }
        }
        y += 1;
    }
    vec![] // shouldn't happen for p ≡ 1 mod 4
}

// compute all distinct D(m) over value assignments; call `visit` on each (D value, )
// coeffs[i] = m / p_i ; valsets[i] = allowed values for p_i
fn enum_D(coeffs: &[i128], valsets: &[Vec<i128>], acc: i128, i: usize, out: &mut Vec<i128>) {
    if i == coeffs.len() { out.push(acc); return; }
    for &v in &valsets[i] {
        enum_D(coeffs, valsets, acc + v * coeffs[i], i + 1, out);
    }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let g = |i: usize, d: u64| a.get(i).and_then(|s| s.parse().ok()).unwrap_or(d);
    let omega_min = g(1, 4) as usize;
    let omega_max = g(2, 6) as usize;
    let p_min = g(3, 3);
    let p_max = g(4, 600);
    let lo = 10f64.powi(g(5, 9) as i32) as u128;
    let hi = 10f64.powi(g(6, 12) as i32) as u128;

    // odd prime pool
    let pool: Vec<u64> = (p_min..=p_max).filter(|&n| n % 2 == 1 && is_prime_u64(n)).collect();
    let valcache: Vec<Vec<i128>> = pool.iter().map(|&p| values(p)).collect();
    let is3: Vec<bool> = pool.iter().map(|&p| p % 4 == 3).collect();

    eprintln!("descended_hunt: pool {} primes [{}..{}], ω {}..{}, product [1e{}..1e{}]",
              pool.len(), p_min, p_max, omega_min, omega_max, g(5,9), g(6,12));
    let start = Instant::now();
    let mut tested: u64 = 0;
    let mut cand_valid: u64 = 0;
    let mut hits: u64 = 0;
    let mut last = Instant::now();

    // recursive DFS choosing an increasing subset P of pool
    // frame passed explicitly to keep prod / #inert / chosen list
    // (indices into pool)
    fn dfs(
        pool: &[u64], valcache: &[Vec<i128>], is3: &[bool],
        lo: u128, hi: u128, omega_min: usize, omega_max: usize,
        start_idx: usize, chosen: &mut Vec<usize>, prod: u128, ninert: usize,
        tested: &mut u64, cand_valid: &mut u64, hits: &mut u64,
        start: &Instant, last: &mut Instant,
    ) {
        let k = chosen.len();
        if k >= omega_min && prod >= lo && prod <= hi && ninert % 2 == 1 {
            // evaluate this m
            *tested += 1;
            let m = prod;
            let coeffs: Vec<i128> = chosen.iter().map(|&i| (m / pool[i] as u128) as i128).collect();
            let valsets: Vec<Vec<i128>> = chosen.iter().map(|&i| valcache[i].clone()).collect();
            let mut ds = Vec::new();
            enum_D(&coeffs, &valsets, 0, 0, &mut ds);
            let pset: Vec<u64> = chosen.iter().map(|&i| pool[i]).collect();
            for d in ds {
                if d <= 1 { continue; }
                let mp = d as u128;
                if mp == m || mp % 2 == 0 { continue; }
                if mp > (u64::MAX as u128) { continue; }
                let mpu = mp as u64;
                // coprime to m ?
                if pset.iter().any(|&p| mpu % p == 0) { continue; }
                // m' odd squarefree, ω ≤ omega_max ?
                let q = match factor_squarefree(mpu) { Some(q) => q, None => continue };
                if q.len() > omega_max { continue; }
                // parity of m'
                if q.iter().filter(|&&x| x % 4 == 3).count() % 2 != 1 { continue; }
                *cand_valid += 1;
                // closure: exists assignment on Q with D(m') = m ?
                let coeffs2: Vec<i128> = q.iter().map(|&p| (mp / p as u128) as i128).collect();
                let valsets2: Vec<Vec<i128>> = q.iter().map(|&p| values(p)).collect();
                let mut ds2 = Vec::new();
                enum_D(&coeffs2, &valsets2, 0, 0, &mut ds2);
                if ds2.iter().any(|&e| e == m as i128) {
                    *hits += 1;
                    let msg = format!(
                        "\n*** DESCENDED 2-CYCLE FOUND ***\n  m  = {}  (primes {:?})\n  m' = {}  (primes {:?})\n  D(m)=m', D(m')=m verified.\n",
                        m, pset, mpu, q);
                    println!("{}", msg);
                    if let Ok(mut f) = OpenOptions::new().create(true).append(true).open("descended_hunt.out") {
                        let _ = f.write_all(msg.as_bytes());
                    }
                }
            }
            // progress
            if last.elapsed().as_secs_f64() > 4.0 {
                let el = start.elapsed().as_secs_f64();
                eprint!("\r  tested {}  valid-m' {}  hits {}  {:.0}s  ({:.0}/s)   ",
                        tested, cand_valid, hits, el, *tested as f64 / el.max(1e-9));
                *last = Instant::now();
                // interim save
                if let Ok(mut f) = OpenOptions::new().create(true).write(true).truncate(true).open("descended_hunt.progress") {
                    let _ = writeln!(f, "tested {} valid-m' {} hits {} elapsed {:.0}s", tested, cand_valid, hits, el);
                }
            }
        }
        if k == omega_max { return; }
        for i in start_idx..pool.len() {
            let np = prod.saturating_mul(pool[i] as u128);
            if np > hi { break; } // pool sorted asc; product only grows
            chosen.push(i);
            dfs(pool, valcache, is3, lo, hi, omega_min, omega_max, i + 1, chosen,
                np, ninert + if is3[i] {1} else {0}, tested, cand_valid, hits, start, last);
            chosen.pop();
        }
    }

    let mut chosen = Vec::new();
    dfs(&pool, &valcache, &is3, lo, hi, omega_min, omega_max, 0, &mut chosen, 1, 0,
        &mut tested, &mut cand_valid, &mut hits, &start, &mut last);

    eprintln!();
    println!("=== descended_hunt done ===");
    println!("m tested (odd count of ≡3 mod4, product in range): {}", tested);
    println!("valid m' (odd squarefree coprime, ω≤{}): {}", omega_max, cand_valid);
    println!("2-cycles found: {}", hits);
    if hits == 0 { println!("=> no descended 2-cycle in this box (ω {}..{}, primes ≤{}, product ≤1e{})",
                            omega_min, omega_max, p_max, g(6,12)); }
    println!("time {:.0}s", start.elapsed().as_secs_f64());
}
