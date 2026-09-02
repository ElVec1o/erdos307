// close59_minus.rs -- independent confirmation of prop:close59 via the MINUS square.
// The paper verifies that N'+2N is a non-square for all 49,961 admissible 59-prime supports.
// This checks the companion condition (a-b)^2 = N'-2N, computed split-free as the CRT of
// (N/l mod l) over l | N (the two agree: N' == N/l and 2N == 0 mod l, and 0 <= N'-2N < N here).
// Result: 49,961 supports, D2 a perfect square for none, 1.8 s.  Build: rustc -O (uses rug/GMP).

// THE SPLIT-FREE TEST.  For a support U with N = prod U, any two-cycle a'=b, b'=a on U has
//     d = b - a  with  d^2 == N/l (mod l) for EVERY l | N,
// so d^2 is pinned mod N by CRT; and d^2 = (b-a)^2 < N whenever t + 1/t < 3, which holds at
// T(U) ~ 2.006 (d^2/N ~ 0.0059).  Hence d^2 EQUALS the CRT value D2 exactly, so D2 must be a
// perfect square.  This is split-free: no 2^58 search over P|Q.
// Regression: the 49,961 admissible 59-prime supports of prop:close59, where no solution exists.
use rug::Integer;
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i*i <= n { if n % i == 0 { return false; } i += 1; } true }
fn main() {
    let forced: Vec<u64> = (2..=167).filter(|&p| is_prime(p)).collect();
    let pool:   Vec<u64> = (168..=787).filter(|&p| is_prime(p)).collect();
    let tf: f64 = forced.iter().map(|&p| 1.0/p as f64).sum();
    let need = 2.0 - tf;
    eprintln!("forced {} (T={:.9}), pool {}, choose 20, tail mass must exceed {:.9}", forced.len(), tf, pool.len(), need);
    // best[i] = max mass of 20 primes from pool[i..]
    let n = pool.len();
    // best[i][k] = max mass of k primes drawn from pool[i..].  Indexing only by i (always taking 20)
    // made the bound vacuous once k < 20 and the tree exploded.
    let mut best = vec![vec![0f64; 21]; n+1];
    for i in (0..n).rev() { for k in 1..=20 {
        best[i][k] = if i + k <= n { pool[i..].iter().take(k).map(|&p| 1.0/p as f64).sum() } else { -1.0 };
    } }
    let nforced = Integer::from(forced.iter().fold(Integer::from(1), |a,&p| a*p));
    let mut cnt: u64 = 0; let mut sq: u64 = 0; let mut sel: Vec<u64> = Vec::with_capacity(20);
    fn rec(i: usize, k: usize, m: f64, pool: &[u64], best: &[Vec<f64>], need: f64, forced: &[u64],
           nf: &Integer, sel: &mut Vec<u64>, cnt: &mut u64, sq: &mut u64) {
        if k == 0 {
            if m > need {
                *cnt += 1;
                let mut nn = nf.clone(); for &p in sel.iter() { nn *= p; }
                // CRT: d^2 == N/l (mod l) for every l | N
                let mut acc = Integer::from(0); let mut modulus = Integer::from(1);
                let all: Vec<u64> = forced.iter().chain(sel.iter()).cloned().collect();
                for &l in &all {
                    let li = Integer::from(l);
                    let cof = Integer::from(&nn / &li);
                    let r = cof.clone() % li.clone();
                    // solve acc' == acc (mod modulus), acc' == r (mod l)
                    let inv = modulus.clone().invert(&li).unwrap();
                    let diff = Integer::from(&r - &acc) % li.clone();
                    let t = (diff * inv) % li.clone();
                    let t = if t < 0 { t + li.clone() } else { t };
                    acc += modulus.clone() * t;
                    modulus *= li;
                }
                if acc.clone().is_perfect_square() { *sq += 1; eprintln!("  PERFECT SQUARE: tail {:?}", sel); }
            }
            return;
        }
        if i >= pool.len() { return; }
        if best[i][k] < 0.0 || m + best[i][k] <= need { return; }
        sel.push(pool[i]);
        rec(i+1, k-1, m + 1.0/pool[i] as f64, pool, best, need, forced, nf, sel, cnt, sq);
        sel.pop();
        rec(i+1, k, m, pool, best, need, forced, nf, sel, cnt, sq);
    }
    let t0 = std::time::Instant::now();
    rec(0, 20, 0.0, &pool, &best, need, &forced, &nforced, &mut sel, &mut cnt, &mut sq);
    println!("supports tested {}   D2 a perfect square: {}   ({:.1}s)", cnt, sq, t0.elapsed().as_secs_f64());
}
