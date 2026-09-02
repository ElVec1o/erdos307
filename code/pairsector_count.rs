// pairsector_count.rs -- the level-60 pair sector, enumerated exactly.
// Build: rustc -O -o pairsector_count pairsector_count.rs   Run: ./pairsector_count [prune-margin]
//
// A level-60 support U (60 primes, T(U) > 2) is covered by the one-new-prime campaign iff
// T(U \ {max U}) > 2, since the campaign's bases are the 59-prime sets of prop:close59.  The
// complement -- the pair sector -- is U = R u {m} with |R| = 59, m = max U, and T(R) <= 2 < T(R) + 1/m.
// By the mass ladder (prop:massladder) at k = 60, every element of R is a prime < 793.67*2 = 1587.4,
// so this is a finite search: 59-subsets of the 250 primes below 1588 with T(R) in (2 - 1/max(R), 2].
// Result: 18,234,653 bases, largest max(R) = 1583.  Corroborated by an independent binned counting DP.
// Each base is an arity-one tail family in m, so the q-independent reciprocity certificate applies to
// it -- prop:pairlocal forbids congruence kills only for the family with BOTH new primes free.





#[derive(Clone, Copy)] struct DD { hi: f64, lo: f64 }
fn two_sum(a: f64, b: f64) -> (f64, f64) { let s = a + b; let bb = s - a; (s, (a - (s - bb)) + (b - bb)) }
fn dd_add(x: DD, y: DD) -> DD { let (s, e) = two_sum(x.hi, y.hi); let e = e + x.lo + y.lo; let (h, l) = two_sum(s, e); DD { hi: h, lo: l } }
fn dd_recip(p: u64) -> DD { let hi = 1.0 / p as f64; let lo = (-hi).mul_add(p as f64, 1.0) / p as f64; DD { hi, lo } }
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i * i <= n { if n % i == 0 { return false; } i += 1; } true }
struct C { margin: f64, pool: Vec<u64>, inv: Vec<f64>, dd: Vec<DD>, pre: Vec<Vec<f64>>, suf: Vec<Vec<f64>>, n: usize,
           count: u64, leaves: u64, mmax: u64 }
fn dfs(c: &mut C, i: usize, need: usize, mass: f64, sig: DD, maxidx: usize) {
    if need == 0 {
        c.leaves += 1;
        let m = c.pool[maxidx];
        // T(R) in (2 - 1/m, 2]
        if mass <= 2.0 + c.margin && mass > 2.0 - 1.0 / m as f64 - c.margin {
            let t = sig.hi + sig.lo;
            if t <= 2.0 && t > 2.0 - 1.0 / m as f64 { c.count += 1; if m > c.mmax { c.mmax = m; } }
        }
        return;
    }
    if i + need > c.n { return; }
    // The requirement T(R) > 2 - 1/max(R) is weakest when max(R) is smallest, i.e. the 59th prime
    // (pool[58]); pruning against any larger threshold would discard genuine sets.
    if mass + c.pre[i][need] <= 2.0 - 1.0 / c.pool[58] as f64 - c.margin { return; }
    if mass + c.suf[i][need] > 2.0 + c.margin { return; }                                   // even the worst is too big
    let (iv, dv) = (c.inv[i], c.dd[i]);
    dfs(c, i + 1, need - 1, mass + iv, dd_add(sig, dv), i);
    dfs(c, i + 1, need, mass, sig, maxidx);
}
fn main() {
    let margin: f64 = std::env::args().nth(1).map(|x| x.parse().unwrap()).unwrap_or(1e-12);
    let pool: Vec<u64> = (2..1588u64).filter(|&p| is_prime(p)).collect();
    let n = pool.len();
    let inv: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    let dd: Vec<DD> = pool.iter().map(|&p| dd_recip(p)).collect();
    let mut pre = vec![vec![0.0; 60]; n + 1]; let mut suf = vec![vec![0.0; 60]; n + 1];
    for i in 0..n { for k in 1..=59 { if i + k <= n { pre[i][k] = inv[i..i + k].iter().sum(); } else { pre[i][k] = f64::NEG_INFINITY; }
        if k <= n - i { suf[i][k] = inv[n - k..].iter().sum(); } else { suf[i][k] = f64::INFINITY; } } }
    let mut c = C { margin, pool, inv, dd, pre, suf, n, count: 0, leaves: 0, mmax: 0 };
    let t0 = std::time::Instant::now();
    dfs(&mut c, 0, 59, 0.0, DD { hi: 0.0, lo: 0.0 }, 0);
    println!("pool {} primes (<1588)", c.n);
    println!("EXACT level-60 pair-sector bases R: {}   (leaves reached {}, largest max(R) {}, {:.0}s)",
        c.count, c.leaves, c.mmax, t0.elapsed().as_secs_f64());
}
