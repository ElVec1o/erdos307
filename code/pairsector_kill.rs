// pairsector_kill.rs -- the reciprocity certificate over level-60 bases.
// Build: rustc -O -o pairsector_kill pairsector_kill.rs --extern rug=<rug rlib>   (uses rug/GMP for Jacobi)
// Run: ./pairsector_kill <campaign|pair> <threads>
// REGRESSION: mode "campaign" reproduces the published level-60 figures exactly --
//   49,961 bases, 31,219 killed by the Jacobi symbol, 18,742 survivors (prop:close59, rem:campaign).
// Mode "pair": 18,234,653 bases, 10,457,149 killed (57.3%).  Survivors written as 32-byte bitmasks.
// Reciprocity certificate over level-60 bases.
//   mode "campaign": the one-new-prime bases of prop:close59 -- 59 primes with T(R) > 2.
//                    Expected (paper): 49,961 bases, 31,219 killed by the Jacobi symbol (62.5%).
//   mode "pair":     the pair sector -- 59 primes, all < 1588, with T(R) <= 2 < T(R) + 1/max(R).
//                    Expected: 18,234,653 bases.
// Per base R: D = prod R, N = D' carried incrementally (D_new = D*p, N_new = N*p + D),
// A = N + 2D.  Kill iff Jacobi(D | A) = -1 (then some l | A of odd multiplicity has (D|l) = -1).
use rug::Integer;
use std::io::Write;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Mutex;
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i * i <= n { if n % i == 0 { return false; } i += 1; } true }
struct Ctx { pool: Vec<u64>, inv: Vec<f64>, pre: Vec<Vec<f64>>, suf: Vec<Vec<f64>>, n: usize, pair: bool,
    lo_thresh: f64, bases: AtomicU64, killed: AtomicU64, surv: Mutex<std::fs::File> }
fn dfs(c: &Ctx, i: usize, need: usize, mass: f64, d: &Integer, nn: &Integer, sel: &mut Vec<usize>) {
    if need == 0 {
        let m = c.pool[*sel.last().unwrap()];
        let ok = if c.pair { mass <= 2.0 + 1e-12 && mass > 2.0 - 1.0 / m as f64 - 1e-12 } else { mass > 2.0 };
        if !ok { return; }
        c.bases.fetch_add(1, Ordering::Relaxed);
        let a = Integer::from(nn + Integer::from(2) * d);
        if d.jacobi(&a) == -1 { c.killed.fetch_add(1, Ordering::Relaxed); }
        else { let mut w = [0u8; 32]; for &s in sel.iter() { w[s / 8] |= 1 << (s % 8); }
               c.surv.lock().unwrap().write_all(&w).unwrap(); }
        return;
    }
    if i + need > c.n { return; }
    if mass + c.pre[i][need] <= c.lo_thresh { return; }
    if c.pair && mass + c.suf[i][need] > 2.0 + 1e-12 { return; }
    sel.push(i);
    dfs(c, i + 1, need - 1, mass + c.inv[i], &(Integer::from(d * c.pool[i])), &(Integer::from(nn * c.pool[i]) + d), sel);
    sel.pop();
    dfs(c, i + 1, need, mass, d, nn, sel);
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let pair = a[1] == "pair"; let nthreads: usize = a[2].parse().unwrap();
    // campaign bases may use primes beyond 1588; bound them by the mass ladder at k=59 (u_59 <= 793.67)
    let cap: u64 = if pair { 1588 } else { 800 };
    let pool: Vec<u64> = (2..cap).filter(|&p| is_prime(p)).collect();
    let n = pool.len();
    let inv: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    let mut pre = vec![vec![0.0; 60]; n + 1]; let mut suf = vec![vec![0.0; 60]; n + 1];
    for i in 0..n { for k in 1..=59 {
        pre[i][k] = if i + k <= n { inv[i..i + k].iter().sum() } else { f64::NEG_INFINITY };
        suf[i][k] = if k <= n - i { inv[n - k..].iter().sum() } else { f64::INFINITY }; } }
    let lo_thresh = if pair { 2.0 - 1.0 / pool[58] as f64 - 1e-12 } else { 2.0 };
    let fname = if pair { "pair_survivors.bin" } else { "campaign_survivors.bin" };
    let ctx = Ctx { pool, inv, pre, suf, n, pair, lo_thresh, bases: AtomicU64::new(0), killed: AtomicU64::new(0),
        surv: Mutex::new(std::fs::File::create(fname).unwrap()) };
    eprintln!("mode {} pool {} primes (<{}) threads {}", if pair {"pair"} else {"campaign"}, n, cap, nthreads);
    const D: usize = 14; let items = 1usize << D; let next = AtomicUsize::new(0);
    let t0 = std::time::Instant::now(); let done = AtomicUsize::new(0);
    std::thread::scope(|sc| { for _ in 0..nthreads { sc.spawn(|| {
        let mut sel = Vec::with_capacity(64); loop {
            let it = next.fetch_add(1, Ordering::Relaxed); if it >= items { break; }
            sel.clear(); let mut mass = 0.0; let mut d = Integer::from(1); let mut nn = Integer::from(0);
            let mut okc = true;
            for j in 0..D { if it >> j & 1 == 1 { sel.push(j); mass += ctx.inv[j];
                nn = Integer::from(&nn * ctx.pool[j]) + &d; d *= ctx.pool[j]; } }
            if sel.len() > 59 { okc = false; }
            if okc { dfs(&ctx, D, 59 - sel.len(), mass, &d, &nn, &mut sel); }
            let dc = done.fetch_add(1, Ordering::Relaxed) + 1;
            if dc % 512 == 0 { let el = t0.elapsed().as_secs_f64();
                eprintln!("  {}/{}  bases {}  killed {}  {:.0}s  ETA {:.0}s", dc, items,
                    ctx.bases.load(Ordering::Relaxed), ctx.killed.load(Ordering::Relaxed), el, el*(items-dc) as f64/dc as f64); }
        } }); } });
    let b = ctx.bases.load(Ordering::Relaxed); let k = ctx.killed.load(Ordering::Relaxed);
    println!("bases {}  killed {}  survivors {}  ({:.1}%)  {:.0}s", b, k, b - k, 100.0 * k as f64 / b as f64, t0.elapsed().as_secs_f64());
}
