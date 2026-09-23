// q_sieve.rs -- the balanced regime of the level-60 single-tail split sieve, decided over the tail prime q.
//
// For a family S u {q} and a split a = q*alpha, b = beta, alpha*beta = D = prod S, the cycle equations give
// A q + D = (q alpha + beta)^2 and B q + D = (q alpha - beta)^2 with A, B = D' +- 2D (prop:tailbound). Reducing
// q alpha^2 == D/p or q (alpha/p)^2 == D/p (mod p) at each odd p in S gives (q|p) = ((D/p)|p): 58 quadratic-character
// conditions on q alone. With rho = alpha^2/D, q = (Sigma - sigma(T))/rho, so rho > 2^-40 forces q < Sigma * 2^40.
// This program lists every q in [1, qmax] with q odd, gcd(q, D) = 1 and all 58 characters matching; the split sieve's
// Stage A (split_mitm.rs) covers rho <= 2^-40. Survivors are candidates only: each is decided afterwards by the exact
// square test on A q + D and B q + D.
//
// Build: rustc -O -C target-cpu=native -o q_sieve q_sieve.rs
// Run:   ./q_sieve bases.txt <threads> <log2 inverse tau>        (40 matches Stage A)
//        ./q_sieve --control bases.txt       (positive control: planted target signs from a chosen q0 must return q0)
// Checkpoint: done.txt and results.txt, atomic (tmp + rename) every 30 s and at exit; resumes from them.
use std::collections::HashSet;
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Instant;

fn pw(mut b: u64, mut e: u64, m: u64) -> u64 { let mut r = 1 % m; b %= m; while e > 0 { if e & 1 == 1 { r = r * b % m; } b = b * b % m; e >>= 1; } r }
fn leg(a: u64, p: u64) -> i32 { let a = a % p; if a == 0 { 0 } else if pw(a, (p - 1) / 2, p) == 1 { 1 } else { -1 } }

struct Base { idx: usize, s: Vec<u64> }
struct Shared { done: Vec<usize>, results: Vec<String>, cand: u64, surv: u64 }

/// Sieve one base. plant = Some(q0) replaces the targets by (q0|p) (positive control).
fn sieve(s: &[u64], qmax: u64, plant: Option<u64>) -> (u64, Vec<u64>) {
    let odd: Vec<u64> = s.iter().cloned().filter(|&p| p != 2).collect();
    let tgt: Vec<i32> = odd.iter().map(|&p| {
        let t = match plant { Some(q0) => leg(q0, p), None => { let dp = s.iter().filter(|&&r| r != p).fold(1u64, |acc, &r| acc * (r % p) % p); leg(dp, p) } };
        assert!(t != 0); t }).collect();
    let ok: Vec<Vec<bool>> = odd.iter().zip(&tgt).map(|(&p, &t)| (0..p).map(|x| leg(x, p) == t).collect()).collect();
    let mut idx: Vec<usize> = (0..odd.len()).collect(); idx.sort_by_key(|&i| odd[i]);
    let k = 7.min(idx.len()); let wh = &idx[..k]; let rest = &idx[k..];
    let w: u64 = 2 * wh.iter().map(|&i| odd[i]).product::<u64>();
    let res: Vec<u64> = (1..w).step_by(2).filter(|&r| wh.iter().all(|&i| ok[i][(r % odd[i]) as usize])).collect();
    let (mut cand, mut surv) = (0u64, Vec::new());
    for &r in &res { let mut q = r; while q <= qmax { cand += 1;
        if rest.iter().all(|&i| ok[i][(q % odd[i]) as usize]) { surv.push(q); }
        q += w; } }
    surv.sort_unstable(); (cand, surv)
}

fn qmax_for(s: &[u64], tl: u32) -> u64 {
    // Sigma * 2^tl, rounded up with a generous margin (f64 relative error ~1e-15 on ~2e12)
    let sig: f64 = s.iter().map(|&p| 1.0 / p as f64).sum();
    (sig * (2f64).powi(tl as i32)).ceil() as u64 + 1_000_000
}

fn read_bases(path: &str) -> Vec<Base> {
    let mut v = Vec::new();
    for line in std::io::BufReader::new(std::fs::File::open(path).unwrap()).lines() {
        let x: Vec<i64> = line.unwrap().split_whitespace().map(|t| t.parse().unwrap()).collect();
        if x[1] == -1 || x[2] == -1 { continue; }
        v.push(Base { idx: x[0] as usize, s: x[4..].iter().map(|&y| y as u64).collect() });
    }
    v
}

fn checkpoint(sh: &Mutex<Shared>) {
    let g = sh.lock().unwrap();
    let w = |name: &str, lines: &[String]| {
        let tmp = format!("{}.tmp", name);
        let attempt = (|| -> std::io::Result<()> { let mut f = std::fs::File::create(&tmp)?; for l in lines { writeln!(f, "{}", l)?; } f.sync_all()?; std::fs::rename(&tmp, name) })();
        if let Err(e) = attempt { eprintln!("  WARNING: checkpoint to {} failed ({}); run continues, will retry", name, e); let _ = std::fs::remove_file(&tmp); }
    };
    w("done.txt", &g.done.iter().map(|d| d.to_string()).collect::<Vec<_>>());
    w("results.txt", &g.results);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args[1] == "--control" {
        let b = &read_bases(&args[2])[0];
        for &q0 in &[1_000_003u64, 987_654_321_001, 1_150_000_000_039] {
            if b.s.iter().any(|&p| q0 % p == 0) { continue; }
            let t0 = Instant::now(); let (c, sv) = sieve(&b.s, 1_200_000_000_000, Some(q0));
            println!("control base={} q0={} candidates={} survivors={:?} found={} ({:.0}s)", b.idx, q0, c, sv, sv.contains(&q0), t0.elapsed().as_secs_f64());
            assert!(sv.contains(&q0), "positive control failed");
        }
        println!("CONTROL PASSED"); return;
    }
    let bases = read_bases(&args[1]); let nthreads: usize = args[2].parse().unwrap(); let tl: u32 = args[3].parse().unwrap();
    let mut done_set: HashSet<usize> = HashSet::new(); let mut prev = Vec::new();
    if let Ok(f) = std::fs::File::open("done.txt") { for l in std::io::BufReader::new(f).lines().flatten() { if let Ok(i) = l.trim().parse() { done_set.insert(i); } } }
    if let Ok(f) = std::fs::File::open("results.txt") { for l in std::io::BufReader::new(f).lines().flatten() { prev.push(l); } }
    let todo: Vec<&Base> = bases.iter().filter(|b| !done_set.contains(&b.idx)).collect();
    let total = todo.len();
    eprintln!("families {}  already done {}  to do {}  tau=2^-{}  threads {}", bases.len(), done_set.len(), total, tl, nthreads);
    let sh = Mutex::new(Shared { done: done_set.iter().cloned().collect(), results: prev, cand: 0, surv: 0 });
    let next = AtomicUsize::new(0); let finished = AtomicUsize::new(0); let t0 = Instant::now();
    let stop = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|sc| {
        sc.spawn(|| { loop { for _ in 0..30 { std::thread::sleep(std::time::Duration::from_secs(1)); if finished.load(Ordering::Relaxed) >= total || stop.load(Ordering::Relaxed) { return; } } checkpoint(&sh); } });
        for _ in 0..nthreads { sc.spawn(|| { loop {
            let i = next.fetch_add(1, Ordering::Relaxed); if i >= total { break; }
            let b = todo[i]; let qmax = qmax_for(&b.s, tl); let tb = Instant::now();
            let (c, sv) = sieve(&b.s, qmax, None);
            let line = format!("DONE base={} qmax={} candidates={} survivors={} list={:?} secs={:.1}", b.idx, qmax, c, sv.len(), sv, tb.elapsed().as_secs_f64());
            { let mut g = sh.lock().unwrap(); g.results.push(line); g.done.push(b.idx); g.cand += c; g.surv += sv.len() as u64; }
            let f = finished.fetch_add(1, Ordering::Relaxed) + 1;
            if f % 10 == 0 || f == total { let el = t0.elapsed().as_secs_f64(); let g = sh.lock().unwrap();
                eprintln!("  done {}/{}  {:.4} bases/s  elapsed {:.0}s  ETA {:.0}s  candidates {}  survivors {}", f, total, f as f64 / el, el, el * (total - f) as f64 / f as f64, g.cand, g.surv); }
        } }); }
    });
    stop.store(true, Ordering::Relaxed); checkpoint(&sh);
    let g = sh.lock().unwrap();
    println!("COMPLETE: families {}  candidates {}  survivors {}  ({:.0}s)", total, g.cand, g.surv, t0.elapsed().as_secs_f64());
}
