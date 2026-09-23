// q_sieve2.rs -- independent second implementation of q_sieve.rs, for cross-checking.
// Differences by design: targets ((D/p)|p) = prod_{r != p} (r|p) from a binary Jacobi symbol (reciprocity), not Euler's
// criterion on a product mod p; the wheel is {2,3,5,11,13,17,19,23} (7 left to the tables); the remaining primes are
// tested from bitsets, largest first; qmax = ceil(Sigma * 2^tl) + 1000 computed in u128 fixed point.
// Run:   ./q_sieve2 bases.txt <threads> <tl>            (checkpointed: done.txt / results.txt, atomic, resumable)
//        ./q_sieve2 --plant bases.txt <q0> <qmax>        (targets from q0; prints the survivor list, for comparison)
use std::collections::HashSet;
use std::io::{BufRead, Write};
use std::sync::{Mutex, atomic::{AtomicUsize, AtomicBool, Ordering}};
use std::time::Instant;

fn jacobi(mut a: u64, mut n: u64) -> i32 {
    // n odd positive
    a %= n; let mut t = 1i32;
    while a != 0 {
        while a % 2 == 0 { a /= 2; let r = n % 8; if r == 3 || r == 5 { t = -t; } }
        std::mem::swap(&mut a, &mut n);
        if a % 4 == 3 && n % 4 == 3 { t = -t; }
        a %= n;
    }
    if n == 1 { t } else { 0 }
}

struct Bs { p: u64, bits: Vec<u64> }
fn run(s: &[u64], qmax: u64, plant: Option<u64>) -> (u64, Vec<u64>) {
    let odd: Vec<u64> = s.iter().cloned().filter(|&p| p != 2).collect();
    let target = |p: u64| -> i32 { match plant {
        Some(q0) => jacobi(q0, p),
        None => s.iter().filter(|&&r| r != p).map(|&r| jacobi(r, p)).product() } };
    let wheel_ps: Vec<u64> = vec![3, 5, 11, 13, 17, 19, 23];
    for p in &wheel_ps { assert!(odd.contains(p)); }
    let mut tabs: Vec<Bs> = Vec::new();
    let mut wt: Vec<(u64, i32)> = Vec::new();
    for &p in &odd { let t = target(p); assert!(t != 0);
        if wheel_ps.contains(&p) { wt.push((p, t)); continue; }
        let mut bits = vec![0u64; (p as usize + 63) / 64];
        for x in 1..p { if jacobi(x, p) == t { bits[(x / 64) as usize] |= 1 << (x % 64); } }
        tabs.push(Bs { p, bits }); }
    tabs.sort_by(|a, b| b.p.cmp(&a.p));
    let w: u64 = 2 * wheel_ps.iter().product::<u64>();
    let res: Vec<u64> = (1..w).step_by(2).filter(|&r| wt.iter().all(|&(p, t)| jacobi(r % p, p) == t)).collect();
    let (mut cand, mut out) = (0u64, Vec::new());
    for &r in &res { let mut q = r; while q <= qmax { cand += 1;
        let mut ok = true;
        for b in &tabs { let x = q % b.p; if b.bits[(x / 64) as usize] >> (x % 64) & 1 == 0 { ok = false; break; } }
        if ok { out.push(q); } q += w; } }
    out.sort_unstable(); (cand, out)
}
fn qmax_of(s: &[u64], tl: u32) -> u64 {
    let sig: u128 = s.iter().map(|&p| (1u128 << 100) / p as u128).sum::<u128>() + s.len() as u128; // upper bound on Sigma * 2^100
    ((sig >> (100 - tl)) + 1 + 1000) as u64
}
fn bases(path: &str) -> Vec<(usize, Vec<u64>)> {
    std::io::BufReader::new(std::fs::File::open(path).unwrap()).lines().filter_map(|l| {
        let x: Vec<i64> = l.unwrap().split_whitespace().map(|t| t.parse().unwrap()).collect();
        if x[1] == -1 || x[2] == -1 { None } else { Some((x[0] as usize, x[4..].iter().map(|&y| y as u64).collect())) } }).collect()
}
fn save(done: &[usize], res: &[String]) {
    for (name, lines) in [("done.txt", done.iter().map(|d| d.to_string()).collect::<Vec<_>>()), ("results.txt", res.to_vec())] {
        let tmp = format!("{}.tmp", name);
        let r = (|| -> std::io::Result<()> { let mut f = std::fs::File::create(&tmp)?; for l in &lines { writeln!(f, "{}", l)?; } f.sync_all()?; std::fs::rename(&tmp, name) })();
        if let Err(e) = r { eprintln!("  WARNING: checkpoint {} failed ({}), will retry", name, e); let _ = std::fs::remove_file(&tmp); }
    }
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a[1] == "--plant" {
        let b = &bases(&a[2])[0]; let q0: u64 = a[3].parse().unwrap(); let qmax: u64 = a[4].parse().unwrap();
        let (c, v) = run(&b.1, qmax, Some(q0));
        println!("plant base={} q0={} qmax={} candidates={} survivors={} list={:?}", b.0, q0, qmax, c, v.len(), v); return;
    }
    let all = bases(&a[1]); let nt: usize = a[2].parse().unwrap(); let tl: u32 = a[3].parse().unwrap();
    let mut done: HashSet<usize> = HashSet::new(); let mut prev = Vec::new();
    if let Ok(f) = std::fs::File::open("done.txt") { for l in std::io::BufReader::new(f).lines().flatten() { if let Ok(i) = l.trim().parse() { done.insert(i); } } }
    if let Ok(f) = std::fs::File::open("results.txt") { for l in std::io::BufReader::new(f).lines().flatten() { prev.push(l); } }
    let todo: Vec<&(usize, Vec<u64>)> = all.iter().filter(|b| !done.contains(&b.0)).collect(); let total = todo.len();
    eprintln!("bases {} done {} todo {} tl {} threads {}", all.len(), done.len(), total, tl, nt);
    let sh = Mutex::new((done.into_iter().collect::<Vec<_>>(), prev, 0u64));
    let (next, fin, stop, t0) = (AtomicUsize::new(0), AtomicUsize::new(0), AtomicBool::new(false), Instant::now());
    std::thread::scope(|sc| {
        sc.spawn(|| loop { for _ in 0..30 { std::thread::sleep(std::time::Duration::from_secs(1)); if fin.load(Ordering::Relaxed) >= total || stop.load(Ordering::Relaxed) { return; } } let g = sh.lock().unwrap(); save(&g.0, &g.1); });
        for _ in 0..nt { sc.spawn(|| loop {
            let i = next.fetch_add(1, Ordering::Relaxed); if i >= total { break; }
            let b = todo[i]; let qm = qmax_of(&b.1, tl); let tb = Instant::now(); let (c, v) = run(&b.1, qm, None);
            { let mut g = sh.lock().unwrap(); g.0.push(b.0); g.1.push(format!("DONE base={} qmax={} candidates={} survivors={} list={:?} secs={:.1}", b.0, qm, c, v.len(), v, tb.elapsed().as_secs_f64())); g.2 += v.len() as u64; }
            let f = fin.fetch_add(1, Ordering::Relaxed) + 1; let el = t0.elapsed().as_secs_f64();
            if f % 10 == 0 || f == total { eprintln!("  done {}/{}  elapsed {:.0}s  ETA {:.0}s  survivors {}", f, total, el, el * (total - f) as f64 / f as f64, sh.lock().unwrap().2); }
        }); }
    });
    stop.store(true, Ordering::Relaxed); let g = sh.lock().unwrap(); save(&g.0, &g.1);
    println!("COMPLETE: bases {} survivors {} ({:.0}s)", total, g.2, t0.elapsed().as_secs_f64());
}
