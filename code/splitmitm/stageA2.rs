// stageA2.rs -- second, independent implementation of Stage A (rho <= 2^-40) of the level-60 single-tail sieve.
// Independent of code/splitmitm/split_mitm.rs: different split (interleaved halves), different join (bucketed hash
// join on a fixed-point grid instead of Schroeppel-Shamir), different exact test (the identity mod two 31-bit primes
// via byte-chunk tables, with the |T| odd restriction), no bignum.
//
// For a base S (59 primes): every T with X = sigma(T) in the lower window [x_-(tau), x_-(0)] is enumerated. A candidate
// T is tested as alpha-set A = T if |T| odd, else A = S\T (cor:splitexact: |alpha| is odd), against the identity
//        c1 * c2 == alpha * (beta - alpha)        (c1 = csum A, c2 = csum S\A, alpha = prod A, beta = prod S\A)
// which every cycle with alpha-set A satisfies. A candidate failing the identity modulo ANY prime is not a cycle, so a
// run with zero "eq" lines (identity holds mod both moduli) proves no low-rho cycle on that base. Window margins only
// need to over-estimate; fixed-point 1/p = floor(2^62/p) has error < 1 per term (lo is widened by 64).
//
// Usage:  stageA2 <bases.txt> <outdir> [maxthreads=2] [log2 inverse tau = 40]
//         stageA2 --plant <bases.txt> <line idx> <seed>     (plant a random T0 inside a production-width window)
// Stop and go: progress is the append-only <outdir>/done.txt (one line per finished base); kill -STOP/-CONT work too.
// The number of ACTIVE workers is re-read from <outdir>/threads before every base (default = maxthreads).
use std::collections::HashSet;
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

const NB: usize = 59;
const SCALE: f64 = 4611686018427387904.0; // 2^62
const M1: u64 = 2147483629; // primes below 2^31
const M2: u64 = 2147483587;

fn merge_add(list: &[(u64, u64)], e: u64, bit: u64) -> Vec<(u64, u64)> {
    let n = list.len();
    let mut out = Vec::with_capacity(2 * n);
    let (mut i, mut j) = (0usize, 0usize);
    while i < n || j < n {
        if j >= n || (i < n && list[i].0 <= list[j].0 + e) { out.push(list[i]); i += 1; }
        else { out.push((list[j].0 + e, list[j].1 | bit)); j += 1; }
    }
    out
}
fn sums(rec: &[u64], pos: &[usize]) -> Vec<(u64, u64)> {
    let mut l = vec![(0u64, 0u64)];
    for &p in pos { l = merge_add(&l, rec[p], 1u64 << p); }
    l
}
/// entries (u+v, mu|mv) of sa x sb with a <= u+v < b (b exclusive), via two descending pointers
fn range_pairs(sa: &[(u64, u64)], sb: &[(u64, u64)], a: u64, b: u64, out: &mut Vec<(u64, u64)>) {
    let mut ilo = sb.len(); // first index with v >= a - u   (descends as u grows)
    let mut ihi = sb.len(); // first index with v >= b - u
    for &(u, mu) in sa {
        let need_lo = a.saturating_sub(u);
        let need_hi = b.saturating_sub(u);
        while ilo > 0 && sb[ilo - 1].0 >= need_lo { ilo -= 1; }
        while ihi > 0 && sb[ihi - 1].0 >= need_hi { ihi -= 1; }
        for k in ilo..ihi { out.push((u + sb[k].0, mu | sb[k].1)); }
        if u >= b { break; }
    }
}

struct Tabs { t1: Vec<Vec<(u64, u64)>>, t2: Vec<Vec<(u64, u64)>> }
fn chunk_tables(p: &[u64], m: u64) -> Vec<Vec<(u64, u64)>> {
    let mut tabs = Vec::new();
    for c in 0..8 {
        let lo = c * 8; let hi = (lo + 8).min(NB);
        let mut t = vec![(1u64, 0u64); 256];
        for mask in 0..(1usize << (hi - lo)) {
            let mut a = 1u64; let mut cs = 0u64;
            for b in 0..(hi - lo) { if mask >> b & 1 == 1 {
                // adjoin prime p[lo+b]: (a,c) + {q} -> (a q, c q + a)
                let q = p[lo + b] % m; cs = (cs * q + a) % m; a = a * q % m; } }
            t[mask] = (a, cs);
        }
        tabs.push(t);
    }
    tabs
}
#[inline] fn compose(x: (u64, u64), y: (u64, u64), m: u64) -> (u64, u64) { (x.0 * y.0 % m, (x.1 * y.0 + x.0 * y.1) % m) }
#[inline] fn eval(t: &[Vec<(u64, u64)>], mask: u64, m: u64) -> (u64, u64) {
    let mut r = (1u64, 0u64);
    for c in 0..8 { r = compose(r, t[c][((mask >> (8 * c)) & 255) as usize], m); }
    r
}
/// identity c1*c2 == alpha*(beta-alpha) mod m for alpha-set `a` (mask), complement within 59 bits
#[inline] fn identity(t: &[Vec<(u64, u64)>], a: u64, m: u64) -> bool {
    let full = (1u64 << NB) - 1;
    let (al, c1) = eval(t, a, m);
    let (be, c2) = eval(t, full & !a, m);
    c1 * c2 % m == al * ((be + m - al) % m) % m
}

struct Res { cand: u64, odd_tests: u64, eq: Vec<u64>, planted_found: bool }

fn run_base(s: &[u64], lt: i32, plant: Option<u64>) -> (Res, f64, u64, u64) {
    let rec: Vec<u64> = s.iter().map(|&p| (1u64 << 62) / p).collect();
    let sig: f64 = s.iter().map(|&p| 1.0 / p as f64).sum();
    let tau = 2f64.powi(-lt);
    let xm0 = (sig - (sig * sig - 4.0).sqrt()) / 2.0;
    let xmt = (sig - (sig * sig - 4.0 * (1.0 - tau)).sqrt()) / 2.0;
    let mut lo = (((xmt - 1e-12) * SCALE).floor() as u64).saturating_sub(64);
    let mut hi = ((xm0 + 1e-12) * SCALE).ceil() as u64;
    if let Some(m0) = plant {
        let s0: u64 = (0..NB).filter(|&i| m0 >> i & 1 == 1).map(|i| rec[i]).sum();
        lo = s0.saturating_sub(1 << 25); hi = s0 + (1 << 25);
    }
    let left: Vec<usize> = (0..NB).filter(|i| i % 2 == 0).collect();
    let right: Vec<usize> = (0..NB).filter(|i| i % 2 == 1).collect();
    let (la, lb): (Vec<usize>, Vec<usize>) = (left.iter().cloned().step_by(2).collect(), left.iter().cloned().skip(1).step_by(2).collect());
    let (ra, rb): (Vec<usize>, Vec<usize>) = (right.iter().cloned().step_by(2).collect(), right.iter().cloned().skip(1).step_by(2).collect());
    let (sla, slb, sra, srb) = (sums(&rec, &la), sums(&rec, &lb), sums(&rec, &ra), sums(&rec, &rb));
    let sigl: u64 = left.iter().map(|&i| rec[i]).sum();
    let nbuck: u64 = 2048;
    let w = sigl / nbuck + 1;
    let kbits = 64 - (hi - lo + 1).leading_zeros(); // 2^kbits > window width
    let tabs = Tabs { t1: chunk_tables(s, M1), t2: chunk_tables(s, M2) };
    let mut res = Res { cand: 0, odd_tests: 0, eq: vec![], planted_found: false };
    let full = (1u64 << NB) - 1;
    let mut lent: Vec<(u64, u64)> = Vec::new();
    let mut rent: Vec<(u64, u64)> = Vec::new();
    let mut head: Vec<u32> = Vec::new();
    let mut next: Vec<u32> = Vec::new();
    for j in 0..nbuck {
        let a = j * w; let b = a + w; // left sums in [a,b)
        lent.clear(); range_pairs(&sla, &slb, a, b, &mut lent);
        if lent.is_empty() { continue; }
        // right sums r with some l in [a,b) giving l+r in [lo,hi]:  r in [lo-(b-1), hi-a]
        let rlo = lo.saturating_sub(b - 1); if hi < a { continue; }
        let rhi = hi - a;
        rent.clear(); range_pairs(&sra, &srb, rlo, rhi + 1, &mut rent);
        if rent.is_empty() { continue; }
        let hs = (2 * lent.len()).next_power_of_two().max(16);
        head.clear(); head.resize(hs, u32::MAX); next.clear(); next.resize(lent.len(), u32::MAX);
        let hmask = hs - 1;
        let hf = |cell: u64| ((cell.wrapping_mul(0x9E3779B97F4A7C15)) >> 20) as usize & hmask;
        for (i, &(l, _)) in lent.iter().enumerate() { let h = hf(l >> kbits); next[i] = head[h]; head[h] = i as u32; }
        for &(r, mr) in &rent {
            let c1 = lo.saturating_sub(r) >> kbits; let c2 = hi.saturating_sub(r) >> kbits;
            for cell in c1..=c2 {
                let mut idx = head[hf(cell)];
                while idx != u32::MAX {
                    let (l, ml) = lent[idx as usize];
                    if (l >> kbits) == cell {
                        let t = l + r;
                        if t >= lo && t <= hi {
                            let tm = ml | mr; res.cand += 1;
                            if plant == Some(tm) { res.planted_found = true; }
                            let a_set = if tm.count_ones() % 2 == 1 { tm } else { full & !tm };
                            res.odd_tests += 1;
                            if identity(&tabs.t1, a_set, M1) && identity(&tabs.t2, a_set, M2) { res.eq.push(a_set); }
                        }
                    }
                    idx = next[idx as usize];
                }
            }
        }
    }
    (res, sig, lo, hi)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() >= 2 && a[1] == "--plant" {
        let txt = std::fs::read_to_string(&a[2]).unwrap();
        let line = txt.lines().nth(a[3].parse().unwrap()).unwrap();
        let t: Vec<u64> = line.split_whitespace().map(|x| x.parse().unwrap()).collect();
        let s = &t[t.len() - NB..];
        let mut seed: u64 = a[4].parse::<u64>().unwrap() | 1;
        let mut found = 0; let trials = 3;
        for _ in 0..trials {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let mask = (seed >> 5) & ((1u64 << NB) - 1);
            let t0 = Instant::now();
            let (r, _, lo, hi) = run_base(s, 40, Some(mask));
            println!("plant mask={:#x} |T|={} found={} cand={} width={} secs={:.1}", mask, mask.count_ones(), r.planted_found, r.cand, hi - lo, t0.elapsed().as_secs_f64());
            if r.planted_found { found += 1; }
        }
        println!("planted found {}/{}", found, trials);
        return;
    }
    let txt = std::fs::read_to_string(&a[1]).unwrap();
    let outdir = a[2].clone();
    let maxthreads: usize = a.get(3).and_then(|x| x.parse().ok()).unwrap_or(2);
    let lt: i32 = a.get(4).and_then(|x| x.parse().ok()).unwrap_or(40);
    std::fs::create_dir_all(&outdir).unwrap();
    let donep = format!("{}/done.txt", outdir);
    let mut done: HashSet<u64> = HashSet::new();
    if let Ok(d) = std::fs::read_to_string(&donep) { for l in d.lines() { if let Some(x) = l.split_whitespace().next() { if let Ok(v) = x.parse() { done.insert(v); } } } }
    let mut todo: Vec<(u64, Vec<u64>)> = Vec::new();
    for line in txt.lines() {
        let t: Vec<u64> = line.split_whitespace().map(|x| x.parse().unwrap()).collect();
        if t.is_empty() || done.contains(&t[0]) { continue; }
        todo.push((t[0], t[t.len() - NB..].to_vec()));
    }
    eprintln!("stageA2: {} bases to do ({} already done), up to {} threads", todo.len(), done.len(), maxthreads);
    let todo = Arc::new(todo);
    let next = Arc::new(AtomicUsize::new(0));
    let out = Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&donep).unwrap()));
    let counter = Arc::new(AtomicUsize::new(0));
    let t_start = Instant::now();
    let mut hs = Vec::new();
    for wid in 0..maxthreads {
        let (todo, next, out, counter, outdir) = (todo.clone(), next.clone(), out.clone(), counter.clone(), outdir.clone());
        hs.push(std::thread::spawn(move || {
            loop {
                let allowed: usize = std::fs::read_to_string(format!("{}/threads", outdir)).ok().and_then(|x| x.trim().parse().ok()).unwrap_or(2);
                if wid >= allowed { if next.load(Ordering::SeqCst) >= todo.len() { break; } std::thread::sleep(Duration::from_secs(20)); continue; }
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= todo.len() { break; }
                let (id, s) = &todo[i];
                let t0 = Instant::now();
                let (r, sig, lo, hi) = run_base(s, lt, None);
                let secs = t0.elapsed().as_secs_f64();
                let mut o = out.lock().unwrap();
                writeln!(o, "{} sigma={:.9} window=[{},{}] cand={} eq={} secs={:.1}{}", id, sig, lo, hi, r.cand, r.eq.len(), secs,
                    if r.eq.is_empty() { String::new() } else { format!(" EQMASKS={:?}", r.eq) }).unwrap();
                o.flush().unwrap();
                let c = counter.fetch_add(1, Ordering::SeqCst) + 1;
                if c % 10 == 0 { eprintln!("done {}/{} elapsed {:.0}s ({:.1}s per base wall)", c, todo.len(), t_start.elapsed().as_secs_f64(), t_start.elapsed().as_secs_f64() / c as f64); }
            }
        }));
    }
    for h in hs { h.join().unwrap(); }
    eprintln!("stageA2: finished");
}
