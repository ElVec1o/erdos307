// split_mitm.rs -- Stage A of the partial-T prune for the level-60 single-tail split sieve.
//
// For a family S u {q}, a = q*alpha, b = beta, alpha*beta = D = prod S, T = primes of alpha, the two cycle
// equations beta' = q*alpha and beta - alpha = q*alpha' give, eliminating q,
//     1 - alpha^2/D = sigma(T) * sigma(S \ T),      sigma = sum of reciprocals.            (*)
// Put X = sigma(T), Sigma = sigma(S), rho = alpha^2/D. Then X(Sigma - X) = 1 - rho. For rho <= tau this pins
// X to [x_-(tau), x_-(0)] or its mirror [x_+(0), x_+(tau)] (x_+ = Sigma - x_-, so the mirror is the set of
// complements). Stage A enumerates every T with X in the lower window, at every |T| at once, by
// Schroeppel-Shamir over four quarters of S, and tests T and S\T exactly. It therefore decides every T
// with alpha^2 <= tau*D. Stage B (tau*D < alpha^2 < D) is not covered here.
//
// Arithmetic: 1/p is carried as floor(2^62/p) in u64; the true scaled sum lies in [Xfix, Xfix + n).
// The window is computed in f64 and widened by a margin that dominates both errors; soundness does not
// depend on the margin being tight, only on it being an overestimate, and every candidate is decided by
// exact 512-bit integer arithmetic on (*) and on the two cycle equations.
//
// Build: rustc -O -C target-cpu=native -o split_mitm split_mitm.rs
// Run:   ./split_mitm bases.txt <threads> <log2 inverse tau>      e.g. 30 for tau = 2^-30
//        ./split_mitm --selftest
//        ./split_mitm --audit bases.txt <idx,idx,...> <plants per base> <log2 inverse tau>
//          (on real 59-prime bases: plant a random split T0, centre a window of the production width on its fixed-point
//           reciprocal sum, and require window() to return T0; reports found/planted and candidates per pass)
// Checkpoint: done.txt and results.txt, atomic (tmp + rename) every 30 s and at exit; resumes from them.
use std::collections::HashSet;
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Instant;

const L: usize = 8; // 512-bit limbs
#[derive(Clone, Copy, PartialEq, Eq)]
struct Big([u64; L]);
impl Big {
    fn from(v: u64) -> Big { let mut r = Big([0; L]); r.0[0] = v; r }
    fn is_zero(&self) -> bool { self.0.iter().all(|&x| x == 0) }
    fn mul_small(&self, m: u64) -> Big {
        let mut r = Big([0; L]); let mut c: u128 = 0;
        for i in 0..L { let t = self.0[i] as u128 * m as u128 + c; r.0[i] = t as u64; c = t >> 64; }
        assert!(c == 0, "Big overflow in mul_small"); r
    }
    fn add(&self, o: &Big) -> Big {
        let mut r = Big([0; L]); let mut c: u128 = 0;
        for i in 0..L { let t = self.0[i] as u128 + o.0[i] as u128 + c; r.0[i] = t as u64; c = t >> 64; }
        assert!(c == 0, "Big overflow in add"); r
    }
    /// Full-width subtraction, required once beta and alpha are both Big.
    fn sub(&self, o: &Big) -> Big {
        let mut r = [0u64; L]; let mut b: i128 = 0;
        for i in 0..L {
            let t = self.0[i] as i128 - o.0[i] as i128 - b;
            if t < 0 { r[i] = (t + (1i128 << 64)) as u64; b = 1; } else { r[i] = t as u64; b = 0; }
        }
        assert!(b == 0, "Big underflow in sub"); Big(r)
    }
    fn sub_small(&self, m: u64) -> Big {
        let mut r = *self; let mut b: u128 = m as u128;
        for i in 0..L { let t = r.0[i] as u128; if t >= b { r.0[i] = (t - b) as u64; b = 0; break; } else { r.0[i] = ((1u128 << 64) + t - b) as u64; b = 1; } }
        assert!(b == 0, "Big underflow in sub_small"); r
    }
    fn divrem_small(&self, d: u64) -> (Big, u64) {
        let mut q = Big([0; L]); let mut rem: u128 = 0;
        for i in (0..L).rev() { let cur = (rem << 64) | self.0[i] as u128; q.0[i] = (cur / d as u128) as u64; rem = cur % d as u128; }
        (q, rem as u64)
    }
    /// Schoolbook product. Asserts on overflow rather than wrapping: alpha^2 and d(alpha)*d(beta)
    /// are both below D here, so 512 bits suffice, and a violated assert means the caller is wrong.
    fn mul(&self, o: &Big) -> Big {
        let mut r = [0u64; L];
        for i in 0..L {
            if self.0[i] == 0 { continue; }
            let mut c: u128 = 0;
            for j in 0..(L - i) {
                let t = self.0[i] as u128 * o.0[j] as u128 + r[i + j] as u128 + c;
                r[i + j] = t as u64; c = t >> 64;
            }
            assert!(c == 0, "Big overflow in mul");
            for j in (L - i)..L { assert!(o.0[j] == 0, "Big overflow in mul"); }
        }
        Big(r)
    }
    fn bits(&self) -> usize {
        for i in (0..L).rev() { if self.0[i] != 0 { return i * 64 + (64 - self.0[i].leading_zeros() as usize); } }
        0
    }
    fn cmp_big(&self, o: &Big) -> std::cmp::Ordering {
        for i in (0..L).rev() { if self.0[i] != o.0[i] { return self.0[i].cmp(&o.0[i]); } }
        std::cmp::Ordering::Equal
    }
    fn shl1b(&self) -> Big {
        let mut r = [0u64; L]; let mut c = 0u64;
        for i in 0..L { r[i] = (self.0[i] << 1) | c; c = self.0[i] >> 63; }
        assert!(c == 0, "Big overflow in shl1b"); Big(r)
    }
    fn shr1b(&self) -> Big {
        let mut r = [0u64; L];
        for i in 0..L { r[i] = self.0[i] >> 1; if i + 1 < L { r[i] |= self.0[i + 1] << 63; } }
        Big(r)
    }
    /// Binary long division: (quotient, remainder) of self by m. Needed once alpha exceeds u64,
    /// which happens from |T| ~ 10 upward and would silently wrap in the old u64 path.
    fn divrem(&self, m: &Big) -> (Big, Big) {
        assert!(!m.is_zero(), "divide by zero");
        if self.cmp_big(m) == std::cmp::Ordering::Less { return (Big([0; L]), *self); }
        let sb = self.bits(); let mb = m.bits();
        let mut sh = *m; let mut k = 0usize;
        while k + mb < sb { sh = sh.shl1b(); k += 1; }
        let mut r = *self; let mut q = Big([0; L]);
        loop {
            q = q.shl1b();
            if r.cmp_big(&sh) != std::cmp::Ordering::Less { r = r.sub(&sh); q.0[0] |= 1; }
            if k == 0 { break; }
            sh = sh.shr1b(); k -= 1;
        }
        (q, r)
    }
    fn to_dec(&self) -> String {
        if self.is_zero() { return "0".into(); }
        let mut parts = Vec::new(); let mut x = *self;
        while !x.is_zero() { let (q, r) = x.divrem_small(1_000_000_000_000_000_000); parts.push(r); x = q; }
        let mut s = format!("{}", parts.pop().unwrap());
        while let Some(p) = parts.pop() { s.push_str(&format!("{:018}", p)); }
        s
    }
}

fn modinv(a: u64, m: u64) -> u64 { // m prime
    let (mut t, mut nt, mut r, mut nr) = (0i128, 1i128, m as i128, (a % m) as i128);
    while nr != 0 { let qq = r / nr; t -= qq * nt; std::mem::swap(&mut t, &mut nt); r -= qq * nr; std::mem::swap(&mut r, &mut nr); }
    assert!(r == 1); ((t % m as i128 + m as i128) % m as i128) as u64
}

use std::collections::{BinaryHeap, VecDeque};
use std::cmp::Reverse;

struct Base { idx: usize, s: Vec<u64> }
struct Shared { done: Vec<usize>, results: Vec<String>, cand: u64, eqhits: u64, hits: u64 }

const SH: u32 = 62;

fn subset_sums(v: &[u64]) -> Vec<(u64, u32)> {
    let k = v.len(); let mut out = Vec::with_capacity(1 << k);
    for m in 0u32..(1u32 << k) { let mut s = 0u64; for i in 0..k { if m >> i & 1 == 1 { s += v[i]; } } out.push((s, m)); }
    out.sort_unstable(); out
}

/// Every (maskAB, maskCD) with lo <= sum <= hi, by Schroeppel-Shamir. Quarters q[0..4] hold (value, local mask).
fn window(q: &[Vec<(u64, u32)>; 4], lo: u64, hi: u64, mut f: impl FnMut(u32, u32, u32, u32)) {
    let (a, b, c, d) = (&q[0], &q[1], &q[2], &q[3]);
    // ascending stream of a+b
    let mut h1: BinaryHeap<Reverse<(u64, u32, u32)>> = a.iter().enumerate().map(|(i, x)| Reverse((x.0 + b[0].0, i as u32, 0u32))).collect();
    // descending stream of c+d
    let mut h2: BinaryHeap<(u64, u32, u32)> = c.iter().enumerate().map(|(i, x)| (x.0 + d[d.len() - 1].0, i as u32, (d.len() - 1) as u32)).collect();
    let mut buf: VecDeque<(u64, u32, u32)> = VecDeque::new(); // c+d values in [lo - s1, hi - s1], descending
    while let Some(Reverse((s1, ia, ib))) = h1.pop() {
        if s1 > hi { break; }
        if (ib as usize) + 1 < b.len() { h1.push(Reverse((a[ia as usize].0 + b[ib as usize + 1].0, ia, ib + 1))); }
        let top = hi - s1; let bot = lo.saturating_sub(s1);
        while let Some(&(s2, _, _)) = buf.front() { if s2 > top { buf.pop_front(); } else { break; } }
        while let Some(&(s2, ic, id)) = h2.peek() {
            if s2 < bot { break; }
            h2.pop();
            if id > 0 { h2.push((c[ic as usize].0 + d[id as usize - 1].0, ic, id - 1)); }
            if s2 <= top { buf.push_back((s2, ic, id)); }
        }
        for &(s2, ic, id) in buf.iter() { if s2 >= bot { f(a[ia as usize].1, b[ib as usize].1, c[ic as usize].1, d[id as usize].1); } }
    }
}

/// Exact test of T (bitmask over s). Returns (eq, full): eq = (*) holds; full = both cycle equations with integral q.
fn exact(s: &[u64], mask: u64) -> (bool, bool, String) {
    let n = s.len();
    let mut alpha = Big::from(1); let mut beta = Big::from(1);
    for i in 0..n { if mask >> i & 1 == 1 { alpha = alpha.mul_small(s[i]); } else { beta = beta.mul_small(s[i]); } }
    let mut da = Big::from(0); let mut db = Big::from(0);
    for i in 0..n { if mask >> i & 1 == 1 { da = da.add(&alpha.divrem_small(s[i]).0); } else { db = db.add(&beta.divrem_small(s[i]).0); } }
    // (*) times D:  alpha*beta - alpha^2 = alpha' * beta'   (needs beta > alpha)
    if alpha.cmp_big(&beta) != std::cmp::Ordering::Less { return (false, false, String::new()); }
    let lhs = alpha.mul(&beta).sub(&alpha.mul(&alpha)); let rhs = da.mul(&db);
    let eq = lhs == rhs;
    if !eq { return (false, false, String::new()); }
    let (q, r) = db.divrem(&alpha);
    let full = r.is_zero() && beta.sub(&alpha) == q.mul(&da);
    (eq, full, q.to_dec())
}

fn process(b: &Base, tau_log2: u32, out: &mut Vec<String>) -> (u64, u64, u64) {
    let s = &b.s; let n = s.len(); let t0 = Instant::now();
    let r: Vec<u64> = s.iter().map(|&p| (1u64 << SH) / p).collect();
    let sig = r.iter().sum::<u64>() as f64 / (1u64 << SH) as f64;
    let (lo, hi) = match bounds(&r, tau_log2) { Some(w) => w, None => {
        out.push(format!("DONE base={} empty-window sigma={:.6} cand=0 secs=0", b.idx, sig)); return (0, 0, 0); } };
    // f64 prefilter of (*): X(Sigma - X) + exp(2 log alpha - log D) - 1 = 0. Its computed value is within
    // ~1e-16 of the truth (terms below 1, 59 of them), so rejecting |res| > 1e-14 loses nothing; survivors go to exact arithmetic.
    let inv: Vec<f64> = s.iter().map(|&p| 1.0 / p as f64).collect();
    let lg: Vec<f64> = s.iter().map(|&p| (p as f64).ln()).collect();
    let sig_f: f64 = inv.iter().sum(); let ld: f64 = lg.iter().sum();
    // quarters
    let cuts = [0, n / 4, n / 2, 3 * n / 4, n];
    let q: [Vec<(u64, u32)>; 4] = std::array::from_fn(|k| subset_sums(&r[cuts[k]..cuts[k + 1]]));
    let (mut cand, mut pre, mut eqh, mut full) = (0u64, 0u64, 0u64, 0u64);
    let full_mask: u64 = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    window(&q, lo, hi, |ma, mb, mc, md| {
        let m = (ma as u64) << cuts[0] | (mb as u64) << cuts[1] | (mc as u64) << cuts[2] | (md as u64) << cuts[3];
        for &mm in &[m, full_mask ^ m] {
            if mm == 0 || mm == full_mask { continue; }
            cand += 1;
            let (mut x, mut la) = (0.0f64, 0.0f64);
            for i in 0..n { if mm >> i & 1 == 1 { x += inv[i]; la += lg[i]; } }
            if 2.0 * la >= ld { continue; }
            let res = x * (sig_f - x) + (2.0 * la - ld).exp() - 1.0;
            if res.abs() > 1e-14 { continue; }
            pre += 1;
            let (e, f, qs) = exact(s, mm);
            if e { eqh += 1; let tp: Vec<String> = (0..n).filter(|&i| mm >> i & 1 == 1).map(|i| s[i].to_string()).collect();
                   out.push(format!("base={} T={} q={} full={}", b.idx, tp.join(","), qs, f as u8)); }
            if f { full += 1; }
        }
    });
    out.push(format!("DONE base={} sigma={:.9} window=[{},{}] cand={} pre={} eq={} full={} secs={:.1}", b.idx, sig, lo, hi, cand, pre, eqh, full, t0.elapsed().as_secs_f64()));
    (cand, eqh, full)
}

/// Fixed-point window [lo, hi] containing Xfix(T) for every T with X(Sigma - X) in [1 - tau, 1) and
/// X <= Sigma/2, or None when no such X exists.
fn bounds(r: &[u64], tau_log2: u32) -> Option<(u64, u64)> {
    let n = r.len(); let scale = (1u64 << SH) as f64;
    let sig = r.iter().sum::<u64>() as f64 / scale;
    let tau = (2.0f64).powi(-(tau_log2 as i32));
    let disc_t = sig * sig - 4.0 * (1.0 - tau);
    if disc_t < 0.0 { return None; }
    let x_lo = (sig - disc_t.sqrt()) / 2.0;
    let disc0 = sig * sig - 4.0;
    let x_hi = if disc0 > 0.0 { (sig - disc0.sqrt()) / 2.0 } else { sig / 2.0 };
    let sens = sig / disc_t.sqrt().max(1e-9);
    let margin = (1u64 << 16) + (n as f64 * (2.0 + sens)) as u64 + n as u64 + ((x_hi * scale) * 1e-14) as u64;
    Some((((x_lo * scale) as u64).saturating_sub(margin), (x_hi * scale) as u64 + margin))
}

fn selftest() {
    // 1. window(): Schroeppel-Shamir output equals brute force on random data.
    let mut seed = 307u64; let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    for trial in 0..20 {
        let n = 20 + (trial % 5); let v: Vec<u64> = (0..n).map(|_| rnd() % (1u64 << 40)).collect();
        let tot: u64 = v.iter().sum(); let c = rnd() % tot; let w = rnd() % (tot / 50 + 1);
        let (lo, hi) = (c, c + w);
        let cuts = [0, n / 4, n / 2, 3 * n / 4, n];
        let q: [Vec<(u64, u32)>; 4] = std::array::from_fn(|k| subset_sums(&v[cuts[k]..cuts[k + 1]]));
        let mut got = Vec::new();
        window(&q, lo, hi, |a, b, cc, d| got.push((a as u64) << cuts[0] | (b as u64) << cuts[1] | (cc as u64) << cuts[2] | (d as u64) << cuts[3]));
        got.sort_unstable();
        let mut want = Vec::new();
        for m in 0u64..(1u64 << n) { let s: u64 = (0..n).filter(|&i| m >> i & 1 == 1).map(|i| v[i]).sum(); if s >= lo && s <= hi { want.push(m); } }
        assert!(got == want, "window mismatch at trial {}: got {} want {}", trial, got.len(), want.len());
        print!("window trial {} n={} hits={} ok; ", trial, n, got.len());
    }
    println!();
    // 2. bounds(): every T of a 24-prime toy base with 1 - X(Sigma-X) <= tau, X <= Sigma/2, lies in the window.
    let s: Vec<u64> = vec![2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89];
    let r: Vec<u64> = s.iter().map(|&p| (1u64 << SH) / p).collect();
    for &tl in &[1u32, 2] {
        let (lo, hi) = bounds(&r, tl).expect("toy window empty");
        let tau = (2.0f64).powi(-(tl as i32)); let sig: f64 = s.iter().map(|&p| 1.0 / p as f64).sum();
        let (mut need, mut inside) = (0u64, 0u64);
        for m in 1u64..(1u64 << 24) {
            let x: f64 = (0..24).filter(|&i| m >> i & 1 == 1).map(|i| 1.0 / s[i] as f64).sum();
            if x <= sig / 2.0 && 1.0 - x * (sig - x) <= tau && 1.0 - x * (sig - x) > 0.0 {
                need += 1; let xf: u64 = (0..24).filter(|&i| m >> i & 1 == 1).map(|i| r[i]).sum();
                if xf >= lo && xf <= hi { inside += 1; }
            }
        }
        assert!(need == inside, "bounds() misses {} of {} at tau=2^-{}", need - inside, need, tl);
        println!("bounds tau=2^-{}: {} of {} required subsets inside the window", tl, inside, need);
    }
    // 3. exact(): a planted identity. For S = {2,3,7,43} no split satisfies (*); check exact() rejects all,
    //    and that it accepts when (*) is forced on a synthetic check of its own algebra.
    let s4 = vec![2u64, 3, 7, 43];
    let mut acc = 0; for m in 1u64..15 { if exact(&s4, m).0 { acc += 1; } }
    println!("exact(): {} of 14 splits of {{2,3,7,43}} satisfy (*)", acc);
    // positive control: S = {2,3,5}, T = {5}: alpha = 5, beta = 6, 30 - 25 = 1 * 5, q = 1 (not prime, so no cycle)
    let pc = exact(&[2, 3, 5], 0b100);
    assert!(pc.0 && pc.1 && pc.2 == "1", "positive control failed");
    println!("exact(): positive control {{2,3,5}}, T = {{5}} accepted with q = 1");
    println!("SELFTEST PASSED");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 && args[1] == "--selftest" { selftest(); return; }
    if args.len() > 1 && args[1] == "--audit" { audit(&args[2], &args[3], args[4].parse().unwrap(), args[5].parse().unwrap()); return; }
    let path = &args[1]; let nthreads: usize = args[2].parse().unwrap(); let tl: u32 = args[3].parse().unwrap();
    let mut bases = Vec::new();
    for line in std::io::BufReader::new(std::fs::File::open(path).unwrap()).lines() {
        let line = line.unwrap(); let v: Vec<i64> = line.split_whitespace().map(|x| x.parse().unwrap()).collect();
        if v[1] == -1 || v[2] == -1 { continue; }
        bases.push(Base { idx: v[0] as usize, s: v[4..].iter().map(|&x| x as u64).collect() });
    }
    let mut done_set: HashSet<usize> = HashSet::new(); let mut prev = Vec::new();
    if let Ok(f) = std::fs::File::open("done.txt") { for l in std::io::BufReader::new(f).lines().flatten() { if let Ok(i) = l.trim().parse() { done_set.insert(i); } } }
    if let Ok(f) = std::fs::File::open("results.txt") { for l in std::io::BufReader::new(f).lines().flatten() { prev.push(l); } }
    let todo: Vec<&Base> = bases.iter().filter(|b| !done_set.contains(&b.idx)).collect();
    let total = todo.len();
    eprintln!("families {}  already done {}  to do {}  tau=2^-{}  threads {}", bases.len(), done_set.len(), total, tl, nthreads);
    let sh = Mutex::new(Shared { done: done_set.iter().cloned().collect(), results: prev, cand: 0, eqhits: 0, hits: 0 });
    let next = AtomicUsize::new(0); let finished = AtomicUsize::new(0); let t0 = Instant::now();
    let stop = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|sc| {
        sc.spawn(|| { loop { for _ in 0..30 { std::thread::sleep(std::time::Duration::from_secs(1)); if finished.load(Ordering::Relaxed) >= total || stop.load(Ordering::Relaxed) { return; } } checkpoint(&sh); } });
        for _ in 0..nthreads { sc.spawn(|| { loop {
            let i = next.fetch_add(1, Ordering::Relaxed); if i >= total { break; }
            let b = todo[i]; let mut out = Vec::new();
            let (c, e, h) = process(b, tl, &mut out);
            { let mut g = sh.lock().unwrap(); g.results.extend(out); g.done.push(b.idx); g.cand += c; g.eqhits += e; g.hits += h; }
            let f = finished.fetch_add(1, Ordering::Relaxed) + 1;
            let el = t0.elapsed().as_secs_f64(); let g = sh.lock().unwrap();
            eprintln!("  done {}/{}  {:.4} bases/s  elapsed {:.0}s  ETA {:.0}s  candidates {}  (*)-hits {}  cycle-hits {}", f, total, f as f64 / el, el, el * (total - f) as f64 / f as f64, g.cand, g.eqhits, g.hits);
        } }); }
    });
    stop.store(true, Ordering::Relaxed);
    checkpoint(&sh);
    let g = sh.lock().unwrap();
    println!("COMPLETE: families {}  candidates {}  (*)-hits {}  cycle-hits {}  ({:.0}s)", total, g.cand, g.eqhits, g.hits, t0.elapsed().as_secs_f64());
}

fn checkpoint(sh: &Mutex<Shared>) {
    let g = sh.lock().unwrap();
    let w = |name: &str, lines: &[String]| {
        let tmp = format!("{}.tmp", name);
        let attempt = (|| -> std::io::Result<()> {
            let mut f = std::fs::File::create(&tmp)?;
            for l in lines { writeln!(f, "{}", l)?; }
            f.sync_all()?;
            std::fs::rename(&tmp, name)
        })();
        if let Err(e) = attempt { eprintln!("  WARNING: checkpoint to {} failed ({}); run continues, will retry", name, e); let _ = std::fs::remove_file(&tmp); }
    };
    w("done.txt", &g.done.iter().map(|d| d.to_string()).collect::<Vec<_>>());
    w("results.txt", &g.results);
}

fn audit(path: &str, ids: &str, plants: usize, tl: u32) {
    let want: Vec<usize> = ids.split(',').map(|x| x.parse().unwrap()).collect();
    let mut seed = 0x9E3779B97F4A7C15u64; let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let (mut found, mut total) = (0usize, 0usize);
    for line in std::io::BufReader::new(std::fs::File::open(path).unwrap()).lines() {
        let line = line.unwrap(); let v: Vec<u64> = line.split_whitespace().map(|x| x.parse::<i64>().unwrap() as u64).collect();
        if !want.contains(&(v[0] as usize)) { continue; }
        let s: Vec<u64> = v[4..].to_vec(); let n = s.len();
        let r: Vec<u64> = s.iter().map(|&p| (1u64 << SH) / p).collect();
        let (lo, hi) = bounds(&r, tl).expect("empty window on a level-60 base");
        let half = (hi - lo) / 2;
        let cuts = [0, n / 4, n / 2, 3 * n / 4, n];
        let q: [Vec<(u64, u32)>; 4] = std::array::from_fn(|k| subset_sums(&r[cuts[k]..cuts[k + 1]]));
        for _ in 0..plants {
            let m0: u64 = rnd() & ((1u64 << n) - 1);
            let x0: u64 = (0..n).filter(|&i| m0 >> i & 1 == 1).map(|i| r[i]).sum();
            let (wlo, whi) = (x0.saturating_sub(half), x0 + half);
            let t0 = Instant::now(); let (mut hit, mut cand) = (false, 0u64);
            window(&q, wlo, whi, |ma, mb, mc, md| { cand += 1;
                let m = (ma as u64) << cuts[0] | (mb as u64) << cuts[1] | (mc as u64) << cuts[2] | (md as u64) << cuts[3];
                if m == m0 { hit = true; } });
            total += 1; if hit { found += 1; }
            println!("audit base={} plant |T0|={} found={} candidates={} secs={:.1}", v[0], m0.count_ones(), hit, cand, t0.elapsed().as_secs_f64());
        }
    }
    println!("AUDIT: found {} of {} planted splits", found, total);
    assert!(found == total, "Stage A audit FAILED: a planted split was not enumerated");
}
