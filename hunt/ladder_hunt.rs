// ladder_hunt.rs — derivative 2-cycle hunts over three imaginary quadratic rings:
//   ring 1: Z[i]        units {1,i,-1,-i}        (validation rung: must reproduce known results)
//   ring 2: Z[sqrt(-2)] units {1,-1}             (MINIMAL units: do prime phases alone suffice?)
//   ring 3: Z[omega]    units {±1,±w,±w^2} (6)   (MAXIMAL units among imaginary quadratics)
//
// Same design as gauss_hunt: Mode 1 = standard derivative pi'=1 on canonical representatives,
// cycles up to units, partners by full factorisation; Mode 2 = twisted derivatives pi' = unit.
// The ladder measures how the twisted-cycle population depends on the unit group: Z[i] data
// (16 cycles below norm 2e7) sits between ring 2 (only sign twists, which over Z provably gain
// nothing — but here the PRIME phases are already complex) and ring 3 (six phases per prime).
//
// Usage: ./ladder_hunt <ring 1|2|3> [B] [B2] [threads]   defaults B=200000000 B2=4000000
// Hits appended to ladder_hits.txt with certificates; round-trip factorisation checks throughout.

use std::env;
use std::fs::OpenOptions;
use std::io::Write as IoWrite;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

type G = (i64, i64);

#[derive(Clone, Copy)]
struct R { d: u8 }
impl R {
    fn mul(self, a: G, b: G) -> G {
        match self.d {
            1 => (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0),
            2 => (a.0 * b.0 - 2 * a.1 * b.1, a.0 * b.1 + a.1 * b.0),
            _ => (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0 - a.1 * b.1), // omega basis
        }
    }
    fn norm(self, a: G) -> i64 {
        match self.d {
            1 => a.0 * a.0 + a.1 * a.1,
            2 => a.0 * a.0 + 2 * a.1 * a.1,
            _ => a.0 * a.0 - a.0 * a.1 + a.1 * a.1,
        }
    }
    fn conj(self, a: G) -> G {
        match self.d {
            1 | 2 => (a.0, -a.1),
            _ => (a.0 - a.1, -a.1),
        }
    }
    fn units(self) -> &'static [G] {
        match self.d {
            1 => &[(1, 0), (0, 1), (-1, 0), (0, -1)],
            2 => &[(1, 0), (-1, 0)],
            _ => &[(1, 0), (0, 1), (1, 1), (-1, 0), (0, -1), (-1, -1)],
        }
    }
    fn ram_p(self) -> u64 { if self.d == 3 { 3 } else { 2 } }
    fn ram_class(self) -> G {
        match self.d { 1 => (1, 1), 2 => (0, 1), _ => (1, 2) }
    }
    fn is_split(self, p: u64) -> bool {
        match self.d {
            1 => p % 4 == 1,
            2 => p % 8 == 1 || p % 8 == 3,
            _ => p % 3 == 1,
        }
    }
    fn canon(self, z: G) -> G {
        let mut best: Option<G> = None;
        for &u in self.units() {
            let w = self.mul(z, u);
            if best.is_none() || w < best.unwrap() { best = Some(w); }
        }
        best.unwrap()
    }
    fn div_exact(self, a: G, b: G) -> Option<G> {
        let n = self.norm(b);
        let t = self.mul(a, self.conj(b));
        if t.0 % n != 0 || t.1 % n != 0 { None } else { Some((t.0 / n, t.1 / n)) }
    }
    // construct a prime above split p
    fn split_prime(self, p: u64) -> G {
        match self.d {
            1 => { let (x, y) = cornacchia(p, 1); (x as i64, y as i64) }
            2 => { let (x, y) = cornacchia(p, 2); (x as i64, y as i64) }
            _ => { let (u, v) = cornacchia(p, 3); ((u + v) as i64, 2 * v as i64) }
        }
    }
}

fn mulmod(a: u64, b: u64, m: u64) -> u64 { ((a as u128 * b as u128) % m as u128) as u64 }
fn powmod(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64; a %= m;
    while e > 0 { if e & 1 == 1 { r = mulmod(r, a, m); } a = mulmod(a, a, m); e >>= 1; }
    r
}
fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 { return n == p; }
    }
    let mut d = n - 1; let mut s = 0u32;
    while d & 1 == 0 { d >>= 1; s += 1; }
    'w: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..s - 1 { x = mulmod(x, x, n); if x == n - 1 { continue 'w; } }
        return false;
    }
    true
}
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn rho(n: u64) -> u64 {
    if n % 2 == 0 { return 2; }
    let mut c = 1u64;
    loop {
        let f = |x: u64| (mulmod(x, x, n) + c) % n;
        let (mut x, mut y, mut d) = (2u64, 2u64, 1u64);
        let mut k = 0u64;
        while d == 1 {
            x = f(x); y = f(f(y));
            d = gcd(x.abs_diff(y), n);
            k += 1; if k > 2_000_000 { break; }
        }
        if d != n && d != 1 { return d; }
        c += 1;
    }
}
fn factorize(mut n: u64, small: &[u32], out: &mut Vec<(u64, u32)>) {
    out.clear();
    for &p in small {
        let p = p as u64;
        if p * p > n { break; }
        if n % p == 0 {
            let mut e = 0u32;
            while n % p == 0 { n /= p; e += 1; }
            out.push((p, e));
        }
    }
    if n > 1 {
        let mut st = vec![n];
        while let Some(m) = st.pop() {
            if is_prime(m) {
                if let Some(s) = out.iter_mut().find(|(q, _)| *q == m) { s.1 += 1; }
                else { out.push((m, 1)); }
            } else { let d = rho(m); st.push(d); st.push(m / d); }
        }
    }
    out.sort();
}
fn isqrt(n: u64) -> u64 {
    let mut x = (n as f64).sqrt() as u64;
    while x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}
// Tonelli-Shanks sqrt mod odd prime p
fn sqrtmod(a: u64, p: u64) -> Option<u64> {
    let a = a % p;
    if a == 0 { return Some(0); }
    if powmod(a, (p - 1) / 2, p) != 1 { return None; }
    if p % 4 == 3 { return Some(powmod(a, (p + 1) / 4, p)); }
    let mut q = p - 1; let mut s = 0u32;
    while q & 1 == 0 { q >>= 1; s += 1; }
    let mut z = 2u64;
    while powmod(z, (p - 1) / 2, p) != p - 1 { z += 1; }
    let mut m = s;
    let mut c = powmod(z, q, p);
    let mut t = powmod(a, q, p);
    let mut r = powmod(a, (q + 1) / 2, p);
    while t != 1 {
        let mut i = 0u32; let mut tt = t;
        while tt != 1 { tt = mulmod(tt, tt, p); i += 1; }
        let b = powmod(c, 1 << (m - i - 1), p);
        m = i; c = mulmod(b, b, p);
        t = mulmod(t, c, p); r = mulmod(r, b, p);
    }
    Some(r)
}
// Cornacchia: x^2 + D y^2 = p (assumes solvable); returns (x, y)
fn cornacchia(p: u64, dd: u64) -> (u64, u64) {
    let mut r = sqrtmod((p - dd % p) % p, p).expect("not split");
    if r > p / 2 { r = p - r; }
    let (mut a, mut b) = (p, r);
    while b * b > p { let t = a % b; a = b; b = t; }
    let x = b;
    let rem = p - x * x;
    assert!(rem % dd == 0, "cornacchia fail");
    let y2 = rem / dd;
    let y = isqrt(y2);
    assert!(y * y == y2, "cornacchia fail2");
    (x, y)
}

// classify value z into canonical prime classes of ring r; false if not squarefree
fn classify(r: R, z: G, nf: &[(u64, u32)], out: &mut Vec<G>) -> bool {
    out.clear();
    for &(q, e) in nf {
        if q == r.ram_p() {
            if e >= 2 { return false; }
            out.push(r.canon(r.ram_class()));
        } else if r.is_split(q) {
            if e >= 3 { return false; }
            let pi = r.split_prime(q);
            if e == 2 {
                if z.0 % q as i64 == 0 && z.1 % q as i64 == 0 {
                    out.push(r.canon(pi)); out.push(r.canon(r.conj(pi)));
                } else { return false; }
            } else {
                if r.div_exact(z, pi).is_some() { out.push(r.canon(pi)); }
                else { out.push(r.canon(r.conj(pi))); }
            }
        } else {
            if e % 2 == 1 || e > 2 { return false; }
            out.push(r.canon((q as i64, 0)));
        }
    }
    let mut p: G = (1, 0);
    for &c in out.iter() { p = r.mul(p, c); }
    r.canon(p) == r.canon(z)
}

struct Hits { file: Mutex<std::fs::File> }
impl Hits {
    fn report(&self, line: &str) {
        println!("\n{}", line);
        let _ = writeln!(self.file.lock().unwrap(), "{}", line);
    }
}
fn fmt_hms(s: u64) -> String { format!("{:02}:{:02}:{:02}", s / 3600, (s / 60) % 60, s % 60) }

fn main() {
    let args: Vec<String> = env::args().collect();
    let ring_d: u8 = args.get(1).and_then(|s| s.parse().ok()).expect("ring 1|2|3 required");
    assert!((1..=3).contains(&ring_d));
    let r = R { d: ring_d };
    let b: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(200_000_000);
    let b2: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(4_000_000);
    let nthreads: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
        std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4)
    });
    let nu = r.units().len() as u64;

    // ---------- self-tests ----------
    {
        // ring axioms on samples
        let samples = [(3i64, 2i64), (-1, 4), (5, -3), (2, 7)];
        for &a in &samples {
            for &bb in &samples {
                assert_eq!(r.norm(r.mul(a, bb)), r.norm(a) * r.norm(bb));
                assert_eq!(r.mul(a, r.conj(a)), (r.norm(a), 0));
            }
        }
        for &u in r.units() { assert_eq!(r.norm(u), 1); }
        // split prime samples
        let p0 = match ring_d { 1 => 5u64, 2 => 3, _ => 7 };
        let pi = r.split_prime(p0);
        assert_eq!(r.norm(pi) as u64, p0);
        assert_eq!(r.norm(r.ram_class()) as u64, r.ram_p());
    }
    println!("self-test OK (ring {} axioms, split primes, ramified class)", ring_d);
    println!("config: ring={}  units={}  B={}  B2={}  threads={}", ring_d, nu, b, b2, nthreads);

    let small: Vec<u32> = {
        let lim = 4096usize;
        let mut comp = vec![false; lim + 1]; let mut v = Vec::new();
        for i in 2..=lim { if !comp[i] { v.push(i as u32); let mut j = i * i; while j <= lim { comp[j] = true; j += i; } } }
        v
    };
    let t0 = Instant::now();

    // ---------- class table: canonical primes with norm <= B/2 ----------
    let plim = (b / 2).max(8);
    let words = ((plim + 1) / 128 + 2) as usize;
    let mut sv = vec![0u64; words];
    {
        let mut i = 3u64;
        while i * i <= plim {
            if sv[(i >> 1) as usize / 64] & (1 << ((i >> 1) % 64)) == 0 {
                let mut j = i * i;
                while j <= plim { sv[(j >> 1) as usize / 64] |= 1 << ((j >> 1) % 64); j += 2 * i; }
            }
            i += 2;
        }
    }
    let isp = |p: u64| -> bool {
        if p == 2 { return true; }
        if p < 2 || p % 2 == 0 { return false; }
        sv[(p >> 1) as usize / 64] & (1 << ((p >> 1) % 64)) == 0
    };
    let mut classes: Vec<(i64, i64, u64)> = Vec::new();
    {
        let c = r.canon(r.ram_class());
        if r.ram_p() <= plim { classes.push((c.0, c.1, r.ram_p())); }
    }
    let mut p = 3u64;
    while p <= plim {
        if isp(p) && p != r.ram_p() {
            if r.is_split(p) {
                let pi = r.split_prime(p);
                let c1 = r.canon(pi); let c2 = r.canon(r.conj(pi));
                classes.push((c1.0, c1.1, p));
                if c2 != c1 { classes.push((c2.0, c2.1, p)); }
            } else if p * p <= plim {
                let c = r.canon((p as i64, 0));
                classes.push((c.0, c.1, p * p));
            }
        }
        p += 2;
    }
    // p=2 inert/split handling for ring 3 (2 inert in Z[omega]: 2 mod 3 = 2)
    if ring_d == 3 && 4 <= plim {
        let c = r.canon((2, 0));
        classes.push((c.0, c.1, 4));
    }
    classes.sort_by_key(|c| (c.2, c.0, c.1));
    let norms: Vec<u64> = classes.iter().map(|c| c.2).collect();
    let l = classes.len();
    println!("prime classes with norm <= {}: {}  [{}]", plim, l, fmt_hms(t0.elapsed().as_secs()));

    const BLK: u64 = 4096;
    let mut cum: Vec<u64> = Vec::with_capacity(l + 1);
    let mut acc = 0u64; cum.push(0);
    for i0 in 0..l {
        let cap = b / norms[i0];
        let hi = norms.partition_point(|&n| n <= cap);
        let cnt = hi.saturating_sub(i0 + 1) as u64;
        acc += (cnt + BLK - 1) / BLK; cum.push(acc);
    }
    let total_units_w = acc;
    let hits = Hits { file: Mutex::new(OpenOptions::new().create(true).append(true).open("ladder_hits.txt").unwrap()) };

    // ---------- counting pass ----------
    let nx = AtomicU64::new(0);
    let cnt = AtomicU64::new(0);
    std::thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| {
                let mut idx = Vec::new();
                loop {
                    let u = nx.fetch_add(1, Ordering::Relaxed);
                    if u >= total_units_w { break; }
                    let i0 = cum.partition_point(|&c| c <= u) - 1;
                    let blk = u - cum[i0];
                    let mut local = 0u64;
                    run_block(r, &classes, &norms, b, i0, blk, BLK, &mut idx, &mut |_, _| local += 1);
                    cnt.fetch_add(local, Ordering::Relaxed);
                }
            });
        }
    });
    let total_c = cnt.load(Ordering::Relaxed);
    println!("Mode 1 candidates (omega>=2, norm <= {}): {}  [{}]", b, total_c, fmt_hms(t0.elapsed().as_secs()));

    // ---------- Mode 1 ----------
    let nx2 = AtomicU64::new(0);
    let done = AtomicU64::new(0);
    let (zc, uc, fc, cc, rt, sp) = (AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0));
    let t1 = Instant::now();
    std::thread::scope(|sc| {
        sc.spawn(|| loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let dcv = done.load(Ordering::Relaxed);
            if dcv >= total_c { break; }
            let f = dcv as f64 / total_c as f64;
            let el = t1.elapsed().as_secs_f64();
            let eta = if f > 1e-9 { el / f - el } else { 0.0 };
            eprint!("\r[ring {} M1] {:5.1}% | {:6.2} Mc/s | elapsed {} | ETA {} | cyc={} fix={} zero={} rt={}   ",
                ring_d, f * 100.0, dcv as f64 / el / 1e6, fmt_hms(el as u64), fmt_hms(eta as u64),
                cc.load(Ordering::Relaxed), fc.load(Ordering::Relaxed), zc.load(Ordering::Relaxed), rt.load(Ordering::Relaxed));
        });
        for _ in 0..nthreads {
            sc.spawn(|| {
                let mut idx = Vec::new();
                let mut nf = Vec::new();
                let mut bcl: Vec<G> = Vec::new();
                let mut local = 0u64;
                loop {
                    let u = nx2.fetch_add(1, Ordering::Relaxed);
                    if u >= total_units_w { break; }
                    let i0 = cum.partition_point(|&c| c <= u) - 1;
                    let blk = u - cum[i0];
                    run_block(r, &classes, &norms, b, i0, blk, BLK, &mut idx, &mut |aidx, prod| {
                        local += 1;
                        if local & 0xFFF == 0 { done.fetch_add(0x1000, Ordering::Relaxed); }
                        let mut d: G = (0, 0);
                        for &j in aidx {
                            let z = (classes[j].0, classes[j].1);
                            let c = r.div_exact(prod, z).unwrap();
                            d = (d.0 + c.0, d.1 + c.1);
                        }
                        if d == (0, 0) {
                            zc.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** ring {} ZERO-DERIVATIVE: {:?} ***", ring_d,
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>()));
                            return;
                        }
                        let nd = r.norm(d) as u64;
                        if nd == 1 {
                            uc.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** ring {} UNIT-DERIVATIVE a'~1: classes {:?}, a'={:?} ***",
                                r.d, aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), d));
                            return;
                        }
                        if r.canon(d) == r.canon(prod) {
                            fc.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** ring {} FIXED POINT a'~a: {:?} ***", ring_d,
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>()));
                            return;
                        }
                        factorize(nd, &small, &mut nf);
                        if !classify(r, d, &nf, &mut bcl) {
                            let mut pchk: G = (1, 0);
                            for &z in bcl.iter() { pchk = r.mul(pchk, z); }
                            if !bcl.is_empty() && r.norm(pchk) as u64 == nd && r.canon(pchk) != r.canon(d) {
                                rt.fetch_add(1, Ordering::Relaxed);
                            }
                            return;
                        }
                        if bcl.len() < 2 { return; }
                        sp.fetch_add(1, Ordering::Relaxed);
                        let mut e: G = (0, 0);
                        for &z in bcl.iter() {
                            let c = r.div_exact(d, z).unwrap();
                            e = (e.0 + c.0, e.1 + c.1);
                        }
                        if e != (0, 0) && r.canon(e) == r.canon(prod) {
                            cc.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!(
                                "*** ring {} 2-CYCLE (up to units): a={:?} classes {:?} | b=a'={:?} classes {:?} | b'~a VERIFIED ***",
                                ring_d, prod,
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(),
                                d, bcl));
                        }
                    });
                }
                done.fetch_add(local & 0xFFF, Ordering::Relaxed);
            });
        }
        sc.spawn(|| loop {
            std::thread::sleep(std::time::Duration::from_millis(500));
            if nx2.load(Ordering::Relaxed) >= total_units_w + nthreads as u64 {
                done.store(total_c, Ordering::Relaxed); break;
            }
        });
    });
    done.store(total_c, Ordering::Relaxed);
    println!("\nring {} Mode 1 complete: {} candidates, sf-partners {}, cycles {}, fixed {}, zero {}, unit' {}, rt-fail {}  [{}]",
        ring_d, total_c, sp.load(Ordering::Relaxed), cc.load(Ordering::Relaxed), fc.load(Ordering::Relaxed),
        zc.load(Ordering::Relaxed), uc.load(Ordering::Relaxed), rt.load(Ordering::Relaxed), fmt_hms(t1.elapsed().as_secs()));

    // ---------- Mode 2 (twisted) ----------
    if b2 >= 4 {
        let t2 = Instant::now();
        let mut idx: Vec<usize> = Vec::new();
        let mut nf = Vec::new();
        let mut bcl: Vec<G> = Vec::new();
        let mut cands2 = 0u64; let mut tw = 0u64; let mut twf = 0u64;
        let lim2 = norms.partition_point(|&n| n <= b2 / 2);
        for i0 in 0..lim2 {
            idx.clear(); idx.push(i0);
            dfs2(r, &classes, &norms, b2, i0, norms[i0], (classes[i0].0, classes[i0].1),
                 &mut idx, &small, &mut nf, &mut bcl, &mut cands2, &mut tw, &mut twf, &hits, nu);
            if i0 % 200 == 0 {
                eprint!("\r[ring {} M2] class {}/{} | pairs {} | twisted cycles {} fixed {}   ",
                    ring_d, i0, lim2, cands2, tw, twf);
            }
        }
        eprintln!();
        println!("ring {} Mode 2 complete: {} (candidate,unit-vector) pairs, norm<={}, omega<=5; twisted cycles {}, twisted fixed {}  [{}]",
            ring_d, cands2, b2, tw, twf, fmt_hms(t2.elapsed().as_secs()));
    }
    println!("\nLADDER SUMMARY ring {} (units {}): see counts above; hits in ladder_hits.txt; total {}",
        ring_d, nu, fmt_hms(t0.elapsed().as_secs()));
}

fn run_block<F: FnMut(&[usize], G)>(
    r: R, classes: &[(i64, i64, u64)], norms: &[u64], b: u64,
    i0: usize, blk: u64, blksz: u64, idx: &mut Vec<usize>, f: &mut F,
) {
    let n0 = norms[i0];
    let z0 = (classes[i0].0, classes[i0].1);
    let start = i0 + 1 + (blk * blksz) as usize;
    let end = (i0 + 1 + ((blk + 1) * blksz) as usize).min(norms.len());
    idx.clear(); idx.push(i0);
    for i1 in start..end {
        if norms[i1] > b / n0 { break; }
        let z1 = (classes[i1].0, classes[i1].1);
        let pp = r.mul(z0, z1);
        idx.push(i1);
        f(idx, pp);
        ext(r, classes, norms, b, i1 + 1, n0 * norms[i1], pp, idx, f);
        idx.pop();
    }
}
fn ext<F: FnMut(&[usize], G)>(
    r: R, classes: &[(i64, i64, u64)], norms: &[u64], b: u64,
    start: usize, pn: u64, prod: G, idx: &mut Vec<usize>, f: &mut F,
) {
    for i in start..norms.len() {
        if norms[i] > b / pn { break; }
        let np = r.mul(prod, (classes[i].0, classes[i].1));
        idx.push(i);
        f(idx, np);
        ext(r, classes, norms, b, i + 1, pn * norms[i], np, idx, f);
        idx.pop();
    }
}
fn dfs2(
    r: R, classes: &[(i64, i64, u64)], norms: &[u64], b2: u64,
    last: usize, pn: u64, prod: G, idx: &mut Vec<usize>,
    small: &[u32], nf: &mut Vec<(u64, u32)>, bcl: &mut Vec<G>,
    cands: &mut u64, tw: &mut u64, twf: &mut u64, hits: &Hits, nu: u64,
) {
    if idx.len() >= 2 {
        proc2(r, classes, idx, prod, small, nf, bcl, cands, tw, twf, hits, nu);
    }
    if idx.len() >= 5 { return; }
    for i in last + 1..norms.len() {
        if norms[i] > b2 / pn { break; }
        idx.push(i);
        dfs2(r, classes, norms, b2, i, pn * norms[i], r.mul(prod, (classes[i].0, classes[i].1)),
             idx, small, nf, bcl, cands, tw, twf, hits, nu);
        idx.pop();
    }
}
fn proc2(
    r: R, classes: &[(i64, i64, u64)], aidx: &[usize], prod: G,
    small: &[u32], nf: &mut Vec<(u64, u32)>, bcl: &mut Vec<G>,
    cands: &mut u64, tw: &mut u64, twf: &mut u64, hits: &Hits, nu: u64,
) {
    let k = aidx.len();
    let cofs: Vec<G> = aidx.iter().map(|&j| r.div_exact(prod, (classes[j].0, classes[j].1)).unwrap()).collect();
    let total = nu.pow(k as u32 - 1);
    if total > 1 << 16 { return; }
    let units = r.units();
    for code in 0..total {
        *cands += 1;
        let mut d = cofs[0];
        let mut c = code;
        for t in 1..k {
            let w = r.mul(cofs[t], units[(c % nu) as usize]);
            d = (d.0 + w.0, d.1 + w.1);
            c /= nu;
        }
        if d == (0, 0) { continue; }
        if r.canon(d) == r.canon(prod) {
            *twf += 1;
            hits.report(&format!("*** ring {} TWISTED FIXED: {:?} code {} ***", r.d,
                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), code));
            continue;
        }
        let nd = r.norm(d) as u64;
        if nd <= 1 { continue; }
        factorize(nd, small, nf);
        if !classify(r, d, nf, bcl) || bcl.len() < 2 { continue; }
        let terms: Vec<G> = bcl.iter().map(|&z| r.div_exact(d, z).unwrap()).collect();
        let mods: Vec<f64> = terms.iter().map(|&t| (r.norm(t) as f64).sqrt()).collect();
        let mut suf = vec![0.0; terms.len() + 1];
        for i in (0..terms.len()).rev() { suf[i] = suf[i + 1] + mods[i]; }
        if close(r, &terms, &suf, 0, (0, 0), prod, nu) {
            *tw += 1;
            hits.report(&format!(
                "*** ring {} TWISTED 2-CYCLE: a-classes {:?} code {} | b=a'={:?} b-classes {:?} | closes exactly ***",
                r.d, aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), code, d, bcl));
        }
    }
}
fn close(r: R, terms: &[G], suf: &[f64], i: usize, part: G, target: G, nu: u64) -> bool {
    if i == terms.len() { return part == target; }
    let dx = (target.0 - part.0) as f64;
    let dy = (target.1 - part.1) as f64;
    // crude euclidean bound via norms (valid up to ring metric constant; use safety factor 2)
    if (dx * dx + dy * dy).sqrt() > 2.0 * (suf[i] + 1e-6) { return false; }
    let units = r.units();
    for u in 0..nu as usize {
        let w = r.mul(terms[i], units[u]);
        if close(r, terms, suf, i + 1, (part.0 + w.0, part.1 + w.1), target, nu) { return true; }
    }
    false
}
