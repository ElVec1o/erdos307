// real_hunt.rs — derivative 2-cycle hunt over Z[sqrt(2)]: the REAL-quadratic rung.
//
// This tests the second pillar of the Q-uniqueness classification. Z[sqrt2] is totally real
// (squares are nonnegative in both embeddings), but its unit group is infinite
// (eps = 1+sqrt2, N(eps) = -1), elements have no canonical positivity, and norms take both
// signs — so the mass barrier's positivity bookkeeping has no purchase.  A cycle here would
// complete the experimental bracketing of Q from both axes (orderability AND unit finiteness).
//
// Mode 1: canonical representatives (log-band reduction by eps), pi' = 1, cycles up to units,
//         partners by full factorisation of |N(a')|.
// Mode 2: twisted derivatives pi' = ±eps^k with |k| <= K (unit-height cap, CLI).
//
// Usage: ./real_hunt [B] [B2] [K] [threads]   defaults B=200000000 B2=2000000 K=2
// Certificates appended to real_hits.txt.

use std::env;
use std::fs::OpenOptions;
use std::io::Write as IoWrite;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

type G = (i64, i64); // x + y*sqrt(2)

#[inline]
fn mul(a: G, b: G) -> G { (a.0 * b.0 + 2 * a.1 * b.1, a.0 * b.1 + a.1 * b.0) }
#[inline]
fn norm(a: G) -> i64 { a.0 * a.0 - 2 * a.1 * a.1 } // SIGNED
#[inline]
fn conj(a: G) -> G { (a.0, -a.1) }
fn div_exact(a: G, b: G) -> Option<G> {
    let n = norm(b);
    let t = mul(a, conj(b));
    if t.0 % n != 0 || t.1 % n != 0 { None } else { Some((t.0 / n, t.1 / n)) }
}
const EPS: G = (1, 1);      // 1+sqrt2, norm -1
const EPSI: G = (-1, 1);    // (1+sqrt2)^{-1} = -1+sqrt2, norm -1
fn emb(a: G) -> (f64, f64) {
    let r = std::f64::consts::SQRT_2;
    (a.0 as f64 + a.1 as f64 * r, a.0 as f64 - a.1 as f64 * r)
}
// canonical associate: emb1 > 0 and t = ln(v1/|v2|) in [-ln(eps), ln(eps))
fn canon(z: G) -> G {
    let lneps = (1.0 + std::f64::consts::SQRT_2).ln();
    let mut w = z;
    let (v1, _) = emb(w);
    if v1 < 0.0 { w = (-w.0, -w.1); }
    for _ in 0..3 {
        let (v1, v2) = emb(w);
        let t = v1.abs().ln() - v2.abs().ln();
        let k = (t / (2.0 * lneps)).round() as i64;
        if k == 0 { break; }
        let step = if k > 0 { EPSI } else { EPS };
        for _ in 0..k.abs() { w = mul(w, step); }
        let (nv1, _) = emb(w);
        if nv1 < 0.0 { w = (-w.0, -w.1); }
    }
    let (v1, _) = emb(w);
    if v1 < 0.0 { w = (-w.0, -w.1); }
    w
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
        if n % p == 0 { let mut e = 0; while n % p == 0 { n /= p; e += 1; } out.push((p, e)); }
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
fn sqrtmod(a: u64, p: u64) -> Option<u64> {
    let a = a % p;
    if a == 0 { return Some(0); }
    if powmod(a, (p - 1) / 2, p) != 1 { return None; }
    if p % 4 == 3 { return Some(powmod(a, (p + 1) / 4, p)); }
    let mut q = p - 1; let mut s = 0u32;
    while q & 1 == 0 { q >>= 1; s += 1; }
    let mut z = 2u64;
    while powmod(z, (p - 1) / 2, p) != p - 1 { z += 1; }
    let (mut m, mut c, mut t, mut r) = (s, powmod(z, q, p), powmod(a, q, p), powmod(a, (q + 1) / 2, p));
    while t != 1 {
        let mut i = 0u32; let mut tt = t;
        while tt != 1 { tt = mulmod(tt, tt, p); i += 1; }
        let b = powmod(c, 1 << (m - i - 1), p);
        m = i; c = mulmod(b, b, p); t = mulmod(t, c, p); r = mulmod(r, b, p);
    }
    Some(r)
}
// x^2 - 2 y^2 = ±p for split p (p = ±1 mod 8), via Euclid with cofactors
fn rep_real(p: u64) -> G {
    let r = sqrtmod(2 % p, p).expect("not split");
    let (mut a0, mut a1) = (p as i128, r as i128);
    let (mut t0, mut t1) = (0i128, 1i128);
    loop {
        let v = a1 * a1 - 2 * t1 * t1;
        if v == p as i128 || v == -(p as i128) { return (a1 as i64, t1 as i64); }
        if v == 2 * p as i128 || v == -2 * (p as i128) {
            debug_assert!(a1 % 2 == 0);
            return (t1 as i64, (a1 / 2) as i64); // (y, x/2): norm = -(v/2)
        }
        if a1 == 0 { panic!("rep_real failed for {}", p); }
        let q = a0 / a1;
        let a2 = a0 - q * a1; let t2 = t0 - q * t1;
        a0 = a1; a1 = a2; t0 = t1; t1 = t2;
    }
}
fn is_split(p: u64) -> bool { p % 8 == 1 || p % 8 == 7 }

// classify d into canonical prime classes; false if not squarefree in Z[sqrt2]
fn classify(d: G, nf: &[(u64, u32)], out: &mut Vec<G>) -> bool {
    out.clear();
    for &(q, e) in nf {
        if q == 2 {
            if e >= 2 { return false; }
            out.push(canon((0, 1)));
        } else if is_split(q) {
            if e >= 3 { return false; }
            let pi = rep_real(q);
            if e == 2 {
                if d.0 % q as i64 == 0 && d.1 % q as i64 == 0 {
                    out.push(canon(pi)); out.push(canon(conj(pi)));
                } else { return false; }
            } else {
                if div_exact(d, pi).is_some() { out.push(canon(pi)); }
                else { out.push(canon(conj(pi))); }
            }
        } else {
            if e % 2 == 1 || e > 2 { return false; }
            out.push(canon((q as i64, 0)));
        }
    }
    let mut p: G = (1, 0);
    for &c in out.iter() { p = mul(p, c); }
    canon(p) == canon(d)
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
    let b: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(200_000_000);
    let b2: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(2_000_000);
    let kcap: i64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(2);
    let nthreads: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
        std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4)
    });

    // unit table for Mode 2: ±eps^k, |k| <= K
    let mut units: Vec<G> = Vec::new();
    {
        let mut pos = vec![(1i64, 0i64)];
        for _ in 0..kcap { pos.push(mul(*pos.last().unwrap(), EPS)); }
        let mut neg = vec![];
        let mut w = (1, 0);
        for _ in 0..kcap { w = mul(w, EPSI); neg.push(w); }
        for u in pos.iter().chain(neg.iter()) { units.push(*u); units.push((-u.0, -u.1)); }
    }
    let nu = units.len() as u64;

    // ---------- self-tests ----------
    {
        assert_eq!(mul(EPS, EPSI), (1, 0));
        assert_eq!(norm(EPS), -1);
        let samples = [(3i64, 1i64), (5, 2), (-7, 3), (4, -1)];
        for &a in &samples {
            for &bb in &samples { assert_eq!(norm(mul(a, bb)), norm(a) * norm(bb)); }
            // canon invariance under units and sign
            let c = canon(a);
            assert_eq!(canon((-a.0, -a.1)), c);
            assert_eq!(canon(mul(a, EPS)), c);
            assert_eq!(canon(mul(a, EPSI)), c);
            assert_eq!(canon(mul(mul(a, EPS), EPS)), c);
        }
        // split reps
        for p in [7u64, 17, 23, 31, 41, 47, 71, 73, 79, 89, 97, 103] {
            if !is_split(p) { continue; }
            let pi = rep_real(p);
            assert_eq!(norm(pi).unsigned_abs(), p, "rep_real {}", p);
            assert_ne!(canon(pi), canon(conj(pi)), "split classes must differ {}", p);
        }
        // classification round-trip on a constructed product
        let cls = [canon((0, 1)), canon(rep_real(7)), canon((3, 0)), canon(rep_real(17))];
        let mut v: G = (1, 0);
        for &z in &cls { v = mul(v, z); }
        let small: Vec<u32> = simple_primes(4096);
        let mut nf = Vec::new();
        factorize(norm(v).unsigned_abs(), &small, &mut nf);
        let mut got = Vec::new();
        assert!(classify(v, &nf, &mut got));
        let mut want = cls.to_vec();
        want.sort(); got.sort();
        assert_eq!(got, want);
    }
    println!("self-test OK (eps arithmetic, canon invariance, indefinite reps, classification round-trip)");
    println!("config: Z[sqrt2]  B={}  B2={}  unit-cap K={} ({} twist units)  threads={}", b, b2, kcap, nu, nthreads);

    let small: Vec<u32> = simple_primes(4096);
    let t0 = Instant::now();

    // ---------- class table by |norm| <= B/2 ----------
    let plim = (b / 2).max(8);
    let sieve = bit_sieve(plim);
    let mut classes: Vec<(i64, i64, u64)> = Vec::new();
    {
        let c = canon((0, 1));
        classes.push((c.0, c.1, 2));
    }
    let mut p = 3u64;
    while p <= plim {
        if sieve_is_prime(&sieve, p) {
            if is_split(p) {
                let pi = rep_real(p);
                let c1 = canon(pi); let c2 = canon(conj(pi));
                classes.push((c1.0, c1.1, p));
                classes.push((c2.0, c2.1, p));
            } else if p * p <= plim {
                let c = canon((p as i64, 0));
                classes.push((c.0, c.1, p * p));
            }
        }
        p += 2;
    }
    classes.sort_by_key(|c| (c.2, c.0, c.1));
    let norms: Vec<u64> = classes.iter().map(|c| c.2).collect();
    let l = classes.len();
    println!("prime classes with |norm| <= {}: {}  [{}]", plim, l, fmt_hms(t0.elapsed().as_secs()));

    const BLK: u64 = 4096;
    let mut cum: Vec<u64> = Vec::with_capacity(l + 1);
    let mut acc = 0u64; cum.push(0);
    for i0 in 0..l {
        let cap = b / norms[i0];
        let hi = norms.partition_point(|&n| n <= cap);
        acc += ((hi.saturating_sub(i0 + 1) as u64) + BLK - 1) / BLK;
        cum.push(acc);
    }
    let total_units_w = acc;
    let hits = Hits { file: Mutex::new(OpenOptions::new().create(true).append(true).open("real_hits.txt").unwrap()) };

    // counting pass
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
                    run_block(&classes, &norms, b, i0, blk, BLK, &mut idx, &mut |_, _| local += 1);
                    cnt.fetch_add(local, Ordering::Relaxed);
                }
            });
        }
    });
    let total_c = cnt.load(Ordering::Relaxed);
    println!("Mode 1 candidates (omega>=2, |norm| <= {}): {}  [{}]", b, total_c, fmt_hms(t0.elapsed().as_secs()));

    // ---------- Mode 1 ----------
    let nx2 = AtomicU64::new(0);
    let done = AtomicU64::new(0);
    let (zc, uc, fc, cc, rt) = (AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0));
    let t1 = Instant::now();
    std::thread::scope(|sc| {
        sc.spawn(|| loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let dv = done.load(Ordering::Relaxed);
            if dv >= total_c { break; }
            let f = dv as f64 / total_c as f64;
            let el = t1.elapsed().as_secs_f64();
            let eta = if f > 1e-9 { el / f - el } else { 0.0 };
            eprint!("\r[Z[sqrt2] M1] {:5.1}% | {:6.2} Mc/s | elapsed {} | ETA {} | cyc={} fix={} zero={} unit'={} rt={}   ",
                f * 100.0, dv as f64 / el / 1e6, fmt_hms(el as u64), fmt_hms(eta as u64),
                cc.load(Ordering::Relaxed), fc.load(Ordering::Relaxed), zc.load(Ordering::Relaxed),
                uc.load(Ordering::Relaxed), rt.load(Ordering::Relaxed));
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
                    run_block(&classes, &norms, b, i0, blk, BLK, &mut idx, &mut |aidx, prod| {
                        local += 1;
                        if local & 0xFFF == 0 { done.fetch_add(0x1000, Ordering::Relaxed); }
                        let mut d: G = (0, 0);
                        for &j in aidx {
                            let c = div_exact(prod, (classes[j].0, classes[j].1)).unwrap();
                            d = (d.0 + c.0, d.1 + c.1);
                        }
                        if d == (0, 0) {
                            zc.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** Z[sqrt2] ZERO-DERIVATIVE: {:?} ***",
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>()));
                            return;
                        }
                        let nd = norm(d).unsigned_abs();
                        if nd == 1 {
                            uc.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** Z[sqrt2] UNIT-DERIVATIVE a'~unit: {:?} a'={:?} ***",
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), d));
                            return;
                        }
                        if canon(d) == canon(prod) {
                            fc.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** Z[sqrt2] FIXED POINT a'~a: {:?} ***",
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>()));
                            return;
                        }
                        factorize(nd, &small, &mut nf);
                        if !classify(d, &nf, &mut bcl) {
                            let mut pchk: G = (1, 0);
                            for &z in bcl.iter() { pchk = mul(pchk, z); }
                            if !bcl.is_empty() && norm(pchk).unsigned_abs() == nd && canon(pchk) != canon(d) {
                                rt.fetch_add(1, Ordering::Relaxed);
                            }
                            return;
                        }
                        if bcl.len() < 2 { return; }
                        let mut e: G = (0, 0);
                        for &z in bcl.iter() {
                            let c = div_exact(d, z).unwrap();
                            e = (e.0 + c.0, e.1 + c.1);
                        }
                        if e != (0, 0) && canon(e) == canon(prod) {
                            cc.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!(
                                "*** Z[sqrt2] 2-CYCLE (up to units): a={:?} classes {:?} | b=a'={:?} classes {:?} | b'~a VERIFIED ***",
                                prod, aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), d, bcl));
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
    println!("\nZ[sqrt2] Mode 1 complete: {} candidates, cycles {}, fixed {}, zero {}, unit' {}, rt-fail {}  [{}]",
        total_c, cc.load(Ordering::Relaxed), fc.load(Ordering::Relaxed), zc.load(Ordering::Relaxed),
        uc.load(Ordering::Relaxed), rt.load(Ordering::Relaxed), fmt_hms(t1.elapsed().as_secs()));

    // ---------- Mode 2 ----------
    if b2 >= 4 {
        let t2 = Instant::now();
        let mut idx = Vec::new();
        let mut nf = Vec::new();
        let mut bcl: Vec<G> = Vec::new();
        let (mut cands2, mut tw, mut twf) = (0u64, 0u64, 0u64);
        let lim2 = norms.partition_point(|&n| n <= b2 / 2);
        for i0 in 0..lim2 {
            idx.clear(); idx.push(i0);
            dfs2(&classes, &norms, b2, i0, norms[i0], (classes[i0].0, classes[i0].1),
                 &mut idx, &small, &mut nf, &mut bcl, &mut cands2, &mut tw, &mut twf, &hits, &units, kcap);
            if i0 % 100 == 0 {
                eprint!("\r[Z[sqrt2] M2] class {}/{} | pairs {} | twisted cycles {} fixed {}   ", i0, lim2, cands2, tw, twf);
            }
        }
        eprintln!();
        println!("Z[sqrt2] Mode 2 complete: {} (candidate,unit-vector) pairs, |norm|<={}, omega<=4, K={}; twisted cycles {}, fixed {}  [{}]",
            cands2, b2, kcap, tw, twf, fmt_hms(t2.elapsed().as_secs()));
    }
    println!("\nREAL-QUADRATIC SUMMARY: see real_hits.txt; total {}", fmt_hms(t0.elapsed().as_secs()));
}

fn run_block<F: FnMut(&[usize], G)>(
    classes: &[(i64, i64, u64)], norms: &[u64], b: u64,
    i0: usize, blk: u64, blksz: u64, idx: &mut Vec<usize>, f: &mut F,
) {
    let n0 = norms[i0];
    let z0 = (classes[i0].0, classes[i0].1);
    let start = i0 + 1 + (blk * blksz) as usize;
    let end = (i0 + 1 + ((blk + 1) * blksz) as usize).min(norms.len());
    idx.clear(); idx.push(i0);
    for i1 in start..end {
        if norms[i1] > b / n0 { break; }
        let pp = mul(z0, (classes[i1].0, classes[i1].1));
        idx.push(i1);
        f(idx, pp);
        ext(classes, norms, b, i1 + 1, n0 * norms[i1], pp, idx, f);
        idx.pop();
    }
}
fn ext<F: FnMut(&[usize], G)>(
    classes: &[(i64, i64, u64)], norms: &[u64], b: u64,
    start: usize, pn: u64, prod: G, idx: &mut Vec<usize>, f: &mut F,
) {
    for i in start..norms.len() {
        if norms[i] > b / pn { break; }
        let np = mul(prod, (classes[i].0, classes[i].1));
        idx.push(i);
        f(idx, np);
        ext(classes, norms, b, i + 1, pn * norms[i], np, idx, f);
        idx.pop();
    }
}
fn dfs2(
    classes: &[(i64, i64, u64)], norms: &[u64], b2: u64,
    last: usize, pn: u64, prod: G, idx: &mut Vec<usize>,
    small: &[u32], nf: &mut Vec<(u64, u32)>, bcl: &mut Vec<G>,
    cands: &mut u64, tw: &mut u64, twf: &mut u64, hits: &Hits, units: &[G], kcap: i64,
) {
    if idx.len() >= 2 {
        proc2(classes, idx, prod, small, nf, bcl, cands, tw, twf, hits, units, kcap);
    }
    if idx.len() >= 4 { return; }
    for i in last + 1..norms.len() {
        if norms[i] > b2 / pn { break; }
        idx.push(i);
        dfs2(classes, norms, b2, i, pn * norms[i], mul(prod, (classes[i].0, classes[i].1)),
             idx, small, nf, bcl, cands, tw, twf, hits, units, kcap);
        idx.pop();
    }
}
fn proc2(
    classes: &[(i64, i64, u64)], aidx: &[usize], prod: G,
    small: &[u32], nf: &mut Vec<(u64, u32)>, bcl: &mut Vec<G>,
    cands: &mut u64, tw: &mut u64, twf: &mut u64, hits: &Hits, units: &[G], kcap: i64,
) {
    let k = aidx.len();
    let nu = units.len() as u64;
    let cofs: Vec<G> = aidx.iter().map(|&j| div_exact(prod, (classes[j].0, classes[j].1)).unwrap()).collect();
    let total = nu.pow(k as u32 - 1);
    if total > 1 << 14 { return; }
    for code in 0..total {
        *cands += 1;
        let mut d = cofs[0];
        let mut c = code;
        for t in 1..k {
            let w = mul(cofs[t], units[(c % nu) as usize]);
            d = (d.0 + w.0, d.1 + w.1);
            c /= nu;
        }
        if d == (0, 0) { continue; }
        if canon(d) == canon(prod) {
            *twf += 1;
            hits.report(&format!("*** Z[sqrt2] TWISTED FIXED: {:?} code {} ***",
                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), code));
            continue;
        }
        let nd = norm(d).unsigned_abs();
        if nd <= 1 { continue; }
        factorize(nd, small, nf);
        if !classify(d, nf, bcl) || bcl.len() < 2 { continue; }
        let terms: Vec<G> = bcl.iter().map(|&z| div_exact(d, z).unwrap()).collect();
        if terms.len() > 7 { continue; }
        // pruning data: moduli in both embeddings, max unit stretch eps^K
        let stretch = (1.0 + std::f64::consts::SQRT_2).powi(kcap as i32);
        let m1: Vec<f64> = terms.iter().map(|&t| emb(t).0.abs()).collect();
        let m2: Vec<f64> = terms.iter().map(|&t| emb(t).1.abs()).collect();
        let mut s1 = vec![0.0; terms.len() + 1];
        let mut s2 = vec![0.0; terms.len() + 1];
        for i in (0..terms.len()).rev() {
            s1[i] = s1[i + 1] + m1[i] * stretch;
            s2[i] = s2[i + 1] + m2[i] * stretch;
        }
        if close(&terms, &s1, &s2, 0, (0, 0), prod, units) {
            *tw += 1;
            hits.report(&format!(
                "*** Z[sqrt2] TWISTED 2-CYCLE: a-classes {:?} code {} | b=a'={:?} b-classes {:?} | closes exactly ***",
                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), code, d, bcl));
        }
    }
}
fn close(terms: &[G], s1: &[f64], s2: &[f64], i: usize, part: G, target: G, units: &[G]) -> bool {
    if i == terms.len() { return part == target; }
    let (p1, p2) = emb(part);
    let (t1, t2) = emb(target);
    if (t1 - p1).abs() > s1[i] + 1e-6 { return false; }
    if (t2 - p2).abs() > s2[i] + 1e-6 { return false; }
    for &u in units {
        let w = mul(terms[i], u);
        if close(terms, s1, s2, i + 1, (part.0 + w.0, part.1 + w.1), target, units) { return true; }
    }
    false
}
fn simple_primes(limit: u32) -> Vec<u32> {
    let lim = limit as usize;
    let mut comp = vec![false; lim + 1]; let mut v = Vec::new();
    for i in 2..=lim { if !comp[i] { v.push(i as u32); let mut j = i * i; while j <= lim { comp[j] = true; j += i; } } }
    v
}
fn bit_sieve(limit: u64) -> Vec<u64> {
    let words = ((limit + 1) / 128 + 2) as usize;
    let mut s = vec![0u64; words];
    let mut i = 3u64;
    while i * i <= limit {
        if s[(i >> 1) as usize / 64] & (1 << ((i >> 1) % 64)) == 0 {
            let mut j = i * i;
            while j <= limit { s[(j >> 1) as usize / 64] |= 1 << ((j >> 1) % 64); j += 2 * i; }
        }
        i += 2;
    }
    s
}
fn sieve_is_prime(s: &[u64], p: u64) -> bool {
    if p == 2 { return true; }
    if p < 2 || p % 2 == 0 { return false; }
    s[(p >> 1) as usize / 64] & (1 << ((p >> 1) % 64)) == 0
}
