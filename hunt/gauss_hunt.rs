// gauss_hunt.rs — search for 2-cycles of the arithmetic derivative over Z[i], up to units.
//
// Setup: canonical Gaussian primes = first-quadrant representatives (Re>0, Im>=0):
//   (1,1) above 2;  (x,y),(y,x) above p = x^2+y^2 for p = 1 mod 4;  (p,0) for p = 3 mod 4 (norm p^2).
// For a squarefree product a = prod pi_i of distinct canonical primes, the derivative is the
// cofactor sum a' = sum_j prod_{i!=j} pi_i  (i.e. pi' = 1, Leibniz).  We hunt:
//   MODE 1 (deep):     a' ~ b and b' ~ a up to units, over all squarefree a with Norm(a) <= B.
//   MODE 2 (twisted):  pi' = u_pi (any unit, per prime) — exact cycles a' = b, b' = a — over
//                      Norm(a) <= B2, omega <= 5.  This is the fullest archimedean freedom of Z[i].
// Also reported (each would be a new object): fixed points up to units (a' ~ a), zero-derivative
// elements (a' = 0: an exact vanishing of complex mass), unit-derivative composites (a' ~ 1).
//
// Rationale (paper, Remark "ordered-archimedean"): the 59-prime barrier of Erdos #307 is AM-GM on
// positive real masses; over Z[i] masses are complex and |sum 1/pi| > 1 needs only 3 primes, so the
// barrier has NO analogue here and small cycles are not excluded.  Any hit is a first-of-its-kind.
//
// Usage:   ./gauss_hunt [B] [B2] [threads]      defaults: B=200000000, B2=4000000, threads=auto
// Hits and notable objects are appended to gauss_hits.txt with full certificates.

use std::env;
use std::fs::OpenOptions;
use std::io::Write as IoWrite;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

type G = (i64, i64);

#[inline]
fn gmul(a: G, b: G) -> G { (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0) }
#[inline]
fn gadd(a: G, b: G) -> G { (a.0 + b.0, a.1 + b.1) }
#[inline]
fn gnorm(a: G) -> u64 { (a.0 * a.0 + a.1 * a.1) as u64 }
#[inline]
fn mul_i(a: G, k: u8) -> G {
    match k & 3 { 0 => a, 1 => (-a.1, a.0), 2 => (-a.0, -a.1), _ => (a.1, -a.0) }
}
fn canon(z: G) -> G {
    let mut w = z;
    for _ in 0..4 {
        if w.0 > 0 && w.1 >= 0 { return w; }
        w = (-w.1, w.0);
    }
    (0, 0)
}
fn gdiv_exact(a: G, b: G) -> Option<G> {
    let n = gnorm(b) as i64;
    let x = a.0 * b.0 + a.1 * b.1;
    let y = a.1 * b.0 - a.0 * b.1;
    if x % n != 0 || y % n != 0 { None } else { Some((x / n, y / n)) }
}

// ---------- u64 arithmetic ----------
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
fn isqrt(n: u64) -> u64 {
    let mut x = (n as f64).sqrt() as u64;
    while x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}
// Brent-Pollard rho
fn rho(n: u64) -> u64 {
    if n % 2 == 0 { return 2; }
    let mut c = 1u64;
    loop {
        let f = |x: u64| (mulmod(x, x, n) + c) % n;
        let (mut x, mut y, mut d) = (2u64, 2u64, 1u64);
        let mut count = 0u64;
        while d == 1 {
            x = f(x); y = f(f(y));
            d = gcd(x.abs_diff(y), n);
            count += 1;
            if count > 2_000_000 { break; }
        }
        if d != n && d != 1 { return d; }
        c += 1;
    }
}
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
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
        let mut stack = vec![n];
        while let Some(m) = stack.pop() {
            if is_prime(m) {
                if let Some(slot) = out.iter_mut().find(|(q, _)| *q == m) { slot.1 += 1; }
                else { out.push((m, 1)); }
            } else {
                let d = rho(m);
                stack.push(d); stack.push(m / d);
            }
        }
    }
    out.sort();
}

// ---------- Cornacchia: p = x^2 + y^2 for p = 1 mod 4 ----------
fn sqrt_m1(p: u64) -> u64 {
    for g in [2u64, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 23] {
        let r = powmod(g, (p - 1) / 4, p);
        if mulmod(r, r, p) == p - 1 { return r; }
    }
    let mut g = 24u64;
    loop {
        let r = powmod(g, (p - 1) / 4, p);
        if mulmod(r, r, p) == p - 1 { return r; }
        g += 1;
    }
}
fn cornacchia(p: u64) -> (u64, u64) {
    let r = sqrt_m1(p);
    let (mut a, mut b) = (p, r);
    while b * b > p { let t = a % b; a = b; b = t; }
    let x = b;
    let y = isqrt(p - x * x);
    debug_assert!(x * x + y * y == p);
    (x, y)
}

// classify d into canonical Gaussian prime classes; None if not squarefree in Z[i]
fn gclassify(d: G, nf: &[(u64, u32)], out: &mut Vec<G>) -> bool {
    out.clear();
    for &(q, e) in nf {
        if q == 2 {
            if e >= 2 { return false; }
            out.push((1, 1));
        } else if q % 4 == 3 {
            if e % 2 == 1 || e > 2 { return false; }
            out.push((q as i64, 0));
        } else {
            if e >= 3 { return false; }
            let (x, y) = cornacchia(q);
            let (x, y) = (x as i64, y as i64);
            if e == 2 {
                if d.0 % q as i64 == 0 && d.1 % q as i64 == 0 {
                    out.push((x, y)); out.push((y, x));
                } else { return false; } // pi^2 or pibar^2
            } else {
                if gdiv_exact(d, (x, y)).is_some() { out.push((x, y)); }
                else { out.push((y, x)); }
            }
        }
    }
    // round-trip: product of classes must be an associate of d
    let mut p: G = (1, 0);
    for &z in out.iter() { p = gmul(p, z); }
    canon(p) == canon(d)
}

struct Hits {
    file: Mutex<std::fs::File>,
}
impl Hits {
    fn report(&self, line: &str) {
        println!("\n{}", line);
        let mut f = self.file.lock().unwrap();
        let _ = writeln!(f, "{}", line);
    }
}

fn fmt_hms(s: u64) -> String { format!("{:02}:{:02}:{:02}", s / 3600, (s / 60) % 60, s % 60) }

fn main() {
    let args: Vec<String> = env::args().collect();
    let b: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(200_000_000);
    let b2: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(4_000_000);
    let nthreads: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
        std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4)
    });

    // ---------- self-tests ----------
    assert_eq!(canon((0, 3)), (3, 0));
    assert_eq!(canon((-2, 5)), (5, 2));
    assert_eq!(cornacchia(5), (2, 1));
    assert_eq!(cornacchia(13), (3, 2));
    assert_eq!(cornacchia(17), (4, 1));
    {
        // classification round-trip on a constructed product (1+i)(2+i)(3+2i)(4+i)
        let cls = [(1i64, 1i64), (2, 1), (3, 2), (4, 1)];
        let mut v: G = (1, 0);
        for &z in &cls { v = gmul(v, z); }
        let mut nf = Vec::new();
        let small: Vec<u32> = simple_primes(4096);
        factorize(gnorm(v), &small, &mut nf);
        let mut got = Vec::new();
        assert!(gclassify(v, &nf, &mut got));
        let mut want: Vec<G> = cls.to_vec();
        want.sort(); got.sort();
        assert_eq!(got, want);
    }
    println!("self-test OK (canon, Cornacchia, Z[i] factorisation round-trip)");
    println!("config: B={}  B2={}  threads={}", b, b2, nthreads);

    let small: Vec<u32> = simple_primes(4096);
    let t0 = Instant::now();

    // ---------- build canonical Gaussian prime classes with norm <= B/2 ----------
    let plim = (b / 2).max(8);
    let sieve = bit_sieve(plim);
    let mut classes: Vec<(i64, i64, u64)> = Vec::new();
    classes.push((1, 1, 2));
    let mut p = 3u64;
    while p <= plim {
        if sieve_is_prime(&sieve, p) {
            if p % 4 == 1 {
                let (x, y) = cornacchia(p);
                classes.push((x as i64, y as i64, p));
                classes.push((y as i64, x as i64, p));
            } else if p * p <= plim {
                classes.push((p as i64, 0, p * p));
            }
        }
        p += 2;
    }
    classes.sort_by_key(|c| (c.2, c.0));
    let norms: Vec<u64> = classes.iter().map(|c| c.2).collect();
    let l = classes.len();
    println!("Gaussian prime classes with norm <= {}: {} ({})", plim, l, fmt_hms(t0.elapsed().as_secs()));

    // ---------- work units: (i0, block of i1) ----------
    const BLK: u64 = 4096;
    let mut blocks_per_i0: Vec<u64> = Vec::with_capacity(l);
    for i0 in 0..l {
        let cap = b / norms[i0];
        let hi = norms.partition_point(|&n| n <= cap);
        let cnt = hi.saturating_sub(i0 + 1) as u64;
        blocks_per_i0.push((cnt + BLK - 1) / BLK);
    }
    let mut cum: Vec<u64> = Vec::with_capacity(l + 1);
    let mut acc = 0u64;
    cum.push(0);
    for i0 in 0..l { acc += blocks_per_i0[i0]; cum.push(acc); }
    let total_units = acc;

    let hits = Hits { file: Mutex::new(OpenOptions::new().create(true).append(true).open("gauss_hits.txt").unwrap()) };

    // ---------- counting pass (exact totals for ETA) ----------
    let next_unit = AtomicU64::new(0);
    let counted = AtomicU64::new(0);
    let units_done = AtomicU64::new(0);
    std::thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| {
                let mut idx: Vec<usize> = Vec::new();
                loop {
                    let u = next_unit.fetch_add(1, Ordering::Relaxed);
                    if u >= total_units { break; }
                    let i0 = cum.partition_point(|&c| c <= u) - 1;
                    let blk = u - cum[i0];
                    let mut local = 0u64;
                    run_block(&classes, &norms, b, i0, blk, BLK, &mut idx, &mut |_, _| { local += 1; });
                    counted.fetch_add(local, Ordering::Relaxed);
                    units_done.fetch_add(1, Ordering::Relaxed);
                }
            });
        }
    });
    let total_cands = counted.load(Ordering::Relaxed);
    println!("Mode 1 candidate count: {} squarefree a (omega>=2, Norm<= {})  [{}]",
             total_cands, b, fmt_hms(t0.elapsed().as_secs()));

    // ---------- Mode 1 processing pass ----------
    let next_unit2 = AtomicU64::new(0);
    let done_c = AtomicU64::new(0);
    let n_zero = AtomicU64::new(0);
    let n_unitd = AtomicU64::new(0);
    let n_fixed = AtomicU64::new(0);
    let n_cycle = AtomicU64::new(0);
    let n_rtfail = AtomicU64::new(0);
    let n_sfpart = AtomicU64::new(0);
    let t1 = Instant::now();
    std::thread::scope(|sc| {
        // progress monitor
        sc.spawn(|| {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(1000));
                let dc = done_c.load(Ordering::Relaxed);
                if dc >= total_cands { break; }
                let frac = dc as f64 / total_cands as f64;
                let el = t1.elapsed().as_secs_f64();
                let eta = if frac > 1e-9 { el / frac - el } else { 0.0 };
                eprint!("\r[Mode 1] {:5.1}% | {}/{} | {:7.2} Mc/s | elapsed {} | ETA {} | cyc={} fix={} zero={} unit'={} rt-fail={}   ",
                    frac * 100.0, dc, total_cands, dc as f64 / el / 1e6,
                    fmt_hms(el as u64), fmt_hms(eta as u64),
                    n_cycle.load(Ordering::Relaxed), n_fixed.load(Ordering::Relaxed),
                    n_zero.load(Ordering::Relaxed), n_unitd.load(Ordering::Relaxed),
                    n_rtfail.load(Ordering::Relaxed));
            }
            eprintln!();
        });
        for _ in 0..nthreads {
            sc.spawn(|| {
                let mut idx: Vec<usize> = Vec::new();
                let mut nf: Vec<(u64, u32)> = Vec::new();
                let mut bcl: Vec<G> = Vec::new();
                let mut local = 0u64;
                loop {
                    let u = next_unit2.fetch_add(1, Ordering::Relaxed);
                    if u >= total_units { break; }
                    let i0 = cum.partition_point(|&c| c <= u) - 1;
                    let blk = u - cum[i0];
                    run_block(&classes, &norms, b, i0, blk, BLK, &mut idx, &mut |aidx, prod| {
                        local += 1;
                        if local & 0xFFF == 0 { done_c.fetch_add(0x1000, Ordering::Relaxed); }
                        // cofactor sum
                        let mut d: G = (0, 0);
                        for &j in aidx {
                            let z = (classes[j].0, classes[j].1);
                            d = gadd(d, gdiv_exact(prod, z).unwrap());
                        }
                        if d == (0, 0) {
                            n_zero.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** ZERO-DERIVATIVE a'=0: classes {:?} (exact vanishing complex mass) ***",
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>()));
                            return;
                        }
                        let nd = gnorm(d);
                        if nd == 1 {
                            n_unitd.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** UNIT-DERIVATIVE a'~1: classes {:?} ***",
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>()));
                            return;
                        }
                        if canon(d) == canon(prod) {
                            n_fixed.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!("*** FIXED POINT a'~a: classes {:?}, a'={:?} ***",
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), d));
                            return;
                        }
                        factorize(nd, &small, &mut nf);
                        if !gclassify(d, &nf, &mut bcl) {
                            // not squarefree partner (or round-trip failure: distinguish)
                            let mut pchk: G = (1, 0);
                            for &z in bcl.iter() { pchk = gmul(pchk, z); }
                            if !bcl.is_empty() && gnorm(pchk) == nd && canon(pchk) != canon(d) {
                                n_rtfail.fetch_add(1, Ordering::Relaxed);
                            }
                            return;
                        }
                        if bcl.len() < 2 { return; }
                        n_sfpart.fetch_add(1, Ordering::Relaxed);
                        let mut e: G = (0, 0);
                        for &z in bcl.iter() { e = gadd(e, gdiv_exact(d, z).unwrap()); }
                        if e != (0, 0) && canon(e) == canon(prod) {
                            n_cycle.fetch_add(1, Ordering::Relaxed);
                            hits.report(&format!(
                                "*** 2-CYCLE (up to units) FOUND: a-classes {:?} (a={:?}), b=a'={:?}, b-classes {:?}, b'={:?} ~ a  VERIFY: canon(b')={:?} canon(a)={:?} ***",
                                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(),
                                prod, d, bcl, e, canon(e), canon(prod)));
                        }
                    });
                    units_done.fetch_add(1, Ordering::Relaxed);
                }
                done_c.fetch_add(local & 0xFFF, Ordering::Relaxed);
            });
        }
        // ensure monitor exits even on rounding
        sc.spawn(|| {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(500));
                if next_unit2.load(Ordering::Relaxed) >= total_units + nthreads as u64 {
                    done_c.store(total_cands, Ordering::Relaxed);
                    break;
                }
            }
        });
    });
    done_c.store(total_cands, Ordering::Relaxed);
    println!("Mode 1 complete: {} candidates, sf-partners {}, cycles {}, fixed {}, zero-deriv {}, unit-deriv {}, roundtrip-failures {}  [{}]",
        total_cands, n_sfpart.load(Ordering::Relaxed), n_cycle.load(Ordering::Relaxed),
        n_fixed.load(Ordering::Relaxed), n_zero.load(Ordering::Relaxed),
        n_unitd.load(Ordering::Relaxed), n_rtfail.load(Ordering::Relaxed),
        fmt_hms(t1.elapsed().as_secs()));

    // ---------- Mode 2: twisted derivatives (pi' = unit), exact cycles ----------
    if b2 >= 4 {
        let t2 = Instant::now();
        let mut idx: Vec<usize> = Vec::new();
        let mut nf: Vec<(u64, u32)> = Vec::new();
        let mut bcl: Vec<G> = Vec::new();
        let mut tw_cyc = 0u64; let mut tw_fix = 0u64; let mut cands2 = 0u64;
        let lim2 = norms.partition_point(|&n| n <= b2 / 2);
        let mut stack: Vec<(usize, u64, G)> = Vec::new();
        // simple sequential DFS (B2 is small)
        for i0 in 0..lim2 {
            stack.clear();
            idx.clear();
            idx.push(i0);
            dfs_mode2(&classes, &norms, b2, i0, norms[i0],
                      (classes[i0].0, classes[i0].1), &mut idx,
                      &small, &mut nf, &mut bcl, &mut cands2, &mut tw_cyc, &mut tw_fix, &hits);
            if i0 % 50 == 0 {
                eprint!("\r[Mode 2] class {}/{} | cands {} | twisted-cycles {} fixed {}   ",
                    i0, lim2, cands2, tw_cyc, tw_fix);
            }
        }
        eprintln!();
        println!("Mode 2 complete: {} (candidate, unit-vector) pairs over Norm<={} omega<=5; twisted cycles {}, twisted fixed {}  [{}]",
            cands2, b2, tw_cyc, tw_fix, fmt_hms(t2.elapsed().as_secs()));
    }

    println!("\n================== SUMMARY ==================");
    println!("Mode 1: all squarefree a over Z[i], omega>=2, Norm(a) <= {}, partner by full factorisation", b);
    println!("Mode 2: all unit-twisted derivatives (pi'=unit), Norm(a) <= {}, omega <= 5", b2);
    let c = n_cycle.load(Ordering::Relaxed);
    if c == 0 {
        println!("no Gaussian 2-cycle found in the covered region (the ordered-archimedean question stays open).");
    } else {
        println!("!!! {} cycles found — check gauss_hits.txt; each is a first-of-its-kind object !!!", c);
    }
    println!("total wall time {}", fmt_hms(t0.elapsed().as_secs()));
}

// enumerate: all subsets with min index i0, second index in block blk, extended arbitrarily
fn run_block<F: FnMut(&[usize], G)>(
    classes: &[(i64, i64, u64)], norms: &[u64], b: u64,
    i0: usize, blk: u64, blksz: u64, idx: &mut Vec<usize>, f: &mut F,
) {
    let n0 = norms[i0];
    let z0 = (classes[i0].0, classes[i0].1);
    let start = i0 + 1 + (blk * blksz) as usize;
    let end = (i0 + 1 + ((blk + 1) * blksz) as usize).min(norms.len());
    idx.clear();
    idx.push(i0);
    for i1 in start..end {
        if norms[i1] > b / n0 { break; }
        let nn = n0 * norms[i1];
        let z1 = (classes[i1].0, classes[i1].1);
        let pp = gmul(z0, z1);
        idx.push(i1);
        f(idx, pp);
        extend(classes, norms, b, i1 + 1, nn, pp, idx, f);
        idx.pop();
    }
}
fn extend<F: FnMut(&[usize], G)>(
    classes: &[(i64, i64, u64)], norms: &[u64], b: u64,
    start: usize, pn: u64, prod: G, idx: &mut Vec<usize>, f: &mut F,
) {
    for i in start..norms.len() {
        if norms[i] > b / pn { break; }
        let z = (classes[i].0, classes[i].1);
        let np = gmul(prod, z);
        idx.push(i);
        f(idx, np);
        extend(classes, norms, b, i + 1, pn * norms[i], np, idx, f);
        idx.pop();
    }
}

// Mode 2 recursive enumeration + twisted processing
fn dfs_mode2(
    classes: &[(i64, i64, u64)], norms: &[u64], b2: u64,
    last: usize, pn: u64, prod: G, idx: &mut Vec<usize>,
    small: &[u32], nf: &mut Vec<(u64, u32)>, bcl: &mut Vec<G>,
    cands: &mut u64, tw_cyc: &mut u64, tw_fix: &mut u64, hits: &Hits,
) {
    if idx.len() >= 2 {
        process_twisted(classes, idx, prod, small, nf, bcl, cands, tw_cyc, tw_fix, hits);
    }
    if idx.len() >= 5 { return; }
    for i in last + 1..norms.len() {
        if norms[i] > b2 / pn { break; }
        let z = (classes[i].0, classes[i].1);
        idx.push(i);
        dfs_mode2(classes, norms, b2, i, pn * norms[i], gmul(prod, z), idx,
                  small, nf, bcl, cands, tw_cyc, tw_fix, hits);
        idx.pop();
    }
}
fn process_twisted(
    classes: &[(i64, i64, u64)], aidx: &[usize], prod: G,
    small: &[u32], nf: &mut Vec<(u64, u32)>, bcl: &mut Vec<G>,
    cands: &mut u64, tw_cyc: &mut u64, tw_fix: &mut u64, hits: &Hits,
) {
    let k = aidx.len();
    let cofs: Vec<G> = aidx.iter()
        .map(|&j| gdiv_exact(prod, (classes[j].0, classes[j].1)).unwrap()).collect();
    let nvec = 4u32.pow(k as u32 - 1);
    for code in 0..nvec {
        *cands += 1;
        let mut d = cofs[0];
        let mut c = code;
        for t in 1..k {
            d = gadd(d, mul_i(cofs[t], (c & 3) as u8));
            c >>= 2;
        }
        if d == (0, 0) { continue; }
        if canon(d) == canon(prod) {
            *tw_fix += 1;
            hits.report(&format!("*** TWISTED FIXED POINT: a-classes {:?} units-code {} a'={:?} ~ a ***",
                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), code, d));
            continue;
        }
        let nd = gnorm(d);
        if nd <= 1 { continue; }
        factorize(nd, small, nf);
        if !gclassify(d, nf, bcl) || bcl.len() < 2 { continue; }
        // need units v: sum v_r (d/r) == prod exactly
        let terms: Vec<G> = bcl.iter().map(|&z| gdiv_exact(d, z).unwrap()).collect();
        let mods: Vec<f64> = terms.iter().map(|&t| (gnorm(t) as f64).sqrt()).collect();
        let mut suffix: Vec<f64> = vec![0.0; terms.len() + 1];
        for i in (0..terms.len()).rev() { suffix[i] = suffix[i + 1] + mods[i]; }
        if close_exact(&terms, &suffix, 0, (0, 0), prod) {
            *tw_cyc += 1;
            hits.report(&format!(
                "*** TWISTED 2-CYCLE: a-classes {:?} units-code {} | b=a'={:?} b-classes {:?} | closing units exist: b'=a exactly ***",
                aidx.iter().map(|&j| (classes[j].0, classes[j].1)).collect::<Vec<_>>(), code, d, bcl));
        }
    }
}
fn close_exact(terms: &[G], suffix: &[f64], i: usize, partial: G, target: G) -> bool {
    if i == terms.len() { return partial == target; }
    let dx = (target.0 - partial.0) as f64;
    let dy = (target.1 - partial.1) as f64;
    if (dx * dx + dy * dy).sqrt() > suffix[i] + 1e-6 { return false; }
    for u in 0..4u8 {
        if close_exact(terms, suffix, i + 1, gadd(partial, mul_i(terms[i], u)), target) {
            return true;
        }
    }
    false
}

// ---------- small helpers ----------
fn simple_primes(limit: u32) -> Vec<u32> {
    let lim = limit as usize;
    let mut comp = vec![false; lim + 1];
    let mut out = Vec::new();
    for i in 2..=lim {
        if !comp[i] { out.push(i as u32); let mut j = i * i; while j <= lim { comp[j] = true; j += i; } }
    }
    out
}
fn bit_sieve(limit: u64) -> Vec<u64> {
    let words = ((limit + 1) / 128 + 1) as usize;
    let mut s = vec![0u64; words]; // bit set = composite, odd numbers only: bit k <-> 2k+1
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
