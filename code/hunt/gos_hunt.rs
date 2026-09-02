// gos_hunt.rs — hunt for members of the mu-Sondow lines mu = -145 and mu = +673
// (the two open instances of Conjecture 1(ii) of Grau--Oller-Marcen--Sadornil,
//  "On mu-Sondow numbers", arXiv:2111.14211; verified there only for n <= 10^10).
//
// Quotient-one dictionary (n squarefree, delta(n) = n' - n with n' the arithmetic derivative):
//   n in S_{-145}  <=>  delta(n) = +145      (line n' = n + 145)
//   n in S_{+673}  <=>  delta(n) = -673      (line n' = n - 673)
// Child rule (delta(Mp) = p*delta(M) + M for prime p not dividing M, M squarefree):
//   parent M with delta(M) = -e  breeds  +145-member M*p with p = (M-145)/e   (M > 145)
//                                breeds  -673-member M*p with p = (M+673)/e
//
// PHASE A: all squarefree M <= B0: direct membership + ALL generation-1 children (reach ~B0^2).
// PHASE B: depth-2 tree: parents M <= B1, intermediate prime q with e2 = q*e - M in [1, J],
//          then the same closing rules at the grandchild (reach ~(B1*J-ish)^2), plus the
//          direct check e2 == 673 (the node M*q itself is then a -673 member).
//
// Usage:  ./gos_hunt [B0] [B1] [J] [threads]
// Defaults: B0=1e9, B1=2e7, J=50000, threads=auto.
// Any hit is printed with a full certificate and appended to gos_hits.txt.

use std::env;
use std::fs::OpenOptions;
use std::io::Write as IoWrite;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

const SEG: u64 = 1 << 20;

// ---------- arithmetic ----------
fn mulmod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}
fn powmod(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64;
    a %= m;
    while e > 0 {
        if e & 1 == 1 { r = mulmod(r, a, m); }
        a = mulmod(a, a, m);
        e >>= 1;
    }
    r
}
fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 { return n == p; }
    }
    let mut d = n - 1;
    let mut s = 0u32;
    while d & 1 == 0 { d >>= 1; s += 1; }
    'witness: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..s - 1 {
            x = mulmod(x, x, n);
            if x == n - 1 { continue 'witness; }
        }
        return false;
    }
    true
}
fn simple_sieve(limit: u64) -> Vec<u64> {
    let lim = limit as usize;
    let mut comp = vec![false; lim + 1];
    let mut primes = Vec::new();
    for i in 2..=lim {
        if !comp[i] {
            primes.push(i as u64);
            let mut j = i * i;
            while j <= lim { comp[j] = true; j += i; }
        }
    }
    primes
}
// trial-division factor list (certificates only; n squarefree expected)
fn factor_small(mut n: u64) -> Vec<u64> {
    let mut f = Vec::new();
    let mut p = 2u64;
    while p * p <= n {
        if n % p == 0 {
            f.push(p);
            while n % p == 0 { n /= p; }
        }
        p += 1;
    }
    if n > 1 { f.push(n); }
    f
}
fn delta_check(n: u64) -> Option<i64> {
    // returns delta(n) for squarefree n, None if not squarefree
    let f = factor_small(n);
    let prod: u64 = f.iter().product();
    if prod != n { return None; } // a repeated prime factor was divided out
    let der: u64 = f.iter().map(|&p| n / p).sum();
    Some(der as i64 - n as i64)
}

// ---------- hit certificate ----------
fn certify_and_report(tag: &str, factors: &[u64], mu: i64, log: &Mutex<std::fs::File>) {
    let mut nn: u128 = 1;
    for &f in factors { nn *= f as u128; }
    let der: u128 = factors.iter().map(|&f| nn / f as u128).sum();
    let want = (nn as i128) - (mu as i128);
    let ok = (der as i128) == want;
    let line = format!(
        "*** HIT [{}] mu={}  N={}  factors={:?}  N'={}  N-mu={}  CERTIFICATE {} ***",
        tag, mu, nn, factors, der, want, if ok { "VALID" } else { "INVALID -- REJECT" }
    );
    println!("\n{}", line);
    let mut fh = log.lock().unwrap();
    let _ = writeln!(fh, "{}", line);
}

struct Counters {
    seg_done: AtomicU64,
    sf_count: AtomicU64,
    minus_parents: AtomicU64,
    cand_p: AtomicU64,
    hits: AtomicU64,
}

// ---------- the per-segment squarefree-derivative sieve ----------
// calls `visit(n, delta)` for every squarefree n in [lo, hi]
fn sieve_segment<F: FnMut(u64, i64)>(
    lo: u64, hi: u64, primes: &[u64],
    rem: &mut Vec<u64>, der: &mut Vec<u64>, dead: &mut Vec<bool>,
    visit: &mut F,
) {
    let len = (hi - lo + 1) as usize;
    rem.clear(); rem.resize(len, 0);
    der.clear(); der.resize(len, 0);
    dead.clear(); dead.resize(len, false);
    for i in 0..len { rem[i] = lo + i as u64; }
    for &p in primes {
        if p * p > hi { break; }
        let mut k = (lo + p - 1) / p;
        if k < 1 { k = 1; }
        let mut np = k * p;
        while np <= hi {
            let idx = (np - lo) as usize;
            der[idx] += k;
            rem[idx] /= p;
            np += p; k += 1;
        }
        let p2 = p * p;
        let mut m2 = ((lo + p2 - 1) / p2) * p2;
        while m2 <= hi {
            dead[(m2 - lo) as usize] = true;
            m2 += p2;
        }
    }
    for i in 0..len {
        if dead[i] { continue; }
        let n = lo + i as u64;
        if n < 2 { continue; }
        let mut d = der[i];
        let rm = rem[i];
        if rm > 1 { d += n / rm; }
        visit(n, d as i64 - n as i64);
    }
}

fn fmt_hms(secs: u64) -> String {
    format!("{:02}:{:02}:{:02}", secs / 3600, (secs / 60) % 60, secs % 60)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let b0: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1_000_000_000);
    let b1: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(20_000_000);
    let j: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(50_000);
    let nthreads: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
        std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4)
    });
    assert!(b1 <= b0, "need B1 <= B0");

    // ---------- self-test ----------
    assert_eq!(delta_check(30), Some(1));
    assert_eq!(delta_check(6), Some(-1));
    assert_eq!(delta_check(1722), Some(1));
    assert_eq!(delta_check(47058), Some(-1));
    assert_eq!(delta_check(66198), Some(1));
    assert_eq!(delta_check(12), None); // not squarefree
    assert!(is_prime(47057) && is_prime(47059));
    for c in [679u64, 1661, 2479, 46913, 47731, 675] { assert!(!is_prime(c)); }
    println!("self-test OK (delta values, primality, known composite holdout routes)");
    println!("targets: mu=-145 (line n'=n+145) and mu=+673 (line n'=n-673), squarefree members");
    println!("config: B0={}  B1={}  J={}  threads={}", b0, b1, j, nthreads);

    let primes = simple_sieve((b0 as f64).sqrt() as u64 + 2);
    let log = Mutex::new(
        OpenOptions::new().create(true).append(true).open("gos_hits.txt").unwrap(),
    );
    let t0 = Instant::now();

    // ================= PHASE A =================
    let nsegs = b0 / SEG + 1;
    let ctr = Counters {
        seg_done: AtomicU64::new(0), sf_count: AtomicU64::new(0),
        minus_parents: AtomicU64::new(0), cand_p: AtomicU64::new(0),
        hits: AtomicU64::new(0),
    };
    let next_seg = AtomicU64::new(0);
    let done = AtomicBool::new(false);

    std::thread::scope(|scope| {
        // progress monitor (exits when all segments are done)
        scope.spawn(|| {
            while ctr.seg_done.load(Ordering::Relaxed) < nsegs {
                std::thread::sleep(std::time::Duration::from_millis(1000));
                let sd = ctr.seg_done.load(Ordering::Relaxed);
                let frac = sd as f64 / nsegs as f64;
                let el = t0.elapsed().as_secs_f64();
                let eta = if frac > 0.0 { el / frac - el } else { 0.0 };
                let rate = (sd * SEG) as f64 / el / 1e6;
                eprint!(
                    "\r[Phase A] {:5.1}% | seg {}/{} | {:6.1} Mn/s | elapsed {} | ETA {} | sf={} parents={} p-tests={} hits={}   ",
                    frac * 100.0, sd, nsegs, rate,
                    fmt_hms(el as u64), fmt_hms(eta as u64),
                    ctr.sf_count.load(Ordering::Relaxed),
                    ctr.minus_parents.load(Ordering::Relaxed),
                    ctr.cand_p.load(Ordering::Relaxed),
                    ctr.hits.load(Ordering::Relaxed)
                );
            }
            eprintln!();
        });
        // workers
        for _ in 0..nthreads {
            scope.spawn(|| {
                let mut rem = Vec::new(); let mut der = Vec::new(); let mut dead = Vec::new();
                loop {
                    let s = next_seg.fetch_add(1, Ordering::Relaxed);
                    if s >= nsegs { break; }
                    let lo = (s * SEG).max(2);
                    let hi = ((s + 1) * SEG - 1).min(b0);
                    if lo > hi { ctr.seg_done.fetch_add(1, Ordering::Relaxed); continue; }
                    let mut local_sf = 0u64; let mut local_par = 0u64;
                    sieve_segment(lo, hi, &primes, &mut rem, &mut der, &mut dead, &mut |n, dl| {
                        local_sf += 1;
                        // direct membership
                        if dl == 145 {
                            ctr.hits.fetch_add(1, Ordering::Relaxed);
                            certify_and_report("A-direct +145", &factor_small(n), -145, &log);
                        }
                        if dl == -673 {
                            ctr.hits.fetch_add(1, Ordering::Relaxed);
                            certify_and_report("A-direct -673", &factor_small(n), 673, &log);
                        }
                        if dl < 0 {
                            local_par += 1;
                            let e = (-dl) as u64;
                            // child on +145: p = (n-145)/e
                            if n > 145 && (n - 145) % e == 0 {
                                let p = (n - 145) / e;
                                if p >= 2 && !(p <= n && n % p == 0) {
                                    ctr.cand_p.fetch_add(1, Ordering::Relaxed);
                                    if is_prime(p) {
                                        ctr.hits.fetch_add(1, Ordering::Relaxed);
                                        let mut f = factor_small(n); f.push(p); f.sort();
                                        certify_and_report("A-gen1 +145", &f, -145, &log);
                                    }
                                }
                            }
                            // child on -673: p = (n+673)/e
                            if (n + 673) % e == 0 {
                                let p = (n + 673) / e;
                                if p >= 2 && !(p <= n && n % p == 0) {
                                    ctr.cand_p.fetch_add(1, Ordering::Relaxed);
                                    if is_prime(p) {
                                        ctr.hits.fetch_add(1, Ordering::Relaxed);
                                        let mut f = factor_small(n); f.push(p); f.sort();
                                        certify_and_report("A-gen1 -673", &f, 673, &log);
                                    }
                                }
                            }
                        } else if dl > 0 && n < 145 {
                            // plus-parent toy branch: p = (145-n)/g
                            let g = dl as u64;
                            if (145 - n) % g == 0 {
                                let p = (145 - n) / g;
                                if p >= 2 && n % p != 0 && is_prime(p) {
                                    ctr.hits.fetch_add(1, Ordering::Relaxed);
                                    let mut f = factor_small(n); f.push(p); f.sort();
                                    certify_and_report("A-gen1(+parent) +145", &f, -145, &log);
                                }
                            }
                        }
                    });
                    ctr.sf_count.fetch_add(local_sf, Ordering::Relaxed);
                    ctr.minus_parents.fetch_add(local_par, Ordering::Relaxed);
                    ctr.seg_done.fetch_add(1, Ordering::Relaxed);
                }
            });
        }
    });
    done.store(true, Ordering::Relaxed);
    let a_sf = ctr.sf_count.load(Ordering::Relaxed);
    println!(
        "\nPhase A complete: {} squarefree M <= {} scanned ({} minus-line parents, {} prime-tests, {} hits), {}",
        a_sf, b0,
        ctr.minus_parents.load(Ordering::Relaxed),
        ctr.cand_p.load(Ordering::Relaxed),
        ctr.hits.load(Ordering::Relaxed),
        fmt_hms(t0.elapsed().as_secs())
    );

    // ================= PHASE B =================
    let tb = Instant::now();
    let nsegs_b = b1 / SEG + 1;
    let next_seg_b = AtomicU64::new(0);
    let seg_done_b = AtomicU64::new(0);
    let qb_tests = AtomicU64::new(0);
    let gb_hits = AtomicU64::new(0);
    let done_b = AtomicBool::new(false);

    std::thread::scope(|scope| {
        scope.spawn(|| {
            while seg_done_b.load(Ordering::Relaxed) < nsegs_b {
                std::thread::sleep(std::time::Duration::from_millis(1000));
                let sd = seg_done_b.load(Ordering::Relaxed);
                let frac = sd as f64 / nsegs_b as f64;
                let el = tb.elapsed().as_secs_f64();
                let eta = if frac > 0.0 { el / frac - el } else { 0.0 };
                eprint!(
                    "\r[Phase B] {:5.1}% | seg {}/{} | elapsed {} | ETA {} | q-tests={} hits={}   ",
                    frac * 100.0, sd, nsegs_b,
                    fmt_hms(el as u64), fmt_hms(eta as u64),
                    qb_tests.load(Ordering::Relaxed), gb_hits.load(Ordering::Relaxed)
                );
            }
            eprintln!();
        });
        for _ in 0..nthreads {
            scope.spawn(|| {
                let mut rem = Vec::new(); let mut der = Vec::new(); let mut dead = Vec::new();
                loop {
                    let s = next_seg_b.fetch_add(1, Ordering::Relaxed);
                    if s >= nsegs_b { break; }
                    let lo = (s * SEG).max(2);
                    let hi = ((s + 1) * SEG - 1).min(b1);
                    if lo > hi { seg_done_b.fetch_add(1, Ordering::Relaxed); continue; }
                    let mut local_q = 0u64;
                    sieve_segment(lo, hi, &primes, &mut rem, &mut der, &mut dead, &mut |m, dl| {
                        if dl >= 0 { return; }
                        let e = (-dl) as u64;
                        // q in (M/e, (M+J)/e]  <=>  e2 = q*e - M in [1, J]
                        let mut q = m / e + 1;
                        if q < 2 { q = 2; }
                        let q_hi = (m + j) / e;
                        while q <= q_hi {
                            let e2 = q * e - m;
                            if e2 >= 1 && e2 <= j && m % q != 0 {
                                local_q += 1;
                                if is_prime(q) {
                                    let node2 = m as u128 * q as u128; // <= ~1e18 for defaults
                                    let node2_64 = node2 as u64;
                                    // node M*q itself on the -673 line?
                                    if e2 == 673 {
                                        gb_hits.fetch_add(1, Ordering::Relaxed);
                                        let mut f = factor_small(m); f.push(q); f.sort();
                                        certify_and_report("B-node -673", &f, 673, &log);
                                    }
                                    // grandchild +145: p = (Mq-145)/e2
                                    if node2_64 > 145 && (node2_64 - 145) % e2 == 0 {
                                        let p = (node2_64 - 145) / e2;
                                        if p >= 2 && p != q && m % if p <= m { p } else { 1 } != 0
                                            && is_prime(p)
                                        {
                                            gb_hits.fetch_add(1, Ordering::Relaxed);
                                            let mut f = factor_small(m); f.push(q); f.push(p); f.sort();
                                            certify_and_report("B-gen2 +145", &f, -145, &log);
                                        }
                                    }
                                    // grandchild -673: p = (Mq+673)/e2
                                    if (node2_64 + 673) % e2 == 0 {
                                        let p = (node2_64 + 673) / e2;
                                        if p >= 2 && p != q && m % if p <= m { p } else { 1 } != 0
                                            && is_prime(p)
                                        {
                                            gb_hits.fetch_add(1, Ordering::Relaxed);
                                            let mut f = factor_small(m); f.push(q); f.push(p); f.sort();
                                            certify_and_report("B-gen2 -673", &f, 673, &log);
                                        }
                                    }
                                }
                            }
                            q += 1;
                        }
                    });
                    qb_tests.fetch_add(local_q, Ordering::Relaxed);
                    seg_done_b.fetch_add(1, Ordering::Relaxed);
                }
            });
        }
    });
    done_b.store(true, Ordering::Relaxed);

    println!(
        "\nPhase B complete: parents M <= {}, intermediate cap J = {}, {} q-candidates, {} hits, {}",
        b1, j, qb_tests.load(Ordering::Relaxed), gb_hits.load(Ordering::Relaxed),
        fmt_hms(tb.elapsed().as_secs())
    );
    let total_hits = ctr.hits.load(Ordering::Relaxed) + gb_hits.load(Ordering::Relaxed);
    println!("\n================== SUMMARY ==================");
    println!("coverage: direct members <= {}; all gen-1 children of every squarefree parent <= {}", b0, b0);
    println!("          (children reach ~{:.1e}); depth-2 tree from parents <= {} with e2 <= {}", (b0 as f64).powi(2), b1, j);
    println!("total hits: {}", total_hits);
    if total_hits == 0 {
        println!("no member of S_-145 or S_673 found in the covered region: both GOS instances remain open.");
    } else {
        println!("!!! check gos_hits.txt: a VALID certificate settles a published open instance !!!");
    }
    println!("total wall time {}", fmt_hms(t0.elapsed().as_secs()));
}
