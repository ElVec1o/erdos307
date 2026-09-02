// stable_hunt.rs — hunt for CONJUGATION-STABLE twisted 2-cycles over Z[i], via their exact
// descent to Z.
//
// A conjugation-stable squarefree Gaussian integer is an associate of (1+i)^d * m with m an
// odd squarefree rational integer (split primes enter as whole conjugate pairs, inert primes
// and 1+i are self-conjugate).  A parity argument excludes d = 1 entirely (see check below),
// and with conjugation-equivariant units the twisted derivative descends to the Z-operator
//
//      D(m) = sum_{p|m, p=1 mod 4} t_p * (m/p)  +  sum_{q|m, q=3 mod 4} e_q * (m/q),
//
// where t_p in {±2x_p, ±2y_p} (p = x_p^2 + y_p^2) and e_q in {±1}.  A 2-cycle of D
// (D(m) = ±n, D(n) = ±m, consistently signed) IS a conjugation-stable twisted Gaussian
// 2-cycle, and the first such object would descend the Gaussian phenomenon to Z itself.
// Parity: D(m) is odd iff m has an ODD number of inert primes; both members need this.
//
// Unit dictionary per split prime: t=+2x <-> pi'=1, +2y <-> i, -2x <-> -1, -2y <-> -i.
//
// Usage:  ./stable_hunt [M] [W] [threads]     defaults M=100000000, W=8, threads=auto
// Coverage: all rational-sector cycles with a member m <= M, omega(m) <= W, unit-vector
// budget 2^16 per side.  Hits, fixed points (|D(m)|=m), and zero-derivative elements are
// certified and appended to stable_hits.txt.

use std::env;
use std::fs::OpenOptions;
use std::io::Write as IoWrite;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

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
        let mut cnt = 0u64;
        while d == 1 {
            x = f(x); y = f(f(y));
            d = gcd(x.abs_diff(y), n);
            cnt += 1;
            if cnt > 2_000_000 { break; }
        }
        if d != n && d != 1 { return d; }
        c += 1;
    }
}
fn isqrt(n: u64) -> u64 {
    let mut x = (n as f64).sqrt() as u64;
    while x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}
fn sqrt_m1(p: u64) -> u64 {
    let mut g = 2u64;
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
    let x = b; let y = isqrt(p - x * x);
    debug_assert!(x * x + y * y == p);
    (x, y)
}

// factor odd n; return Some(list of (prime, is_split, halves)) if squarefree, else None
fn factor_sf(n: u64, out: &mut Vec<(u64, bool, u64, u64)>) -> bool {
    out.clear();
    let mut m = n;
    for p in [3u64, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] {
        if p * p > m { break; }
        if m % p == 0 {
            m /= p;
            if m % p == 0 { return false; }
            push_prime(p, out);
        }
    }
    if m > 1 {
        let mut stack = vec![m];
        while let Some(v) = stack.pop() {
            if is_prime(v) {
                if out.iter().any(|&(q, _, _, _)| q == v) { return false; }
                push_prime(v, out);
            } else {
                let d = rho(v);
                if d == 0 || d == 1 || d == v { return false; }
                if (v / d) % d == 0 || gcd(d, v / d) != 1 { return false; } // repeated factor
                stack.push(d); stack.push(v / d);
            }
        }
    }
    out.sort();
    true
}
fn push_prime(p: u64, out: &mut Vec<(u64, bool, u64, u64)>) {
    if p % 4 == 1 {
        let (x, y) = cornacchia(p);
        out.push((p, true, 2 * x, 2 * y));
    } else {
        out.push((p, false, 1, 0));
    }
}

// D(m) for one unit-vector code; primes: (p, split, 2x, 2y).
// per split prime 2 bits: 0->+2x 1->+2y 2->-2x 3->-2y ; per inert 1 bit: 0->+1 1->-1
fn d_value(m: u64, pr: &[(u64, bool, u64, u64)], mut code: u64) -> i64 {
    let mut d: i64 = 0;
    for &(p, split, tx, ty) in pr {
        let cof = (m / p) as i64;
        if split {
            let c = code & 3; code >>= 2;
            let t = match c { 0 => tx as i64, 1 => ty as i64, 2 => -(tx as i64), _ => -(ty as i64) };
            d += t * cof;
        } else {
            let c = code & 1; code >>= 1;
            d += if c == 0 { cof } else { -cof };
        }
    }
    d
}
fn vec_count(pr: &[(u64, bool, u64, u64)]) -> u64 {
    let mut v = 1u64;
    for &(_, split, _, _) in pr { v *= if split { 4 } else { 2 }; if v > 1 << 20 { return v; } }
    v
}
fn unit_name(split: bool, c: u64) -> &'static str {
    if split { ["1", "i", "-1", "-i"][c as usize] } else { ["1", "-1"][c as usize] }
}

struct Hits { file: Mutex<std::fs::File> }
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
    let mlim: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(100_000_000);
    let wcap: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(8);
    let nthreads: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
        std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4)
    });
    const BUDGET: u64 = 1 << 16;

    // ---------- self-tests ----------
    assert_eq!(cornacchia(5), (2, 1));
    assert_eq!(cornacchia(13), (3, 2));
    {
        // D(15) with t_5=+4 (u=1), e_3=+1: 4*3 + 1*5 = 17 — matches the Z[i] computation
        // 15/3 + 15/(2+i) + 15/(2-i) = 5 + 3(2-i) + 3(2+i) = 5 + 12 = 17.
        let mut pr = Vec::new();
        assert!(factor_sf(15, &mut pr));
        // order sorted: [(3,inert),(5,split,4,2)]
        // code layout follows order: inert 3 first (1 bit), then split 5 (2 bits)
        let d = d_value(15, &pr, 0b00_0); // e_3=+1, t_5=+2x=+4
        assert_eq!(d, 17);
        let d2 = d_value(15, &pr, 0b01_1); // e_3=-1, t_5=+2y=+2
        assert_eq!(d2, 2 * 3 - 5);
    }
    println!("self-test OK (Cornacchia, descended operator D matches Z[i] computation)");
    println!("the (1+i)-sector is empty by parity; members need an ODD number of primes = 3 mod 4");
    println!("config: M={}  omega<={}  threads={}", mlim, wcap, nthreads);

    // ---------- odd prime list to M/3, with halves for split primes ----------
    let t0 = Instant::now();
    let plim = mlim / 3;
    let words = (plim / 128 + 2) as usize;
    let mut sieve = vec![0u64; words];
    {
        let mut i = 3u64;
        while i * i <= plim {
            if sieve[(i >> 1) as usize / 64] & (1 << ((i >> 1) % 64)) == 0 {
                let mut j = i * i;
                while j <= plim { sieve[(j >> 1) as usize / 64] |= 1 << ((j >> 1) % 64); j += 2 * i; }
            }
            i += 2;
        }
    }
    let mut primes: Vec<(u64, bool, u64, u64)> = Vec::new();
    let mut p = 3u64;
    while p <= plim {
        if sieve[(p >> 1) as usize / 64] & (1 << ((p >> 1) % 64)) == 0 {
            if p % 4 == 1 {
                let (x, y) = cornacchia(p);
                primes.push((p, true, 2 * x, 2 * y));
            } else {
                primes.push((p, false, 1, 0));
            }
        }
        p += 2;
    }
    let np = primes.len();
    println!("odd primes <= {}: {}  [{}]", plim, np, fmt_hms(t0.elapsed().as_secs()));

    // ---------- work units: (i0, block of i1) over first two prime indices ----------
    const BLK: u64 = 2048;
    let pvals: Vec<u64> = primes.iter().map(|t| t.0).collect();
    let mut cum: Vec<u64> = Vec::with_capacity(np + 1);
    let mut acc = 0u64;
    cum.push(0);
    for i0 in 0..np {
        let cap = mlim / pvals[i0];
        let hi = pvals.partition_point(|&q| q <= cap);
        let cnt = hi.saturating_sub(i0 + 1) as u64;
        acc += (cnt + BLK - 1) / BLK + 1; // +1: the singleton {p_i0} subtree marker
        cum.push(acc);
    }
    let total_units = acc;

    let hits = Hits { file: Mutex::new(OpenOptions::new().create(true).append(true).open("stable_hits.txt").unwrap()) };

    // counting pass (for ETA): number of (m, vector) pairs with r odd
    let next_u = AtomicU64::new(0);
    let counted = AtomicU64::new(0);
    std::thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| {
                let mut sel: Vec<usize> = Vec::new();
                loop {
                    let u = next_u.fetch_add(1, Ordering::Relaxed);
                    if u >= total_units { break; }
                    let i0 = cum.partition_point(|&c| c <= u) - 1;
                    let blk = u - cum[i0];
                    let mut local = 0u64;
                    run_unit(&primes, mlim, wcap, i0, blk, BLK, &mut sel, &mut |pr: &[(u64, bool, u64, u64)]| {
                        let r = pr.iter().filter(|t| !t.1).count();
                        if r % 2 == 1 && !(pr.len() == 1 && r == 1) {
                            let v = vec_count(pr);
                            if v <= BUDGET { local += v / 2; }
                        }
                    });
                    counted.fetch_add(local, Ordering::Relaxed);
                }
            });
        }
    });
    let total_work = counted.load(Ordering::Relaxed);
    println!("candidate (m, unit-vector) pairs (r odd, omega<={}, budget {}): {}  [{}]",
             wcap, BUDGET, total_work, fmt_hms(t0.elapsed().as_secs()));

    // ---------- main pass ----------
    let next_u2 = AtomicU64::new(0);
    let done_w = AtomicU64::new(0);
    let n_cyc = AtomicU64::new(0);
    let n_fix = AtomicU64::new(0);
    let n_zero = AtomicU64::new(0);
    let n_ret = AtomicU64::new(0);
    let t1 = Instant::now();
    std::thread::scope(|sc| {
        sc.spawn(|| {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(1000));
                let dw = done_w.load(Ordering::Relaxed);
                if dw >= total_work { break; }
                let frac = dw as f64 / total_work as f64;
                let el = t1.elapsed().as_secs_f64();
                let eta = if frac > 1e-9 { el / frac - el } else { 0.0 };
                eprint!("\r[stable] {:5.1}% | {}/{} | {:7.2} Mv/s | elapsed {} | ETA {} | cycles={} fixed={} zero={} returns={}   ",
                    frac * 100.0, dw, total_work, dw as f64 / el / 1e6,
                    fmt_hms(el as u64), fmt_hms(eta as u64),
                    n_cyc.load(Ordering::Relaxed), n_fix.load(Ordering::Relaxed),
                    n_zero.load(Ordering::Relaxed), n_ret.load(Ordering::Relaxed));
            }
            eprintln!();
        });
        for _ in 0..nthreads {
            sc.spawn(|| {
                let mut sel: Vec<usize> = Vec::new();
                let mut nf: Vec<(u64, bool, u64, u64)> = Vec::new();
                let mut local = 0u64;
                loop {
                    let u = next_u2.fetch_add(1, Ordering::Relaxed);
                    if u >= total_units { break; }
                    let i0 = cum.partition_point(|&c| c <= u) - 1;
                    let blk = u - cum[i0];
                    run_unit(&primes, mlim, wcap, i0, blk, BLK, &mut sel, &mut |pr: &[(u64, bool, u64, u64)]| {
                        let r = pr.iter().filter(|t| !t.1).count();
                        if r % 2 == 0 || (pr.len() == 1 && r == 1) { return; }
                        let v = vec_count(pr);
                        if v > BUDGET { return; }
                        let m: u64 = pr.iter().map(|t| t.0).product();
                        for code in 0..v / 2 {  // global negation: halve
                            local += 1;
                            if local & 0x3FFF == 0 { done_w.fetch_add(0x4000, Ordering::Relaxed); }
                            let d = d_value(m, pr, code);
                            if d == 0 {
                                n_zero.fetch_add(1, Ordering::Relaxed);
                                hits.report(&format!("*** ZERO D: m={} primes={:?} code={} ***", m, pr, code));
                                continue;
                            }
                            let n = d.unsigned_abs();
                            if n == m {
                                n_fix.fetch_add(1, Ordering::Relaxed);
                                hits.report(&format!("*** FIXED |D(m)|=m: m={} code={} D={} ***", m, code, d));
                                continue;
                            }
                            if n <= 1 || n % 2 == 0 { continue; }
                            // quick reject: n must have an odd number of inert primes too —
                            // cheap necessary test mod 4: D(n) odd requires it; defer to factoring.
                            if !factor_sf(n, &mut nf) { continue; }
                            let rn = nf.iter().filter(|t| !t.1).count();
                            if rn % 2 == 0 { continue; }
                            let vn = vec_count(&nf);
                            if vn > BUDGET { continue; }
                            n_ret.fetch_add(1, Ordering::Relaxed);
                            // return: need D(n) = -m if d<0... global sign free: test |D(n)| == m
                            for code2 in 0..vn {
                                let d2 = d_value(n, &nf, code2);
                                if d2.unsigned_abs() == m {
                                    // sign consistency: need D(b)=a with b=d: if d<0, effective
                                    // return derivative is -D(n); both signs are available, so
                                    // any |D(n)|=m closes a genuine cycle.
                                    n_cyc.fetch_add(1, Ordering::Relaxed);
                                    let aunits: Vec<String> = {
                                        let mut cc = code; let mut o = Vec::new();
                                        for &(_, sp, _, _) in pr.iter() {
                                            if sp { o.push(unit_name(true, cc & 3).to_string()); cc >>= 2; }
                                            else { o.push(unit_name(false, cc & 1).to_string()); cc >>= 1; }
                                        }
                                        o
                                    };
                                    let bunits: Vec<String> = {
                                        let mut cc = code2; let mut o = Vec::new();
                                        for &(_, sp, _, _) in nf.iter() {
                                            if sp { o.push(unit_name(true, cc & 3).to_string()); cc >>= 2; }
                                            else { o.push(unit_name(false, cc & 1).to_string()); cc >>= 1; }
                                        }
                                        o
                                    };
                                    hits.report(&format!(
                                        "*** CONJUGATION-STABLE 2-CYCLE (descends to Z): m={} primes={:?} units={:?} | D(m)={} | n={} primes={:?} units={:?} | D(n)={} -> |D(n)|=m  VERIFIED ***",
                                        m, pr.iter().map(|t| t.0).collect::<Vec<_>>(), aunits, d,
                                        n, nf.iter().map(|t| t.0).collect::<Vec<_>>(), bunits, d2));
                                    break;
                                }
                            }
                        }
                    });
                }
                done_w.fetch_add(local & 0x3FFF, Ordering::Relaxed);
            });
        }
        sc.spawn(|| {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(500));
                if next_u2.load(Ordering::Relaxed) >= total_units + nthreads as u64 {
                    done_w.store(total_work, Ordering::Relaxed);
                    break;
                }
            }
        });
    });
    done_w.store(total_work, Ordering::Relaxed);

    println!("\n================== SUMMARY ==================");
    println!("coverage: all conjugation-stable (rational-sector, equivariant) twisted 2-cycles over Z[i]");
    println!("          with a member m <= {}, omega(m) <= {}, unit budget {} per side", mlim, wcap, BUDGET);
    println!("          ((1+i)-sector empty by parity; members need an odd number of primes = 3 mod 4)");
    println!("cycles: {}   fixed |D|=m: {}   zero-D: {}   return-checks: {}",
        n_cyc.load(Ordering::Relaxed), n_fix.load(Ordering::Relaxed),
        n_zero.load(Ordering::Relaxed), n_ret.load(Ordering::Relaxed));
    if n_cyc.load(Ordering::Relaxed) == 0 {
        println!("no conjugation-stable cycle in the covered region: the descent target remains open.");
    } else {
        println!("!!! conjugation-stable cycles FOUND: each descends the Gaussian phenomenon to Z — see stable_hits.txt !!!");
    }
    println!("total wall time {}", fmt_hms(t0.elapsed().as_secs()));
}

// enumerate squarefree odd m as ascending-index prime subsets; unit = (i0, i1-block);
// blk 0 also covers the singleton {p_i0}.
fn run_unit<F: FnMut(&[(u64, bool, u64, u64)])>(
    primes: &[(u64, bool, u64, u64)], mlim: u64, wcap: usize,
    i0: usize, blk: u64, blksz: u64, sel: &mut Vec<usize>, f: &mut F,
) {
    let p0 = primes[i0].0;
    let mut buf: Vec<(u64, bool, u64, u64)> = Vec::with_capacity(wcap);
    buf.push(primes[i0]);
    if blk == 0 { f(&buf); }
    let start = i0 + 1 + (blk * blksz) as usize;
    let end = (i0 + 1 + ((blk + 1) * blksz) as usize).min(primes.len());
    sel.clear();
    for i1 in start..end {
        let p1 = primes[i1].0;
        if p1 > mlim / p0 { break; }
        buf.truncate(1);
        buf.push(primes[i1]);
        f(&buf);
        extend_m(primes, mlim, wcap, i1 + 1, p0 * p1, &mut buf, f);
    }
}
fn extend_m<F: FnMut(&[(u64, bool, u64, u64)])>(
    primes: &[(u64, bool, u64, u64)], mlim: u64, wcap: usize,
    start: usize, prod: u64, buf: &mut Vec<(u64, bool, u64, u64)>, f: &mut F,
) {
    if buf.len() >= wcap { return; }
    for i in start..primes.len() {
        let p = primes[i].0;
        if p > mlim / prod { break; }
        buf.push(primes[i]);
        f(buf);
        extend_m(primes, mlim, wcap, i + 1, prod * p, buf, f);
        buf.pop();
    }
}
