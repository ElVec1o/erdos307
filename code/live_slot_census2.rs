// live_slot_census2.rs -- the live-slot census with Rule 8 machinery and a quadratic-residue
// filter, so the entry region of the decoupled family can be pushed well past 10^14.
//
// prop:liveslot: a live slot needs sigma(N_0) >= 3/2, hence N_0 >= Pi_10 = 6469693230. This sweeps
// squarefree N_0 with sigma(N_0) >= 3/2 up to a bound, testing whether Q_{N_0}(s,d) = A s^2 + B d^2
// represents 4 N_0^2 with an admissible slot r = (s^2 - N_0)/B that is prime and > 1.
//
// THE FILTER, which is what makes the range reachable. Since 2 N_0 = N_0' (mod A),
//      4 N_0^2 = N_0'^2   and   B = 2 N_0 + N_0' = 2 N_0'   (mod A),
// so A | 4N_0^2 - B d^2 becomes  A | N_0' (N_0' - 2 d^2). Let h be the part of A coprime to N_0'
// (divide out gcds until coprime). Then necessarily
//      2 d^2 = N_0'   (mod h).
// For every odd prime q | h with q not dividing 2 N_0', that forces N_0' * inv2 to be a quadratic
// residue mod q. A single non-residue kills the base outright, with no d-loop at all. Bases that
// survive the filter get the full loop over d <= dmax, where
//      dmax^2 = N_0 (2 sigma^2 + sigma - 6)/(2 + sigma),
// the bound from prop:liveslot's inequality.
//
// MEMORY (Rule 8 pre-flight): O(1). A 38 KB table of primes below 10^5 for the filter, ~430 primes
// below 3000 for the DFS, recursion depth under 20, and no allocation that grows with the range.
// There is no OOM risk at any bound.
//
// Rule 8 also: progress with rate, ETA, atomic checkpoint every 20 s (temp file then rename), and
// resume. The DFS order is deterministic, so the checkpoint is simply the number of bases already
// completed; on resume that many are skipped.
//
// Usage: ./live_slot_census2 <xmax> [resume_count]

use std::io::Write;

fn primes_upto(n: usize) -> Vec<u32> {
    let mut s = vec![true; n + 1];
    s[0] = false;
    if n >= 1 { s[1] = false; }
    let mut i = 2;
    while i * i <= n {
        if s[i] { let mut j = i * i; while j <= n { s[j] = false; j += i; } }
        i += 1;
    }
    (2..=n).filter(|&i| s[i]).map(|i| i as u32).collect()
}

fn isqrt(n: u128) -> u128 {
    if n == 0 { return 0; }
    let mut x = (n as f64).sqrt() as u128;
    while x > 0 && x > n / x.max(1) { x -= 1; }
    while (x + 1) <= n / (x + 1) { x += 1; }
    x
}

fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }

fn mulmod(a: u128, b: u128, m: u128) -> u128 {
    let mut res = 0u128; let mut a = a % m; let mut b = b;
    while b > 0 { if b & 1 == 1 { res = (res + a) % m; } a = (a << 1) % m; b >>= 1; }
    res
}

fn powmod(mut b: u128, mut e: u128, m: u128) -> u128 {
    let mut r = 1u128; b %= m;
    while e > 0 { if e & 1 == 1 { r = mulmod(r, b, m); } b = mulmod(b, b, m); e >>= 1; }
    r
}

fn is_prime_u128(n: u128) -> bool {
    if n < 2 { return false; }
    for p in [2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 { return n == p; }
    }
    let mut d = n - 1; let mut r = 0;
    while d % 2 == 0 { d /= 2; r += 1; }
    'outer: for a in [2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 1..r { x = mulmod(x, x, n); if x == n - 1 { continue 'outer; } }
        return false;
    }
    true
}

/// Legendre symbol (a|q) for odd prime q
fn legendre(a: u128, q: u128) -> i32 {
    let a = a % q;
    if a == 0 { return 0; }
    let t = powmod(a, (q - 1) / 2, q);
    if t == 1 { 1 } else { -1 }
}

struct Stats { bases: u64, filtered: u64, looped: u64, reps: u64, live: u64 }

/// returns Some((s,d,r)) if a live slot is found
fn check(n0: u128, np: u128, small: &[u32], st: &mut Stats) -> Option<(u128, u128, u128)> {
    if np >= 2 * n0 { return None; }              // sigma >= 2: covered by thm:barrier
    let a = 2 * n0 - np;
    let b = 2 * n0 + np;
    // prop:liveslot bound on d
    let num = 2 * np * np + np * n0;
    if num <= 6 * n0 * n0 { return None; }        // sigma < 3/2
    let dmax = isqrt((num - 6 * n0 * n0) / b);

    // quadratic-residue filter: h = part of A coprime to N_0'
    let mut h = a;
    loop { let g = gcd(h, np); if g == 1 { break; } h /= g; if h == 1 { break; } }
    if h > 1 {
        let inv2 = (h + 1) / 2;                    // h is odd here iff a/np structure allows; guard below
        if h % 2 == 1 {
            let target = mulmod(np % h, inv2 % h, h);
            for &qq in small.iter() {
                let q = qq as u128;
                if q * q > h { break; }
                if h % q == 0 {
                    if q > 2 && (2 * np) % q != 0 {
                        if legendre(target, q) == -1 { st.filtered += 1; return None; }
                    }
                }
            }
        }
    }

    st.looped += 1;
    let target4 = 4 * n0 * n0;
    for d in 0..=dmax {
        let bd2 = b * d * d;
        if bd2 > target4 { break; }
        let rem = target4 - bd2;
        if rem % a != 0 { continue; }
        let s2 = rem / a;
        let s = isqrt(s2);
        if s * s != s2 { continue; }
        st.reps += 1;
        if s * s <= n0 { continue; }
        let numr = s * s - n0;
        if numr % b != 0 { continue; }
        let r = numr / b;
        if r <= 1 { continue; }
        if gcd(r, n0) != 1 { continue; }
        if !is_prime_u128(r) { continue; }
        st.live += 1;
        return Some((s, d, r));
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn dfs(i: usize, n0: u128, np: u128, sig: f64, xmax: u128, dp: &[u32], small: &[u32],
       st: &mut Stats, resume: u64, t0: &std::time::Instant, last: &mut std::time::Instant,
       xmax_str: &str) {
    if sig >= 1.5 && n0 > 1 {
        st.bases += 1;
        if st.bases > resume {
            if let Some((s, d, r)) = check(n0, np, small, st) {
                println!("\n  *** LIVE SLOT *** N_0 = {}  s = {}  d = {}  r = {}", n0, s, d, r);
                let _ = std::io::stdout().flush();
            }
        }
        if last.elapsed().as_secs_f64() > 20.0 {
            let el = t0.elapsed().as_secs_f64();
            eprint!("\r  bases {}  filtered {}  looped {}  reps {}  live {}  {:.0}/s  {:.1}m elapsed   ",
                    st.bases, st.filtered, st.looped, st.reps, st.live,
                    (st.bases.saturating_sub(resume)) as f64 / el.max(1e-9), el / 60.0);
            let _ = std::io::stderr().flush();
            let tmp = "live_slot_census2.progress.tmp";
            if let Ok(mut f) = std::fs::File::create(tmp) {
                let _ = writeln!(f, "xmax {} bases_done {} filtered {} looped {} reps {} live {} elapsed_s {:.0}",
                                 xmax_str, st.bases, st.filtered, st.looped, st.reps, st.live, el);
                let _ = std::fs::rename(tmp, "live_slot_census2.progress");
            }
            *last = std::time::Instant::now();
        }
    }
    // prune: can the remaining primes still reach mass 3/2 within the bound?
    let mut opt = sig; let mut prod = n0;
    for j in i..dp.len() {
        let p = dp[j] as u128;
        if prod > xmax / p { break; }
        prod *= p; opt += 1.0 / p as f64;
        if opt >= 1.5 { break; }
    }
    if opt < 1.5 { return; }
    for j in i..dp.len() {
        let p = dp[j] as u128;
        if n0 > xmax / p { break; }
        dfs(j + 1, n0 * p, np * p + n0, sig + 1.0 / p as f64, xmax, dp, small, st, resume, t0, last, xmax_str);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let xmax: u128 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1_000_000_000_000_000_000);
    let resume: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    let dp = primes_upto(3000);
    let small = primes_upto(100_000);
    eprintln!("live-slot census, xmax = {}, resume from base {}", xmax, resume);
    eprintln!("memory: {} KB of prime tables, O(1) otherwise",
              (dp.len() * 4 + small.len() * 4) / 1024);
    let mut st = Stats { bases: 0, filtered: 0, looped: 0, reps: 0, live: 0 };
    let t0 = std::time::Instant::now();
    let mut last = std::time::Instant::now();
    let xs = format!("{}", xmax);
    dfs(0, 1, 0, 0.0, xmax, &dp, &small, &mut st, resume, &t0, &mut last, &xs);
    println!("\n\nxmax = {}", xmax);
    println!("  bases with sigma >= 3/2 : {}", st.bases);
    println!("  killed by the QR filter : {}", st.filtered);
    println!("  reaching the d-loop     : {}", st.looped);
    println!("  representations found   : {}", st.reps);
    println!("  LIVE slots (r prime >1) : {}", st.live);
    println!("  elapsed {:.1} min", t0.elapsed().as_secs_f64() / 60.0);
}
