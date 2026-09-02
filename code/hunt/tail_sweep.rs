// tail_sweep.rs — Erdős #307: sweep of the level-60 "tail family" U = {first 59 primes} ∪ {q}.
//
// A solution supported on U forces BOTH
//     A·q + Π₅₉ = x²   and   B·q + Π₅₉ = y²,
// where A = N₅₉ + 2Π₅₉, B = N₅₉ − 2Π₅₉ (both 113-digit constants, hardcoded and re-derived
// at startup as a self-test).  At startup the program PROVES (by direct mod-8 computation on
// the exact constants) that q ≡ 1, 3, 7 (mod 8) are impossible, then exhaustively sweeps the
// remaining class q ≡ 5 (mod 8) up to BOUND with layered square filters
// (mod 64/63/65/11 incremental+direct, then mod 97/101/103/107), exact bignum isqrt on
// survivors, and deterministic Miller–Rabin on any exact hit.
//
// Outcome "0 both-square q" proves:  no tail-shape level-60 solution has q ≤ BOUND.
//
// Progress + ETA on stderr; state autosaved every segment to ./tail_sweep_state.txt
// (resume is automatic — safe to Ctrl-C anytime); survivors + summary appended to
// ./tail_sweep_results.txt.
//
// Build:  rustc -O -o tail_sweep tail_sweep.rs
// Run:    ./tail_sweep              (default BOUND = 1e12; ~2–3 h single-core, Ctrl-C safe + auto-resume)
//         ./tail_sweep 10000000000000   (1e13; resumes past work automatically)

use std::env;
use std::fs;
use std::io::Write as IoWrite;
use std::time::Instant;

// ---------------- minimal unsigned bignum (little-endian u64 limbs) ----------
type Big = Vec<u64>;

fn norm(mut a: Big) -> Big { while a.len() > 1 && *a.last().unwrap() == 0 { a.pop(); } a }
fn from_u64(x: u64) -> Big { vec![x] }
fn is_zero(a: &Big) -> bool { a.len() == 1 && a[0] == 0 }

fn cmp_big(a: &Big, b: &Big) -> std::cmp::Ordering {
    use std::cmp::Ordering::*;
    if a.len() != b.len() { return a.len().cmp(&b.len()); }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] { return if a[i] < b[i] { Less } else { Greater }; }
    }
    Equal
}

fn add_big(a: &Big, b: &Big) -> Big {
    let n = a.len().max(b.len());
    let mut r = Vec::with_capacity(n + 1);
    let mut carry = 0u128;
    for i in 0..n {
        let s = carry + *a.get(i).unwrap_or(&0) as u128 + *b.get(i).unwrap_or(&0) as u128;
        r.push(s as u64);
        carry = s >> 64;
    }
    if carry > 0 { r.push(carry as u64); }
    norm(r)
}

fn sub_big(a: &Big, b: &Big) -> Big { // requires a >= b
    let mut r = Vec::with_capacity(a.len());
    let mut borrow = 0i128;
    for i in 0..a.len() {
        let d = a[i] as i128 - *b.get(i).unwrap_or(&0) as i128 - borrow;
        if d < 0 { r.push((d + (1i128 << 64)) as u64); borrow = 1; }
        else { r.push(d as u64); borrow = 0; }
    }
    assert_eq!(borrow, 0, "sub_big underflow");
    norm(r)
}

fn mul_small(a: &Big, m: u64) -> Big {
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut carry = 0u128;
    for &x in a {
        let p = x as u128 * m as u128 + carry;
        r.push(p as u64);
        carry = p >> 64;
    }
    if carry > 0 { r.push(carry as u64); }
    norm(r)
}

fn mul_big(a: &Big, b: &Big) -> Big {
    let mut r = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = r[i + j] as u128 + x as u128 * y as u128 + carry;
            r[i + j] = t as u64;
            carry = t >> 64;
        }
        let mut k = i + b.len();
        while carry > 0 { let t = r[k] as u128 + carry; r[k] = t as u64; carry = t >> 64; k += 1; }
    }
    norm(r)
}

fn mod_small(a: &Big, m: u64) -> u64 {
    let mut rem = 0u128;
    for i in (0..a.len()).rev() { rem = ((rem << 64) | a[i] as u128) % m as u128; }
    rem as u64
}

fn div_small(a: &Big, d: u64) -> (Big, u64) {
    let mut q = vec![0u64; a.len()];
    let mut rem = 0u128;
    for i in (0..a.len()).rev() {
        let cur = (rem << 64) | a[i] as u128;
        q[i] = (cur / d as u128) as u64;
        rem = cur % d as u128;
    }
    (norm(q), rem as u64)
}

fn bit_len(a: &Big) -> usize { 64 * (a.len() - 1) + (64 - a.last().unwrap().leading_zeros() as usize) }

fn shr_bits(a: &Big, k: usize) -> Big {
    let (limbs, bits) = (k / 64, k % 64);
    if limbs >= a.len() { return from_u64(0); }
    let mut r = Vec::with_capacity(a.len() - limbs);
    for i in limbs..a.len() {
        let mut v = a[i] >> bits;
        if bits > 0 && i + 1 < a.len() { v |= a[i + 1] << (64 - bits); }
        r.push(v);
    }
    norm(r)
}

fn shl_bits(a: &Big, k: usize) -> Big {
    let (limbs, bits) = (k / 64, k % 64);
    let mut r = vec![0u64; limbs];
    let mut carry = 0u64;
    for &x in a {
        r.push((x << bits) | carry);
        carry = if bits > 0 { x >> (64 - bits) } else { 0 };
    }
    if carry > 0 { r.push(carry); }
    norm(r)
}

/// (floor(sqrt(n)), remainder-is-zero) by the binary method.
fn isqrt_exact(n: &Big) -> (Big, bool) {
    if is_zero(n) { return (from_u64(0), true); }
    let l = bit_len(n);
    let mut bit = shl_bits(&from_u64(1), (l - 1) & !1);
    let mut res = from_u64(0);
    let mut rem = n.clone();
    while !is_zero(&bit) {
        let t = add_big(&res, &bit);
        if cmp_big(&rem, &t) != std::cmp::Ordering::Less {
            rem = sub_big(&rem, &t);
            res = add_big(&shr_bits(&res, 1), &bit);
        } else {
            res = shr_bits(&res, 1);
        }
        bit = shr_bits(&bit, 2);
    }
    (res, is_zero(&rem))
}

fn from_dec(s: &str) -> Big {
    let mut r = from_u64(0);
    for c in s.bytes() { r = mul_small(&r, 10); r = add_big(&r, &from_u64((c - b'0') as u64)); }
    r
}

fn to_dec(a: &Big) -> String {
    let mut x = a.clone();
    let mut s = String::new();
    while !is_zero(&x) { let (q, r) = div_small(&x, 10); s.push((b'0' + r as u8) as char); x = q; }
    if s.is_empty() { s.push('0'); }
    s.chars().rev().collect()
}

// deterministic Miller–Rabin for u64 (valid far past 1e13 with these bases)
fn mulmod(a: u64, b: u64, m: u64) -> u64 { ((a as u128 * b as u128) % m as u128) as u64 }
fn powmod(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64; a %= m;
    while e > 0 { if e & 1 == 1 { r = mulmod(r, a, m); } a = mulmod(a, a, m); e >>= 1; }
    r
}
fn is_prime_u64(n: u64) -> bool {
    if n < 2 { return false; }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 { return n == p; }
    }
    let mut d = n - 1; let mut s = 0;
    while d & 1 == 0 { d >>= 1; s += 1; }
    'wit: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 1..s { x = mulmod(x, x, n); if x == n - 1 { continue 'wit; } }
        return false;
    }
    true
}

// ------------------------------- constants -----------------------------------
const P59_DEC: &str = "87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390";
const N59_DEC: &str = "175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363";

const STATE_FILE: &str = "tail_sweep_state.txt";
const RESULT_FILE: &str = "tail_sweep_results.txt";
const SEG: u64 = 8_000_000_000; // q-range per autosave segment (~30-60 s)

fn main() {
    let bound: u64 = env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(1_000_000_000_000);

    // ---- constants + self-tests ------------------------------------------------
    let pi59 = from_dec(P59_DEC);
    let n59 = from_dec(N59_DEC);
    // re-derive Π₅₉, N₅₉ from the primes themselves
    let primes59: Vec<u64> = { // primes < 280
        let mut v = Vec::new();
        'o: for n in 2u64..280 {
            for d in 2..n { if d * d > n { break; } if n % d == 0 { continue 'o; } }
            v.push(n);
        }
        v
    };
    assert_eq!(primes59.len(), 59);
    let mut prod = from_u64(1);
    for &p in &primes59 { prod = mul_small(&prod, p); }
    assert_eq!(cmp_big(&prod, &pi59), std::cmp::Ordering::Equal, "Pi59 mismatch");
    let mut cof = from_u64(0);
    for &p in &primes59 { let (q, r) = div_small(&pi59, p); assert_eq!(r, 0); cof = add_big(&cof, &q); }
    assert_eq!(cmp_big(&cof, &n59), std::cmp::Ordering::Equal, "N59 mismatch");
    let two_pi = mul_small(&pi59, 2);
    let a_big = add_big(&n59, &two_pi);        // A = N59 + 2*Pi59
    let b_big = sub_big(&n59, &two_pi);        // B = N59 - 2*Pi59  (positive: T59 > 2)
    // bignum sqrt self-test
    let t = from_dec("123456789012345678901234567890123456789");
    let sq = mul_big(&t, &t);
    let (r1, e1) = isqrt_exact(&sq);
    assert!(e1 && cmp_big(&r1, &t) == std::cmp::Ordering::Equal);
    assert!(!isqrt_exact(&add_big(&sq, &from_u64(1))).1);
    // mod-8 elimination PROOF: odd squares are ≡ 1 (mod 8); check classes 1,3,5,7
    let (a8, b8, p8) = (mod_small(&a_big, 8), mod_small(&b_big, 8), mod_small(&pi59, 8));
    let mut ok_classes = Vec::new();
    for r in [1u64, 3, 5, 7] {
        if (a8 * r + p8) % 8 == 1 && (b8 * r + p8) % 8 == 1 { ok_classes.push(r); }
    }
    assert_eq!(ok_classes, vec![5], "mod-8 analysis changed?!");
    eprintln!("self-tests ok; mod 8 proves q ≡ 5 (mod 8) is the only possible class");

    // ---- filters -----------------------------------------------------------------
    // stage 1 (incremental): mod 64 and mod 63 on both sides
    // stage 2 (direct): mod 65, 11, 97, 101, 103, 107 on both sides
    let mods: Vec<u64> = vec![64, 63, 65, 11, 97, 101, 103, 107];
    let masks: Vec<Vec<bool>> = mods.iter().map(|&m| {
        let mut v = vec![false; m as usize];
        for s in 0..m { v[((s * s) % m) as usize] = true; }
        v
    }).collect();
    let am: Vec<u64> = mods.iter().map(|&m| mod_small(&a_big, m)).collect();
    let bm: Vec<u64> = mods.iter().map(|&m| mod_small(&b_big, m)).collect();
    let pm: Vec<u64> = mods.iter().map(|&m| mod_small(&pi59, m)).collect();
    // filter sanity: actual squares always pass every filter
    for s in 1u64..2000 {
        let v = s * s;
        for (i, &m) in mods.iter().enumerate() { assert!(masks[i][(v % m) as usize]); }
    }

    // ---- resume ----------------------------------------------------------------
    let mut q_start: u64 = 285; // least q ≡ 5 (mod 8) exceeding 277
    let mut tested: u64 = 0;
    let mut stage2: u64 = 0;
    let mut exact_plus: u64 = 0;
    let mut both: u64 = 0;
    if let Ok(s) = fs::read_to_string(STATE_FILE) {
        let mut vals = std::collections::HashMap::new();
        for line in s.lines() {
            if let Some((k, v)) = line.split_once('=') { vals.insert(k.trim().to_string(), v.trim().to_string()); }
        }
        if let (Some(nq), Some(ts)) = (vals.get("next_q"), vals.get("tested")) {
            q_start = nq.parse().unwrap_or(q_start);
            tested = ts.parse().unwrap_or(0);
            stage2 = vals.get("stage2").and_then(|x| x.parse().ok()).unwrap_or(0);
            exact_plus = vals.get("exact_plus").and_then(|x| x.parse().ok()).unwrap_or(0);
            both = vals.get("both").and_then(|x| x.parse().ok()).unwrap_or(0);
            eprintln!("resuming from q = {} (tested so far: {})", q_start, tested);
        }
    }
    if q_start > bound {
        eprintln!("state already past BOUND={}; nothing to do (raise BOUND to continue)", bound);
        return;
    }

    // incremental residues for stage-1 moduli (64, 63, 65, 11), both sides, at q = q_start
    let nst1 = 4usize; // first 4 moduli are incremental
    let mut va: Vec<u64> = (0..nst1).map(|i| (am[i] * (q_start % mods[i]) + pm[i]) % mods[i]).collect();
    let mut vb: Vec<u64> = (0..nst1).map(|i| (bm[i] * (q_start % mods[i]) + pm[i]) % mods[i]).collect();
    let sa: Vec<u64> = (0..nst1).map(|i| (am[i] * 8) % mods[i]).collect();
    let sb: Vec<u64> = (0..nst1).map(|i| (bm[i] * 8) % mods[i]).collect();

    let start = Instant::now();
    let mut q = q_start;
    let mut seg_end = ((q / SEG) + 1) * SEG;

    while q <= bound {
        // ---- stage 1: mod 64, 63, 65, 11 on both sides (incremental) ----
        if masks[0][va[0] as usize] && masks[0][vb[0] as usize]
            && masks[1][va[1] as usize] && masks[1][vb[1] as usize]
            && masks[2][va[2] as usize] && masks[2][vb[2] as usize]
            && masks[3][va[3] as usize] && masks[3][vb[3] as usize] {
            // ---- stage 2: direct mod filters ----
            stage2 += 1;
            let mut pass = true;
            for i in nst1..mods.len() {
                let m = mods[i];
                let qi = q % m;
                if !masks[i][((am[i] * qi + pm[i]) % m) as usize]
                    || !masks[i][((bm[i] * qi + pm[i]) % m) as usize] { pass = false; break; }
            }
            if pass {
                // ---- exact: plus side, then minus side ----
                let plus = add_big(&mul_small(&a_big, q), &pi59);
                let (_, plus_sq) = isqrt_exact(&plus);
                if plus_sq {
                    exact_plus += 1;
                    let minus = add_big(&mul_small(&b_big, q), &pi59);
                    let (_, minus_sq) = isqrt_exact(&minus);
                    if minus_sq {
                        both += 1;
                        let msg = format!("*** BOTH SQUARES at q = {} (prime: {}) ***\n  A*q+Pi59 = {}\n",
                                          q, is_prime_u64(q), to_dec(&plus));
                        eprintln!("\n{}", msg);
                        let mut f = fs::OpenOptions::new().create(true).append(true).open(RESULT_FILE).unwrap();
                        f.write_all(msg.as_bytes()).unwrap();
                    }
                }
            }
        }
        tested += 1;
        q += 8;
        for i in 0..nst1 {
            va[i] += sa[i]; if va[i] >= mods[i] { va[i] -= mods[i]; }
            vb[i] += sb[i]; if vb[i] >= mods[i] { vb[i] -= mods[i]; }
        }

        if q > seg_end || q > bound {
            // autosave (atomic: tmp + rename)
            let st = format!("next_q={}\ntested={}\nstage2={}\nexact_plus={}\nboth={}\nbound_seen={}\n",
                             q, tested, stage2, exact_plus, both, bound);
            fs::write("tail_sweep_state.tmp", &st).unwrap();
            fs::rename("tail_sweep_state.tmp", STATE_FILE).unwrap();
            let frac = (q.min(bound) as f64 - 285.0) / (bound as f64 - 285.0);
            let el = start.elapsed().as_secs_f64();
            let done_this_run = (q - q_start) as f64;
            let rate = done_this_run / el.max(1e-9);
            let eta = (bound.saturating_sub(q)) as f64 / rate.max(1.0);
            eprint!("\r  {:5.1}%  q={:<14}  {:.1e} q/s  stage2={}  exact+={}  both={}  ETA {:.0}s   ",
                    frac * 100.0, q, rate * 8.0, stage2, exact_plus, both, eta);
            seg_end += SEG;
        }
    }
    eprintln!();

    let summary = format!(
        "SWEEP COMPLETE to q <= {}: candidates(q≡5 mod 8)={}, stage2 survivors={}, exact plus-squares={}, BOTH-square hits={}\n{}\n",
        bound, tested, stage2, exact_plus, both,
        if both == 0 {
            format!("PROVEN: no level-60 tail-shape solution (U = first 59 primes + q) has q <= {}.", bound)
        } else {
            "!!! survivors found — investigate immediately !!!".to_string()
        });
    println!("{}", summary);
    let mut f = fs::OpenOptions::new().create(true).append(true).open(RESULT_FILE).unwrap();
    f.write_all(summary.as_bytes()).unwrap();
}
