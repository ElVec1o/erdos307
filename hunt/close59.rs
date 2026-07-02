// close59.rs — independent verification closing the 59-prime level of Erdős #307.
//
// THEOREM (Prop. close59 of the note): no solution of #307 has |P ∪ Q| = 59.
//
// Any solution's support U (|U| = 59) must satisfy T(U) = Σ 1/p > 2, which forces
//   (i)  all 39 primes ≤ 167 in U, and
//   (ii) the other 20 primes in (167, 787],
// leaving exactly 49,961 candidate supports.  For each, rigidity forces BOTH
//   N' + 2N = (a+b)²  and  N' - 2N = (a-b)²
// to be perfect squares (N = ΠU squarefree, N' = cofactor sum).  This program
// re-verifies, with its own bignum arithmetic and a different enumeration order
// from code/close59.py, that N' + 2N is a non-square for every candidate.
//
// Build:  rustc -O -o close59 close59.rs
// Run:    ./close59          (expected: count = 49961, survivors = 0, ~seconds)

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
        let s = carry
            + *a.get(i).unwrap_or(&0) as u128
            + *b.get(i).unwrap_or(&0) as u128;
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

fn mul_big(a: &Big, b: &Big) -> Big { // schoolbook (self-test only)
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

fn bit_len(a: &Big) -> usize {
    64 * (a.len() - 1) + (64 - a.last().unwrap().leading_zeros() as usize)
}

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

/// Binary-method integer sqrt; returns (floor(sqrt(n)), remainder-is-zero).
fn isqrt_exact(n: &Big) -> (Big, bool) {
    if is_zero(n) { return (from_u64(0), true); }
    let l = bit_len(n);
    let mut bit = shl_bits(&from_u64(1), (l - 1) & !1); // largest power of 4 <= n
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
    for c in s.bytes() {
        r = mul_small(&r, 10);
        r = add_big(&r, &from_u64((c - b'0') as u64));
    }
    r
}

// ------------------------------- main ---------------------------------------
fn main() {
    // self-tests: bignum sqrt on ~40-digit numbers
    let t = from_dec("123456789012345678901234567890123456789");
    let sq = mul_big(&t, &t);
    let (r1, ex1) = isqrt_exact(&sq);
    assert!(ex1 && cmp_big(&r1, &t) == std::cmp::Ordering::Equal);
    let (_, ex2) = isqrt_exact(&add_big(&sq, &from_u64(1)));
    assert!(!ex2);
    let (r3, ex3) = isqrt_exact(&from_u64(144));
    assert!(ex3 && r3 == from_u64(12));
    eprintln!("bignum self-tests ok");

    // primes to 800
    let nmax = 800usize;
    let mut comp = vec![false; nmax + 1];
    let mut primes: Vec<u64> = Vec::new();
    for i in 2..=nmax {
        if !comp[i] {
            primes.push(i as u64);
            let mut j = i * i;
            while j <= nmax { comp[j] = true; j += i; }
        }
    }

    // forced / pool, with float margins far above f64 error (~1e-16)
    let t58: f64 = primes[..58].iter().map(|&p| 1.0 / p as f64).sum();
    let t60: f64 = primes[..60].iter().map(|&p| 1.0 / p as f64).sum();
    let forced: Vec<u64> = primes.iter().cloned()
        .filter(|&p| p <= 277 && (t60 - 1.0 / (p as f64)) < 2.0 - 1e-9).collect();
    assert_eq!(forced.len(), 39);
    assert_eq!(*forced.last().unwrap(), 167);
    let pool: Vec<u64> = primes.iter().cloned()
        .filter(|&p| p > 167 && (t58 + 1.0 / (p as f64)) > 2.0 + 1e-9).collect();
    assert_eq!((pool[0], *pool.last().unwrap()), (173, 787));
    // no borderline case within 1e-9 of the cutoffs (margins are ~1e-4)
    for &p in &primes {
        if p <= 277 { assert!((t60 - 1.0 / (p as f64) - 2.0).abs() > 1e-7); }
        assert!((t58 + 1.0 / (p as f64) - 2.0).abs() > 1e-7);
    }
    let k = 59 - forced.len(); // 20
    let thr: f64 = 2.0 - forced.iter().map(|&p| 1.0 / p as f64).sum::<f64>();
    let pf: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    let suffix_best: Vec<f64> = {
        // best[i] over need values computed on the fly instead
        Vec::new()
    };
    let _ = suffix_best;

    // exhaustive DFS (explicit stack; EXCLUDE-first order — opposite of the
    // Python reference), float prune with 1e-9 guard band, exact final filter.
    let mut count = 0u64;
    let mut survivors: Vec<Vec<u64>> = Vec::new();
    let mut near_boundary = 0u64;
    let mut stack: Vec<(usize, usize, f64, Vec<u8>)> = vec![(0, k, 0.0, Vec::new())];
    while let Some((i, need, cur, ch)) = stack.pop() {
        if need == 0 {
            if cur > thr - 1e-9 {
                // exact test: T(U) > 2  <=>  Nu > 2*D  (bignum, no floats)
                let u: Vec<u64> = forced.iter().cloned()
                    .chain(ch.iter().map(|&j| pool[j as usize])).collect();
                let mut d = from_u64(1);
                for &p in &u { d = mul_small(&d, p); }
                let mut nu = from_u64(0);
                for &p in &u {
                    let (q, r) = div_small(&d, p);
                    assert_eq!(r, 0);
                    nu = add_big(&nu, &q);
                }
                let d2 = mul_small(&d, 2);
                if cmp_big(&nu, &d2) == std::cmp::Ordering::Greater {
                    count += 1;
                    if (cur - thr).abs() < 1e-9 { near_boundary += 1; }
                    let plus = add_big(&nu, &d2);
                    let (_, plus_sq) = isqrt_exact(&plus);
                    if plus_sq {
                        let minus = sub_big(&nu, &d2);
                        let (_, minus_sq) = isqrt_exact(&minus);
                        if minus_sq { survivors.push(u); }
                    }
                }
            }
            continue;
        }
        if i + need > pool.len() { continue; }
        let best: f64 = cur + pf[i..i + need].iter().sum::<f64>();
        if best <= thr - 1e-9 { continue; }
        // exclude-first ordering:
        stack.push((i + 1, need - 1, cur + pf[i], { let mut c = ch.clone(); c.push(i as u8); c }));
        stack.push((i + 1, need, cur, ch));
    }

    println!("admissible 59-prime supports: {}", count);
    println!("float near-boundary (exact-checked): {}", near_boundary);
    println!("passing both-squares test:    {}", survivors.len());
    for u in &survivors { println!("  SURVIVOR: {:?}", u); }
    if count == 49961 && survivors.is_empty() {
        println!("VERIFIED (independent): no 59-prime support closes -> |P∪Q| >= 60.");
    } else {
        println!("WARNING: unexpected count or survivors — investigate before citing.");
    }
}
