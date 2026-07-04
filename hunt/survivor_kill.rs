// survivor_kill.rs — Erdős #307: factoring attack on the Jacobi-inconclusive tail families.
//
// Context (Prop. tailkill): a level-60 tail family with base S (a 59-prime set, Σ1/p > 2)
// is EMPTY for every tail prime q as soon as some prime ℓ | A_S = N_S + 2·D_S with odd
// multiplicity has Legendre (D_S|ℓ) = −1  (equally for B_S = N_S − 2·D_S).  The Jacobi
// symbol (D_S|A_S) = (D_S|B_S) decides this without factoring when it is −1 (31,219 of
// the 49,961 families).  The remaining 18,742 have Jacobi +1: their −1-Legendre primes,
// if any, occur to an even count — visible only by partial factorization.
//
// This program re-derives the enumeration and the Jacobi split (cross-checks 31,219 /
// 18,742), then attacks each survivor's A_S and B_S with trial division + Brent–Pollard
// rho on a Montgomery-multiplication bignum core.  Found factors are kept as a PAIRWISE
// COPRIME basis, so the kill rule needs no primality testing at all:
//     a basis piece P with odd multiplicity and Jacobi (D_S|P) = −1  ⇒  family EMPTY
// (P then contains a prime of odd total multiplicity in A_S with Legendre −1).
//
// Progress + ETA; state autosaved to ./survivor_state.txt (resume automatic, Ctrl-C safe);
// kills appended to ./survivor_kill_results.txt.
//
// Build:  rustc -O -o survivor_kill survivor_kill.rs
// Run:    ./survivor_kill                 (default 300000 rho iters per side; ~2–4 h)
//         ./survivor_kill 50000 30        (smoke test: small budget, first 30 survivors)

use std::env;
use std::fs;
use std::io::Write as IoWrite;
use std::time::Instant;

// ---------------- minimal bignum (little-endian u64 limbs) ----------------
type Big = Vec<u64>;

fn norm(mut a: Big) -> Big { while a.len() > 1 && *a.last().unwrap() == 0 { a.pop(); } a }
fn from_u64(x: u64) -> Big { vec![x] }
fn is_zero(a: &Big) -> bool { a.len() == 1 && a[0] == 0 }
fn is_one(a: &Big) -> bool { a.len() == 1 && a[0] == 1 }

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
    let mut c = 0u128;
    for i in 0..n {
        let s = c + *a.get(i).unwrap_or(&0) as u128 + *b.get(i).unwrap_or(&0) as u128;
        r.push(s as u64); c = s >> 64;
    }
    if c > 0 { r.push(c as u64); }
    norm(r)
}

fn sub_big(a: &Big, b: &Big) -> Big { // a >= b
    let mut r = Vec::with_capacity(a.len());
    let mut br = 0i128;
    for i in 0..a.len() {
        let d = a[i] as i128 - *b.get(i).unwrap_or(&0) as i128 - br;
        if d < 0 { r.push((d + (1i128 << 64)) as u64); br = 1; } else { r.push(d as u64); br = 0; }
    }
    assert_eq!(br, 0);
    norm(r)
}

fn mul_small(a: &Big, m: u64) -> Big {
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut c = 0u128;
    for &x in a { let p = x as u128 * m as u128 + c; r.push(p as u64); c = p >> 64; }
    if c > 0 { r.push(c as u64); }
    norm(r)
}

fn mul_big(a: &Big, b: &Big) -> Big {
    let mut r = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut c = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = r[i + j] as u128 + x as u128 * y as u128 + c;
            r[i + j] = t as u64; c = t >> 64;
        }
        let mut k = i + b.len();
        while c > 0 { let t = r[k] as u128 + c; r[k] = t as u64; c = t >> 64; k += 1; }
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

fn mod_small(a: &Big, m: u64) -> u64 {
    let mut rem = 0u128;
    for i in (0..a.len()).rev() { rem = ((rem << 64) | a[i] as u128) % m as u128; }
    rem as u64
}

fn bit_len(a: &Big) -> usize { 64 * (a.len() - 1) + (64 - a.last().unwrap().leading_zeros() as usize) }

fn shl_bits(a: &Big, k: usize) -> Big {
    let (l, b) = (k / 64, k % 64);
    let mut r = vec![0u64; l];
    let mut c = 0u64;
    for &x in a {
        r.push(if b > 0 { (x << b) | c } else { x });
        c = if b > 0 { x >> (64 - b) } else { 0 };
    }
    if c > 0 { r.push(c); }
    norm(r)
}

fn shr1(a: &Big) -> Big {
    let mut r = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        let mut v = a[i] >> 1;
        if i + 1 < a.len() { v |= a[i + 1] << 63; }
        r.push(v);
    }
    norm(r)
}

/// a mod n by shift-and-subtract (n > 0).
fn mod_bigsub(a: &Big, n: &Big) -> Big {
    let mut a = a.clone();
    while cmp_big(&a, n) != std::cmp::Ordering::Less {
        let k = bit_len(&a) - bit_len(n);
        let mut t = shl_bits(n, k);
        if cmp_big(&t, &a) == std::cmp::Ordering::Greater { t = shl_bits(n, k - 1); }
        a = sub_big(&a, &t);
    }
    a
}

/// binary gcd
fn gcd_big(a: &Big, b: &Big) -> Big {
    let (mut a, mut b) = (a.clone(), b.clone());
    if is_zero(&a) { return b; }
    if is_zero(&b) { return a; }
    let mut shift = 0usize;
    while a[0] & 1 == 0 && b[0] & 1 == 0 { a = shr1(&a); b = shr1(&b); shift += 1; }
    while a[0] & 1 == 0 { a = shr1(&a); }
    loop {
        while b[0] & 1 == 0 { b = shr1(&b); }
        if cmp_big(&a, &b) == std::cmp::Ordering::Greater { std::mem::swap(&mut a, &mut b); }
        b = sub_big(&b, &a);
        if is_zero(&b) { break; }
    }
    shl_bits(&a, shift)
}

/// Jacobi symbol (a | n), n odd positive.
fn jacobi_big(a: &Big, n: &Big) -> i32 {
    let mut a = mod_bigsub(a, n);
    let mut n = n.clone();
    let mut t = 1i32;
    while !is_zero(&a) {
        while a[0] & 1 == 0 {
            a = shr1(&a);
            let m8 = n[0] & 7;
            if m8 == 3 || m8 == 5 { t = -t; }
        }
        std::mem::swap(&mut a, &mut n);
        if a[0] & 3 == 3 && n[0] & 3 == 3 { t = -t; }
        a = mod_bigsub(&a, &n);
    }
    if is_one(&n) { t } else { 0 }
}

// ---------------- Montgomery arithmetic for a fixed odd modulus ----------------
struct Mont { m: Big, l: usize, n0: u64, r2: Big }

impl Mont {
    fn new(m: &Big) -> Mont {
        assert!(m[0] & 1 == 1);
        let l = m.len();
        // n0 = -m^{-1} mod 2^64 (Newton)
        let mut inv: u64 = 1;
        for _ in 0..6 { inv = inv.wrapping_mul(2u64.wrapping_sub(m[0].wrapping_mul(inv))); }
        let n0 = inv.wrapping_neg();
        // r = 2^(64l) mod m ; r2 = r * 2^(64l) mod m by 64l doublings
        let r = mod_bigsub(&shl_bits(&from_u64(1), 64 * l), m);
        let mut r2 = r.clone();
        for _ in 0..64 * l {
            r2 = add_big(&r2, &r2);
            if cmp_big(&r2, m) != std::cmp::Ordering::Less { r2 = sub_big(&r2, m); }
        }
        Mont { m: m.clone(), l, n0, r2 }
    }
    /// CIOS Montgomery multiplication: returns a*b*R^{-1} mod m (inputs in Mont domain).
    fn mul(&self, a: &Big, b: &Big) -> Big {
        let l = self.l;
        let mut t = vec![0u64; l + 2];
        for i in 0..l {
            let ai = *a.get(i).unwrap_or(&0);
            // t += ai * b
            let mut c = 0u128;
            for j in 0..l {
                let s = t[j] as u128 + ai as u128 * *b.get(j).unwrap_or(&0) as u128 + c;
                t[j] = s as u64; c = s >> 64;
            }
            let s = t[l] as u128 + c; t[l] = s as u64; t[l + 1] += (s >> 64) as u64;
            // reduce one limb
            let mu = t[0].wrapping_mul(self.n0);
            let mut c = 0u128;
            for j in 0..l {
                let s = t[j] as u128 + mu as u128 * self.m[j] as u128 + c;
                t[j] = s as u64; c = s >> 64;
            }
            let s = t[l] as u128 + c; t[l] = s as u64; t[l + 1] += (s >> 64) as u64;
            // shift down one limb
            for j in 0..l + 1 { t[j] = t[j + 1]; }
            t[l + 1] = 0;
        }
        let mut r = norm(t[..l + 1].to_vec());
        if cmp_big(&r, &self.m) != std::cmp::Ordering::Less { r = sub_big(&r, &self.m); }
        r
    }
    fn to_mont(&self, x: &Big) -> Big { self.mul(&mod_bigsub(x, &self.m), &self.r2) }
}

/// Brent rho on modulus m (odd, composite hoped), budget iterations. Returns a factor or None.
fn brent_rho(m: &Big, seed: u64, budget: u64) -> Option<Big> {
    let mont = Mont::new(m);
    let one = from_u64(1);
    let c = mont.to_mont(&from_u64(seed | 1));
    let mut y = mont.to_mont(&from_u64(seed.wrapping_add(2)));
    let (mut r, mut q) = (1u64, mont.to_mont(&one));
    let mut it = 0u64;
    let (mut x, mut ys) = (y.clone(), y.clone());
    let mut g = from_u64(1);
    'outer: while it < budget {
        x = y.clone();
        for _ in 0..r { y = add_mod(&mont.mul(&y, &y), &c, m); }
        let mut k = 0u64;
        while k < r {
            let lim = (r - k).min(128);
            ys = y.clone();
            for _ in 0..lim {
                y = add_mod(&mont.mul(&y, &y), &c, m);
                let d = if cmp_big(&x, &y) == std::cmp::Ordering::Less { sub_big(&y, &x) } else { sub_big(&x, &y) };
                q = mont.mul(&q, &if is_zero(&d) { one.clone() } else { d });
            }
            g = gcd_big(&q, m);
            it += lim;
            if !is_one(&g) { break 'outer; }
            if it >= budget { return None; }
            k += lim;
        }
        r <<= 1;
    }
    if is_one(&g) { return None; }
    if cmp_big(&g, m) == std::cmp::Ordering::Equal {
        // backtrack
        loop {
            ys = add_mod(&mont.mul(&ys, &ys), &c, m);
            let d = if cmp_big(&x, &ys) == std::cmp::Ordering::Less { sub_big(&ys, &x) } else { sub_big(&x, &ys) };
            let g2 = gcd_big(&d, m);
            if !is_one(&g2) {
                return if cmp_big(&g2, m) == std::cmp::Ordering::Equal { None } else { Some(g2) };
            }
        }
    }
    Some(g)
}

fn add_mod(a: &Big, b: &Big, m: &Big) -> Big {
    let s = add_big(a, b);
    if cmp_big(&s, m) != std::cmp::Ordering::Less { sub_big(&s, m) } else { s }
}

// ---------------- coprime-basis factor bookkeeping ----------------
/// Insert f into a pairwise-coprime basis (pieces with multiplicities), refining as needed.
fn basis_insert(basis: &mut Vec<(Big, u32)>, f: Big, mult: u32) {
    let mut queue = vec![(f, mult)];
    while let Some((f, m)) = queue.pop() {
        if is_one(&f) { continue; }
        let mut merged = false;
        for i in 0..basis.len() {
            let g = gcd_big(&basis[i].0, &f);
            if !is_one(&g) {
                let (p, pm) = basis.remove(i);
                let (pq, pr) = divide_out(&p, &g);
                assert!(is_zero(&pr));
                let (fq, fr) = divide_out(&f, &g);
                assert!(is_zero(&fr));
                // p = g*pq, f = g*fq
                queue.push((g.clone(), pm + m));
                if !is_one(&pq) { queue.push((pq, pm)); }
                if !is_one(&fq) { queue.push((fq, m)); }
                merged = true;
                break;
            }
        }
        if !merged { basis.push((f, m)); }
    }
}

/// exact division helper (returns (quotient, remainder-as-big))
fn divide_out(a: &Big, d: &Big) -> (Big, Big) {
    // long division via shift-subtract building the quotient
    let mut q = from_u64(0);
    let mut r = a.clone();
    while cmp_big(&r, d) != std::cmp::Ordering::Less {
        let mut k = bit_len(&r) - bit_len(d);
        let mut t = shl_bits(d, k);
        if cmp_big(&t, &r) == std::cmp::Ordering::Greater { k -= 1; t = shl_bits(d, k); }
        r = sub_big(&r, &t);
        q = add_big(&q, &shl_bits(&from_u64(1), k));
    }
    (q, r)
}

// ---------------- main ----------------
const STATE_FILE: &str = "survivor_state.txt";
const RESULT_FILE: &str = "survivor_kill_results.txt";

fn main() {
    let budget: u64 = env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(300_000);
    let max_surv: usize = env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(usize::MAX);

    // ---- self-tests ----
    {
        // mod / div / gcd / jacobi on knowns
        let a = mul_big(&from_u64(10_000_000_019), &from_u64(10_000_000_033));
        let (q, r) = divide_out(&a, &from_u64(10_000_000_019));
        assert!(is_zero(&r) && q == from_u64(10_000_000_033));
        assert_eq!(jacobi_big(&from_u64(2), &from_u64(7)), 1);   // 2 = 3^2 mod 7
        assert_eq!(jacobi_big(&from_u64(3), &from_u64(7)), -1);
        // Montgomery vs naive on pseudo-random pairs
        let m = norm(vec![0x1234567890abcdefu64 | 1, 0xfedcba0987654321, 0x0f0e0d0c0b0a0908]);
        let mont = Mont::new(&m);
        let mut s: u64 = 88172645463325252;
        for _ in 0..200 {
            let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
            let x = norm(vec![rnd(), rnd(), rnd() % 0x0f0e0d0c0b0a0908]);
            let y = norm(vec![rnd(), rnd(), rnd() % 0x0f0e0d0c0b0a0908]);
            let naive = mod_bigsub(&mul_big(&x, &y), &m);
            let mx = mont.to_mont(&x);
            let my = mont.to_mont(&y);
            let mm = mont.mul(&mx, &my);            // x*y*R mod m
            let back = mont.mul(&mm, &from_u64(1)); // x*y mod m
            assert_eq!(cmp_big(&back, &naive), std::cmp::Ordering::Equal, "Montgomery mismatch");
        }
        eprintln!("self-tests ok (division, jacobi, Montgomery vs naive)");
    }

    // ---- primes to 10^6 for trial division; primes to 800 for the enumeration ----
    let tbound = 1_000_000usize;
    let mut comp = vec![false; tbound + 1];
    let mut tprimes: Vec<u64> = Vec::new();
    for i in 2..=tbound {
        if !comp[i] {
            tprimes.push(i as u64);
            let mut j = i * i;
            while j <= tbound { comp[j] = true; j += i; }
        }
    }
    let primes800: Vec<u64> = tprimes.iter().cloned().take_while(|&p| p <= 800).collect();
    let forced: Vec<u64> = primes800.iter().cloned().filter(|&p| p <= 167).collect();
    let pool: Vec<u64> = primes800.iter().cloned().filter(|&p| p > 167 && p <= 787).collect();
    assert_eq!((forced.len(), pool.len()), (39, 99));

    // ---- enumerate the 49,961 bases; split by Jacobi ----
    eprintln!("enumerating bases + Jacobi split...");
    let t58: f64 = {
        let mut all: Vec<u64> = primes800.clone();
        all.truncate(58);
        all.iter().map(|&p| 1.0 / p as f64).sum()
    };
    let _ = t58;
    let thr: f64 = 2.0 - forced.iter().map(|&p| 1.0 / p as f64).sum::<f64>();
    let pf: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    let mut dforced = from_u64(1);
    for &p in &forced { dforced = mul_small(&dforced, p); }

    let mut survivors: Vec<Vec<u64>> = Vec::new(); // the 20 chosen pool primes
    let mut prekilled = 0u64;
    let mut count = 0u64;
    // DFS
    let mut stack: Vec<(usize, usize, f64, Vec<u8>)> = vec![(0, 20, 0.0, Vec::new())];
    while let Some((i, need, cur, ch)) = stack.pop() {
        if need == 0 {
            if cur > thr - 1e-9 {
                let mut d = dforced.clone();
                let sel: Vec<u64> = ch.iter().map(|&j| pool[j as usize]).collect();
                for &p in &sel { d = mul_small(&d, p); }
                let full: Vec<u64> = forced.iter().cloned().chain(sel.iter().cloned()).collect();
                let mut ns = from_u64(0);
                for &p in &full { let (q, r) = div_small(&d, p); assert_eq!(r, 0); ns = add_big(&ns, &q); }
                let d2 = mul_small(&d, 2);
                if cmp_big(&ns, &d2) == std::cmp::Ordering::Greater {
                    count += 1;
                    let a = add_big(&ns, &d2);
                    if jacobi_big(&d, &a) == -1 { prekilled += 1; } else { survivors.push(sel); }
                }
            }
            continue;
        }
        if i + need > pool.len() { continue; }
        if cur + pf[i..i + need].iter().sum::<f64>() <= thr - 1e-9 { continue; }
        stack.push((i + 1, need, cur, ch.clone()));
        let mut c2 = ch.clone(); c2.push(i as u8);
        stack.push((i + 1, need - 1, cur + pf[i], c2));
    }
    eprintln!("bases: {} (expect 49961), jacobi-killed: {} (expect 31219), survivors: {} (expect 18742)",
              count, prekilled, survivors.len());
    assert_eq!(count, 49961); assert_eq!(prekilled, 31219); assert_eq!(survivors.len(), 18742);
    survivors.sort();

    // ---- resume ----
    let mut start_idx = 0usize;
    let mut killed = 0u64;
    let mut open = 0u64;
    if let Ok(s) = fs::read_to_string(STATE_FILE) {
        for line in s.lines() {
            if let Some((k, v)) = line.split_once('=') {
                match k.trim() {
                    "next" => start_idx = v.trim().parse().unwrap_or(0),
                    "killed" => killed = v.trim().parse().unwrap_or(0),
                    "open" => open = v.trim().parse().unwrap_or(0),
                    _ => {}
                }
            }
        }
        if start_idx > 0 { eprintln!("resuming at survivor #{}", start_idx); }
    }

    // ---- attack ----
    let start = Instant::now();
    let end_idx = survivors.len().min(max_surv);
    let mut res = fs::OpenOptions::new().create(true).append(true).open(RESULT_FILE).unwrap();
    for idx in start_idx..end_idx {
        let sel = &survivors[idx];
        let mut d = dforced.clone();
        for &p in sel { d = mul_small(&d, p); }
        let full: Vec<u64> = forced.iter().cloned().chain(sel.iter().cloned()).collect();
        let mut ns = from_u64(0);
        for &p in &full { let (q, _r) = div_small(&d, p); ns = add_big(&ns, &q); }
        let d2 = mul_small(&d, 2);
        let a_side = add_big(&ns, &d2);
        let b_side = sub_big(&ns, &d2);

        let mut dead = false;
        'sides: for (tag, x0) in [("A", &a_side), ("B", &b_side)] {
            // coprime basis of found pieces + cofactor
            let mut basis: Vec<(Big, u32)> = Vec::new();
            let mut cof = x0.clone();
            for &p in &tprimes {
                if p < 279 { continue; } // no factors ≤ 277 (rigidity)
                if p * p > 0 && cof.len() == 1 && cof[0] < p * p { break; }
                let mut v = 0u32;
                loop {
                    let (q, r) = div_small(&cof, p);
                    if r != 0 { break; }
                    cof = q; v += 1;
                }
                if v > 0 { basis_insert(&mut basis, from_u64(p), v); }
            }
            // rho on the remaining cofactor
            let mut seeds = [3u64, 5, 7];
            let mut si = 0;
            while !is_one(&cof) && si < seeds.len() {
                if let Some(f) = brent_rho(&cof, seeds[si], budget) {
                    let (q, r) = divide_out(&cof, &f);
                    if is_zero(&r) {
                        // pull ALL copies of f
                        let mut v = 1u32;
                        cof = q;
                        loop {
                            let (q2, r2) = divide_out(&cof, &f);
                            if !is_zero(&r2) { break; }
                            cof = q2; v += 1;
                        }
                        basis_insert(&mut basis, f, v);
                    } else { si += 1; }
                } else { si += 1; }
                seeds[si.min(2)] = seeds[si.min(2)].wrapping_add(4);
            }
            if !is_one(&cof) { basis_insert(&mut basis, cof.clone(), 1); }
            // kill rule: any odd-multiplicity piece with Jacobi (D|piece) = −1
            for (piece, mult) in &basis {
                if mult % 2 == 1 && piece[0] & 1 == 1 && jacobi_big(&d, piece) == -1 {
                    dead = true;
                    let digs = (bit_len(piece) as f64 * 0.30103) as usize + 1;
                    writeln!(res, "KILL base#{} side={} piece~{}digits mult={}", idx, tag, digs, mult).unwrap();
                    break 'sides;
                }
            }
        }
        if dead { killed += 1; } else { open += 1; }

        if (idx + 1) % 25 == 0 || idx + 1 == end_idx {
            let st = format!("next={}\nkilled={}\nopen={}\n", idx + 1, killed, open);
            fs::write("survivor_state.tmp", &st).unwrap();
            fs::rename("survivor_state.tmp", STATE_FILE).unwrap();
            let done = (idx + 1 - start_idx) as f64;
            let el = start.elapsed().as_secs_f64();
            let eta = (end_idx - idx - 1) as f64 * el / done.max(1.0);
            eprint!("\r  {}/{}  killed={}  open={}  {:.2} s/family  ETA {:.0} min   ",
                    idx + 1, end_idx, killed, open, el / done, eta / 60.0);
        }
    }
    eprintln!();
    let total_killed = 31219 + killed;
    let summary = format!(
        "FACTORING ATTACK to survivor #{} (rho budget {}/side): {} more families PROVEN EMPTY, {} still open.\nTOTAL level-60 one-new-prime families closed: {} / 49961 ({:.2}%).\n",
        end_idx, budget, killed, open, total_killed, 100.0 * total_killed as f64 / 49961.0);
    println!("{}", summary);
    let mut f = fs::OpenOptions::new().create(true).append(true).open(RESULT_FILE).unwrap();
    f.write_all(summary.as_bytes()).unwrap();
}
