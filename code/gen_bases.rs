// gen_bases.rs -- generate the level-60 base list consumed by split_sieve.rs, with no Python.
//
// A level-60 single-tail base is a 59-element set S of primes with mass T(S) = sum_{p in S} 1/p > 2.
// Every prime <= 167 lies in S (omitting p caps the mass below 2), and every element is <= 787, so
// S = {p : p <= 167} u (20 primes from (167, 787]).  Exactly 49,961 such sets have T(S) > 2.
//
// The enumeration prunes on f64 mass with a conservative slack, so it never prunes a live branch,
// and every surviving leaf is then tested EXACTLY in integer arithmetic: T(S) > 2 is csum S > 2 * dprod S.
// Floating point therefore decides nothing; it only decides where not to look.
//
// For each base the file records the two Jacobi symbols (D|A) and (D|B), A = N + 2D, B = N - 2D,
// D = dprod S, N = csum S.  split_sieve.rs skips a base when either is -1 (the reciprocity
// certificate of prop:tailkill already empties those families).  Field 4 is a placeholder kept for
// format compatibility with the earlier generator; split_sieve.rs does not read it, so no primality
// test on the ~113-digit A is performed here.
//
// Build: rustc -O -o gen_bases gen_bases.rs
// Run:   ./gen_bases > bases.txt
// Output line: idx kronA kronB 0 p1 p2 ... p59
// Expected: 49,961 lines, 18,742 with both symbols != -1.  Runtime ~1 min.

const L: usize = 8; // 512 bits; D ~ 10^112 ~ 2^372 and A ~ 4D fit with room to spare

#[derive(Clone, Copy, PartialEq, Eq)]
struct Big([u64; L]);

impl Big {
    fn zero() -> Big { Big([0; L]) }
    fn from(v: u64) -> Big { let mut r = Big([0; L]); r.0[0] = v; r }
    fn is_zero(&self) -> bool { self.0.iter().all(|&x| x == 0) }
    fn is_even(&self) -> bool { self.0[0] & 1 == 0 }
    fn bits(&self) -> usize {
        for i in (0..L).rev() { if self.0[i] != 0 { return i * 64 + (64 - self.0[i].leading_zeros() as usize); } }
        0
    }
    fn cmp(&self, o: &Big) -> std::cmp::Ordering {
        for i in (0..L).rev() {
            if self.0[i] != o.0[i] { return self.0[i].cmp(&o.0[i]); }
        }
        std::cmp::Ordering::Equal
    }
    fn mul_small(&self, m: u64) -> Big {
        let mut r = Big::zero(); let mut c: u128 = 0;
        for i in 0..L { let t = self.0[i] as u128 * m as u128 + c; r.0[i] = t as u64; c = t >> 64; }
        assert!(c == 0, "overflow in mul_small"); r
    }
    fn add(&self, o: &Big) -> Big {
        let mut r = Big::zero(); let mut c: u128 = 0;
        for i in 0..L { let t = self.0[i] as u128 + o.0[i] as u128 + c; r.0[i] = t as u64; c = t >> 64; }
        assert!(c == 0, "overflow in add"); r
    }
    fn sub(&self, o: &Big) -> Big { // requires self >= o
        let mut r = Big::zero(); let mut b: i128 = 0;
        for i in 0..L {
            let t = self.0[i] as i128 - o.0[i] as i128 - b;
            if t < 0 { r.0[i] = (t + (1i128 << 64)) as u64; b = 1; } else { r.0[i] = t as u64; b = 0; }
        }
        assert!(b == 0, "underflow in sub"); r
    }
    fn shl1(&self) -> Big {
        let mut r = Big::zero(); let mut c = 0u64;
        for i in 0..L { r.0[i] = (self.0[i] << 1) | c; c = self.0[i] >> 63; }
        assert!(c == 0, "overflow in shl1"); r
    }
    fn shr1(&self) -> Big {
        let mut r = Big::zero();
        for i in 0..L { r.0[i] = self.0[i] >> 1; if i + 1 < L { r.0[i] |= self.0[i + 1] << 63; } }
        r
    }
    fn divrem_small(&self, d: u64) -> (Big, u64) {
        let mut q = Big::zero(); let mut rem: u128 = 0;
        for i in (0..L).rev() {
            let cur = (rem << 64) | self.0[i] as u128;
            q.0[i] = (cur / d as u128) as u64; rem = cur % d as u128;
        }
        (q, rem as u64)
    }
    /// Binary long division remainder: self mod m, for m != 0.
    fn rem(&self, m: &Big) -> Big {
        if self.cmp(m) == std::cmp::Ordering::Less { return *self; }
        let sb = self.bits(); let mb = m.bits();
        let mut shifted = *m; let mut k = 0usize;
        while k + mb < sb { shifted = shifted.shl1(); k += 1; }
        let mut r = *self;
        loop {
            if r.cmp(&shifted) != std::cmp::Ordering::Less { r = r.sub(&shifted); }
            if k == 0 { break; }
            shifted = shifted.shr1(); k -= 1;
        }
        r
    }
}

/// Jacobi symbol (a | n) for odd n > 0.
fn jacobi(a0: &Big, n0: &Big) -> i32 {
    let mut a = a0.rem(n0); let mut n = *n0; let mut t = 1i32;
    while !a.is_zero() {
        while a.is_even() {
            a = a.shr1();
            let r = n.0[0] & 7;
            if r == 3 || r == 5 { t = -t; }
        }
        std::mem::swap(&mut a, &mut n);
        if (a.0[0] & 3) == 3 && (n.0[0] & 3) == 3 { t = -t; }
        a = a.rem(&n);
    }
    if n == Big::from(1) { t } else { 0 }
}

fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    let mut d = 2u64;
    while d * d <= n { if n % d == 0 { return false; } d += 1; }
    true
}

fn main() {
    let forced: Vec<u64> = (2..168).filter(|&p| is_prime(p)).collect();
    let pool: Vec<u64> = (168..801).filter(|&p| is_prime(p)).collect();
    const KK: usize = 20;
    assert_eq!(forced.len(), 39, "forced-prime count");
    let thr: f64 = 2.0 - forced.iter().map(|&p| 1.0 / p as f64).sum::<f64>();
    let inv: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    let np = pool.len();
    // suffix sums of the largest available reciprocals, for the branch bound
    let mut cum = vec![0.0f64; np + 1];
    for i in 0..np { cum[i + 1] = cum[i] + inv[i]; }
    let eps = 1e-12; // conservative slack: never prune a branch that could still qualify

    let mut chosen: Vec<usize> = Vec::with_capacity(KK);
    let mut out = String::new();
    let mut idx = 0usize; let mut kept = 0usize; let mut both = 0usize;

    fn dfs(i: usize, need: usize, cur: f64, chosen: &mut Vec<usize>, pool: &Vec<u64>, inv: &Vec<f64>,
           cum: &Vec<f64>, thr: f64, eps: f64, forced: &Vec<u64>, np: usize,
           idx: &mut usize, kept: &mut usize, both: &mut usize, out: &mut String) {
        if need == 0 {
            *idx += 1;
            // exact test: T(S) > 2  <=>  csum S > 2 * dprod S
            let mut s: Vec<u64> = forced.clone();
            for &t in chosen.iter() { s.push(pool[t]); }
            let mut d = Big::from(1);
            for &p in &s { d = d.mul_small(p); }
            let mut n = Big::zero();
            for &p in &s {
                let (q, r) = d.divrem_small(p);
                assert!(r == 0);
                n = n.add(&q);
            }
            let two_d = d.shl1();
            if n.cmp(&two_d) != std::cmp::Ordering::Greater { return; } // mass not above 2
            *kept += 1;
            let a = n.add(&two_d);
            let b = n.sub(&two_d);
            let ka = jacobi(&d, &a);
            let kb = jacobi(&d, &b);
            if ka != -1 && kb != -1 { *both += 1; }
            out.push_str(&format!("{} {} {} 0", *kept, ka, kb));
            for &p in &s { out.push_str(&format!(" {}", p)); }
            out.push('\n');
            return;
        }
        if i + need > np { return; }
        // best possible completion from here
        let hi = cum[std::cmp::min(i + need, np)] - cum[i];
        if cur + hi <= thr - eps { return; }
        chosen.push(i);
        dfs(i + 1, need - 1, cur + inv[i], chosen, pool, inv, cum, thr, eps, forced, np, idx, kept, both, out);
        chosen.pop();
        dfs(i + 1, need, cur, chosen, pool, inv, cum, thr, eps, forced, np, idx, kept, both, out);
    }

    dfs(0, KK, 0.0, &mut chosen, &pool, &inv, &cum, thr, eps, &forced, np,
        &mut idx, &mut kept, &mut both, &mut out);
    print!("{}", out);
    eprintln!("leaves reached {}  bases with T(S) > 2 (exact): {}  both Jacobi symbols != -1: {}",
              idx, kept, both);
}
