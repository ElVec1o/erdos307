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


fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut d = 2; while d*d <= n { if n % d == 0 { return false; } d += 1; } true }

/// Legendre (a|l) for small odd prime l, by Euler's criterion.
fn legendre(a: u64, l: u64) -> i32 {
    let a = a % l; if a == 0 { return 0; }
    let mut r = 1u64; let mut b = a; let mut e = (l - 1) / 2;
    while e > 0 { if e & 1 == 1 { r = (r as u128 * b as u128 % l as u128) as u64; } b = (b as u128 * b as u128 % l as u128) as u64; e >>= 1; }
    if r == 1 { 1 } else { -1 }
}

fn main() {
    // stdin: the bases file (idx kronA kronB Aprime p1..p59). Emit the ones NOT killed.
    // Certificate (prop:tailkill / certificate_sound): a prime l dividing A_S (or B_S) with
    // (D_S|l) = -1 empties the family for every tail prime q. Trial division to 10^6.
    let lim: u64 = 1_000_000;
    let smalls: Vec<u64> = (2..lim).filter(|&p| is_prime(p)).collect();
    eprintln!("trial-division primes below {}: {}", lim, smalls.len());
    let mut seen = 0usize; let mut killed = 0usize; let mut kept = 0usize;
    let mut out = String::new();
    use std::io::BufRead;
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let v: Vec<i64> = line.split_whitespace().map(|x| x.parse().unwrap()).collect();
        let (ka, kb) = (v[1], v[2]);
        if ka == -1 || kb == -1 { continue; }   // already killed by the Jacobi symbol
        seen += 1;
        let s: Vec<u64> = v[4..].iter().map(|&x| x as u64).collect();
        let mut d = Big::from(1); for &p in &s { d = d.mul_small(p); }
        let mut n = Big::zero(); for &p in &s { let (q, r) = d.divrem_small(p); assert!(r == 0); n = n.add(&q); }
        let two_d = d.shl1();
        let a = n.add(&two_d);
        let b = if n.cmp(&two_d) == std::cmp::Ordering::Greater { n.sub(&two_d) } else { two_d.sub(&n) };
        let mut dead = false;
        for &l in &smalls {
            if dead { break; }
            let (_, ra) = a.divrem_small(l);
            let (_, rb) = b.divrem_small(l);
            if ra != 0 && rb != 0 { continue; }
            let (_, dl) = d.divrem_small(l);
            if legendre(dl, l) == -1 { dead = true; }
        }
        if dead { killed += 1; } else { kept += 1; out.push_str(&line); out.push('\n'); }
        if seen % 2000 == 0 { eprintln!("  {} seen, {} killed, {} kept", seen, killed, kept); }
    }
    print!("{}", out);
    eprintln!("DONE: {} Jacobi survivors, {} killed by the certificate, {} still open", seen, killed, kept);
}
