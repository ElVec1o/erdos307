// split_sieve.rs -- the split-anatomy sieve for level-60 single-tail families S u {q}.
//
// Write a 2-cycle on the family as a = q*alpha, b = beta with alpha*beta = D = prod S and T = primes of
// alpha.  Then d(b) = a gives  d(beta) = q*alpha  (so alpha | d(beta)), and d(a) = b gives
// beta - alpha = q*d(alpha).  By the anatomy lemma, alpha | d(beta) is:  for every r in T,
//     sum_{p in S\T} p^{-1} == 0 (mod r),   equivalently   sum_{p in T, p != r} p^{-1} == s_r (mod r)
// with s_r = sum_{p in S, p != r} p^{-1} mod r.  Each condition costs ~1/r, so the expected number of
// surviving splits is prod_{p in S}(1 + 1/p) ~ 6 out of 2^59, concentrated at |T| <= 6.  This program
// enumerates every T with 1 <= |T| <= kmax, applies the congruences, and for each survivor performs the
// exact checks: alpha | d(beta) (must agree), q = d(beta)/alpha, and (i) beta - alpha == q*d(alpha).
// Every survivor is written out; (i)-hits are flagged and are the only candidates for a 2-cycle
// (q must additionally be prime -- tested afterwards in PARI/GP, there are expected to be none).
// Needs NO primality or factorisation of A_S, unlike prop:immunedecide.
//
// Build: rustc -O -o split_sieve split_sieve.rs
// Run:   ./split_sieve bases.txt <threads> <kmax> [--only 268,3]
//   bases.txt lines: idx kronA kronB Aprime p1 ... p59   (from gen_bases.py); bases with
//   kronA == -1 or kronB == -1 are Jacobi-killed and skipped.
// Checkpoint: done.txt and results.txt are rewritten atomically (tmp file, then rename) every 30 s
// and at exit; on restart the bases in done.txt are skipped and results.txt is kept.
use std::collections::HashSet;
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Instant;

const L: usize = 8; // 512-bit limbs
#[derive(Clone, Copy, PartialEq, Eq)]
struct Big([u64; L]);
impl Big {
    fn from(v: u64) -> Big { let mut r = Big([0; L]); r.0[0] = v; r }
    fn is_zero(&self) -> bool { self.0.iter().all(|&x| x == 0) }
    fn mul_small(&self, m: u64) -> Big {
        let mut r = Big([0; L]); let mut c: u128 = 0;
        for i in 0..L { let t = self.0[i] as u128 * m as u128 + c; r.0[i] = t as u64; c = t >> 64; }
        assert!(c == 0, "Big overflow in mul_small"); r
    }
    fn add(&self, o: &Big) -> Big {
        let mut r = Big([0; L]); let mut c: u128 = 0;
        for i in 0..L { let t = self.0[i] as u128 + o.0[i] as u128 + c; r.0[i] = t as u64; c = t >> 64; }
        assert!(c == 0, "Big overflow in add"); r
    }
    /// Full-width subtraction, required once beta and alpha are both Big.
    fn sub(&self, o: &Big) -> Big {
        let mut r = [0u64; L]; let mut b: i128 = 0;
        for i in 0..L {
            let t = self.0[i] as i128 - o.0[i] as i128 - b;
            if t < 0 { r[i] = (t + (1i128 << 64)) as u64; b = 1; } else { r[i] = t as u64; b = 0; }
        }
        assert!(b == 0, "Big underflow in sub"); Big(r)
    }
    fn sub_small(&self, m: u64) -> Big {
        let mut r = *self; let mut b: u128 = m as u128;
        for i in 0..L { let t = r.0[i] as u128; if t >= b { r.0[i] = (t - b) as u64; b = 0; break; } else { r.0[i] = ((1u128 << 64) + t - b) as u64; b = 1; } }
        assert!(b == 0, "Big underflow in sub_small"); r
    }
    fn divrem_small(&self, d: u64) -> (Big, u64) {
        let mut q = Big([0; L]); let mut rem: u128 = 0;
        for i in (0..L).rev() { let cur = (rem << 64) | self.0[i] as u128; q.0[i] = (cur / d as u128) as u64; rem = cur % d as u128; }
        (q, rem as u64)
    }
    /// Schoolbook product. Asserts on overflow rather than wrapping: alpha^2 and d(alpha)*d(beta)
    /// are both below D here, so 512 bits suffice, and a violated assert means the caller is wrong.
    fn mul(&self, o: &Big) -> Big {
        let mut r = [0u64; L];
        for i in 0..L {
            if self.0[i] == 0 { continue; }
            let mut c: u128 = 0;
            for j in 0..(L - i) {
                let t = self.0[i] as u128 * o.0[j] as u128 + r[i + j] as u128 + c;
                r[i + j] = t as u64; c = t >> 64;
            }
            assert!(c == 0, "Big overflow in mul");
            for j in (L - i)..L { assert!(o.0[j] == 0, "Big overflow in mul"); }
        }
        Big(r)
    }
    fn bits(&self) -> usize {
        for i in (0..L).rev() { if self.0[i] != 0 { return i * 64 + (64 - self.0[i].leading_zeros() as usize); } }
        0
    }
    fn cmp_big(&self, o: &Big) -> std::cmp::Ordering {
        for i in (0..L).rev() { if self.0[i] != o.0[i] { return self.0[i].cmp(&o.0[i]); } }
        std::cmp::Ordering::Equal
    }
    fn shl1b(&self) -> Big {
        let mut r = [0u64; L]; let mut c = 0u64;
        for i in 0..L { r[i] = (self.0[i] << 1) | c; c = self.0[i] >> 63; }
        assert!(c == 0, "Big overflow in shl1b"); Big(r)
    }
    fn shr1b(&self) -> Big {
        let mut r = [0u64; L];
        for i in 0..L { r[i] = self.0[i] >> 1; if i + 1 < L { r[i] |= self.0[i + 1] << 63; } }
        Big(r)
    }
    /// Binary long division: (quotient, remainder) of self by m. Needed once alpha exceeds u64,
    /// which happens from |T| ~ 10 upward and would silently wrap in the old u64 path.
    fn divrem(&self, m: &Big) -> (Big, Big) {
        assert!(!m.is_zero(), "divide by zero");
        if self.cmp_big(m) == std::cmp::Ordering::Less { return (Big([0; L]), *self); }
        let sb = self.bits(); let mb = m.bits();
        let mut sh = *m; let mut k = 0usize;
        while k + mb < sb { sh = sh.shl1b(); k += 1; }
        let mut r = *self; let mut q = Big([0; L]);
        loop {
            q = q.shl1b();
            if r.cmp_big(&sh) != std::cmp::Ordering::Less { r = r.sub(&sh); q.0[0] |= 1; }
            if k == 0 { break; }
            sh = sh.shr1b(); k -= 1;
        }
        (q, r)
    }
    fn to_dec(&self) -> String {
        if self.is_zero() { return "0".into(); }
        let mut parts = Vec::new(); let mut x = *self;
        while !x.is_zero() { let (q, r) = x.divrem_small(1_000_000_000_000_000_000); parts.push(r); x = q; }
        let mut s = format!("{}", parts.pop().unwrap());
        while let Some(p) = parts.pop() { s.push_str(&format!("{:018}", p)); }
        s
    }
}

fn modinv(a: u64, m: u64) -> u64 { // m prime
    let (mut t, mut nt, mut r, mut nr) = (0i128, 1i128, m as i128, (a % m) as i128);
    while nr != 0 { let qq = r / nr; t -= qq * nt; std::mem::swap(&mut t, &mut nt); r -= qq * nr; std::mem::swap(&mut r, &mut nr); }
    assert!(r == 1); ((t % m as i128 + m as i128) % m as i128) as u64
}

struct Base { idx: usize, s: Vec<u64> }

struct Shared { done: Vec<usize>, results: Vec<String>, surv: u64, ihits: u64 }

fn checkpoint(sh: &Mutex<Shared>) {
    let g = sh.lock().unwrap();
    // A checkpoint write must never take the run down with it. The first version unwrapped here,
    // so a full disk poisoned the shared mutex and every worker died with it, discarding hours of
    // completed work that was already safely on disk. On failure this reports and returns: the
    // committed file is untouched, because the write goes to a temporary and is renamed only on
    // success, and the next checkpoint can succeed once space is free.
    let w = |name: &str, lines: &[String]| {
        let tmp = format!("{}.tmp", name);
        let attempt = (|| -> std::io::Result<()> {
            let mut f = std::fs::File::create(&tmp)?;
            for l in lines { writeln!(f, "{}", l)?; }
            f.sync_all()?;
            std::fs::rename(&tmp, name)
        })();
        if let Err(e) = attempt {
            eprintln!("  WARNING: checkpoint to {} failed ({}); run continues, will retry", name, e);
            let _ = std::fs::remove_file(&tmp);
        }
    };
    w("done.txt", &g.done.iter().map(|d| d.to_string()).collect::<Vec<_>>());
    w("results.txt", &g.results);
}

fn process(b: &Base, kmax: usize, out: &mut Vec<String>) -> (u64, u64) {
    let n = b.s.len(); let tb = Instant::now();
    // inverses and targets
    let mut inv = vec![vec![0u64; n]; n]; let mut s_r = vec![0u64; n];
    for i in 0..n { let r = b.s[i]; let mut acc = 0u64; for j in 0..n { if i != j { inv[i][j] = modinv(b.s[j], r); acc = (acc + inv[i][j]) % r; } } s_r[i] = acc; }
    let mut d = Big::from(1); for &p in &b.s { d = d.mul_small(p); }
    let mut t: Vec<usize> = Vec::with_capacity(kmax); let mut sums: Vec<u64> = Vec::with_capacity(kmax);
    let mut nsurv = 0u64; let mut nhit = 0u64;
    fn rec(start: usize, b: &Base, inv: &Vec<Vec<u64>>, s_r: &Vec<u64>, d: &Big, kmax: usize, t: &mut Vec<usize>, sums: &mut Vec<u64>, out: &mut Vec<String>, nsurv: &mut u64, nhit: &mut u64) {
        let n = b.s.len();
        for j in start..n {
            // push j
            let mut own = 0u64;
            for m in 0..t.len() { sums[m] += inv[t[m]][j]; own += inv[j][t[m]]; }
            t.push(j); sums.push(own);
            // test (ii) on this T
            let mut ok = true;
            for m in 0..t.len() { let r = b.s[t[m]]; if sums[m] % r != s_r[t[m]] { ok = false; break; } }
            if ok {
                // alpha and beta are built as products, never by division, so nothing here is
                // limited to u64: at |T| ~ 10 the old u64 alpha would have wrapped silently.
                let mut alpha = Big::from(1);
                for &i in t.iter() { alpha = alpha.mul_small(b.s[i]); }
                let mut beta = Big::from(1);
                for i in 0..n { if !t.contains(&i) { beta = beta.mul_small(b.s[i]); } }
                let mut dbeta = Big::from(0);
                for i in 0..n { if !t.contains(&i) { let (qq, r) = beta.divrem_small(b.s[i]); assert!(r == 0); dbeta = dbeta.add(&qq); } }
                let (q, r2) = dbeta.divrem(&alpha);
                assert!(r2.is_zero(), "congruence test and exact divisibility disagree at base {}", b.idx);
                let mut dalpha = Big::from(0);
                for &i in t.iter() { let (qq, r) = alpha.divrem_small(b.s[i]); assert!(r == 0); dalpha = dalpha.add(&qq); }
                let lhs = beta.sub(&alpha); let rhs = q.mul(&dalpha);
                let iok = lhs == rhs;
                *nsurv += 1; if iok { *nhit += 1; }
                let tp: Vec<String> = t.iter().map(|&i| b.s[i].to_string()).collect();
                out.push(format!("base={} T={} q={} i_ok={}", b.idx, tp.join(","), q.to_dec(), if iok { 1 } else { 0 }));
            }
            if t.len() < kmax { rec(j + 1, b, inv, s_r, d, kmax, t, sums, out, nsurv, nhit); }
            // pop j
            t.pop(); sums.pop();
            for m in 0..t.len() { sums[m] -= inv[t[m]][j]; }
        }
    }
    rec(0, b, &inv, &s_r, &d, kmax, &mut t, &mut sums, out, &mut nsurv, &mut nhit);
    out.push(format!("DONE base={} nsurv={} ihits={} secs={:.1}", b.idx, nsurv, nhit, tb.elapsed().as_secs_f64()));
    (nsurv, nhit)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = &args[1]; let nthreads: usize = args[2].parse().unwrap(); let kmax: usize = args[3].parse().unwrap();
    let mut only: Option<HashSet<usize>> = None;
    if args.len() > 5 && args[4] == "--only" { only = Some(args[5].split(',').map(|x| x.parse().unwrap()).collect()); }
    let mut bases = Vec::new();
    for line in std::io::BufReader::new(std::fs::File::open(path).unwrap()).lines() {
        let line = line.unwrap(); let v: Vec<i64> = line.split_whitespace().map(|x| x.parse().unwrap()).collect();
        let (idx, ka, kb) = (v[0] as usize, v[1], v[2]);
        if ka == -1 || kb == -1 { continue; }
        if let Some(o) = &only { if !o.contains(&idx) { continue; } }
        bases.push(Base { idx, s: v[4..].iter().map(|&x| x as u64).collect() });
    }
    let mut done_set: HashSet<usize> = HashSet::new(); let mut prev_results = Vec::new();
    if let Ok(f) = std::fs::File::open("done.txt") { for l in std::io::BufReader::new(f).lines() { if let Ok(x) = l { if let Ok(i) = x.trim().parse() { done_set.insert(i); } } } }
    if let Ok(f) = std::fs::File::open("results.txt") { for l in std::io::BufReader::new(f).lines() { if let Ok(x) = l { prev_results.push(x); } } }
    let todo: Vec<&Base> = bases.iter().filter(|b| !done_set.contains(&b.idx)).collect();
    let total = todo.len();
    eprintln!("families in scope {}  already done {}  to do {}  kmax {}  threads {}", bases.len(), done_set.len(), total, kmax, nthreads);
    let sh = Mutex::new(Shared { done: done_set.iter().cloned().collect(), results: prev_results, surv: 0, ihits: 0 });
    let next = AtomicUsize::new(0); let finished = AtomicUsize::new(0); let t0 = Instant::now();
    let stop = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|sc| {
        // checkpoint thread
        // exits on its own once every base is finished, so the scope can close (a stop flag set after
        // the scope would deadlock: the scope waits for this thread)
        sc.spawn(|| { loop { for _ in 0..30 { std::thread::sleep(std::time::Duration::from_secs(1)); if finished.load(Ordering::Relaxed) >= total || stop.load(Ordering::Relaxed) { return; } } checkpoint(&sh); } });
        for _ in 0..nthreads { sc.spawn(|| { loop {
            let i = next.fetch_add(1, Ordering::Relaxed); if i >= total { break; }
            let b = todo[i]; let mut out = Vec::new();
            let (ns, nh) = process(b, kmax, &mut out);
            { let mut g = sh.lock().unwrap(); g.results.extend(out); g.done.push(b.idx); g.surv += ns; g.ihits += nh; }
            let f = finished.fetch_add(1, Ordering::Relaxed) + 1;
            if f % 25 == 0 || f == total {
                let el = t0.elapsed().as_secs_f64(); let g = sh.lock().unwrap();
                eprintln!("  done {}/{}  {:.2} bases/s  elapsed {:.0}s  ETA {:.0}s  survivors {}  (i)-hits {}", f, total, f as f64 / el, el, el * (total - f) as f64 / f as f64, g.surv, g.ihits);
            }
        } }); }
    });
    stop.store(true, Ordering::Relaxed);
    checkpoint(&sh);
    let g = sh.lock().unwrap();
    println!("COMPLETE: families {}  survivors {}  (i)-hits {}  ({:.0}s)", total, g.surv, g.ihits, t0.elapsed().as_secs_f64());
}
