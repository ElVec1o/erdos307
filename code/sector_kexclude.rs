// sector_kexclude.rs -- decide whether omega(e) = k is possible in a GIVEN sector d of the two-cycle.
// Generalises sector42_k64.rs: the forced-prime identity is l*(dR - d'R') = d'R + d^2 for any squarefree d.
// Build: rustc -O -o sector_kexclude sector_kexclude.rs   Run: ./sector_kexclude <d> <d'> <k> <phase> [threads] [N]
// Sector d = 42:  e = 42 + 41 q,  e' = 42 q,  supp(e) avoids {2,3,7,41},  equivalently  42 e - 41 e' = 1764.
// Facts (checked exactly in sector42_k64.gp): with A_j the allowed primes, S_61 + 3/1231 < 42/41, so a
// 64-set has at most two primes > A_197 = 1229.
//   Phase 1 (<= 1 large prime): S = the 63 primes <= 1229, sigma(S) in [42/41 - 1/A_64, 42/41);
//            the last prime is forced:  l = (41 R + 1764) / (42 R - 41 R'),  R = prod S.
//   Phase 2 (two large primes l2 <= l1): S = the 62 primes <= 1229, sigma(S) in [42/41 - 2/1231, 42/41);
//            l2 in (1/delta, 2/delta], delta = 42/41 - sigma(S); then l1 is forced by the same formula from S u {l2}.
// Mass pruning in f64 with margins; the forced-prime test is a double-double prefilter with a conservative
// band (|1/delta - nearest integer| < 1e-4, or delta < 1e-11), then exact fixed-width integer arithmetic.
// Every integer l found is written to k64_phase<n>_results.txt.  Checkpoint: k64_phase<n>_done.txt (delete it when the
// source changes: items are keyed by index only).  'leaves' counts every full-size set reached by the pruned search;
// 'in_window' counts those whose mass lies in the window, i.e. the sets the proof actually tests.
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Mutex;
use std::io::Write;
#[derive(Clone, Copy)] struct DD { hi: f64, lo: f64 }
fn two_sum(a: f64, b: f64) -> (f64, f64) { let s = a + b; let bb = s - a; (s, (a - (s - bb)) + (b - bb)) }
fn dd_add(x: DD, y: DD) -> DD { let (s, e) = two_sum(x.hi, y.hi); let e = e + x.lo + y.lo; let (h, l) = two_sum(s, e); DD { hi: h, lo: l } }
fn dd_neg(x: DD) -> DD { DD { hi: -x.hi, lo: -x.lo } }
fn dd_recip(p: u64) -> DD { let hi = 1.0 / p as f64; let lo = (-hi).mul_add(p as f64, 1.0) / p as f64; DD { hi, lo } }
fn dd_ratio(a: f64, b: f64) -> DD { let hi = a / b; let lo = (-hi).mul_add(b, a) / b; DD { hi, lo } }
fn is_prime_small(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i * i <= n { if n % i == 0 { return false; } i += 1; } true }
fn mulmod(a: u64, b: u64, m: u64) -> u64 { ((a as u128 * b as u128) % m as u128) as u64 }
fn powmod(mut a: u64, mut e: u64, m: u64) -> u64 { let mut r = 1; a %= m; while e > 0 { if e & 1 == 1 { r = mulmod(r, a, m); } a = mulmod(a, a, m); e >>= 1; } r }
fn is_prime(n: u64) -> bool { // deterministic Miller-Rabin, valid for all n < 2^64
    if n < 2 { return false; } for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] { if n % p == 0 { return n == p; } }
    let mut d = n - 1; let mut s = 0; while d % 2 == 0 { d /= 2; s += 1; }
    'w: for &a in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] { let mut x = powmod(a, d, n); if x == 1 || x == n - 1 { continue; }
        for _ in 1..s { x = mulmod(x, x, n); if x == n - 1 { continue 'w; } } return false; } true }
struct Ctx { d: u64, dp: u64, d2: Big, allowed: Vec<u64>, inv: Vec<DD>, invf: Vec<f64>, pre_max: Vec<Vec<f64>>, suf_min: Vec<Vec<f64>>, t: DD,
    leaves: AtomicU64, in_window: AtomicU64, exact: AtomicU64, found: AtomicU64, min_delta: AtomicU64, max_hi2: AtomicU64, results: Mutex<std::fs::File> }
#[derive(Clone, Copy, PartialEq, Eq)] struct Big([u64; 16]);
impl Big {
    fn from_u64(x: u64) -> Big { let mut b = Big([0; 16]); b.0[0] = x; b }
    fn is_zero(&self) -> bool { self.0.iter().all(|&l| l == 0) }
    fn mul_small(&self, m: u64) -> Big { let mut r = Big([0; 16]); let mut c: u128 = 0;
        for i in 0..16 { let t = self.0[i] as u128 * m as u128 + c; r.0[i] = t as u64; c = t >> 64; } assert!(c == 0, "overflow"); r }
    fn add(&self, o: &Big) -> Big { let mut r = Big([0; 16]); let mut c: u128 = 0;
        for i in 0..16 { let t = self.0[i] as u128 + o.0[i] as u128 + c; r.0[i] = t as u64; c = t >> 64; } assert!(c == 0, "overflow"); r }
    fn cmp(&self, o: &Big) -> std::cmp::Ordering { for i in (0..16).rev() { if self.0[i] != o.0[i] { return self.0[i].cmp(&o.0[i]); } } std::cmp::Ordering::Equal }
    fn sub(&self, o: &Big) -> Big { let mut r = Big([0; 16]); let mut br: i128 = 0; // requires self >= o
        for i in 0..16 { let t = self.0[i] as i128 - o.0[i] as i128 - br; if t < 0 { r.0[i] = (t + (1i128 << 64)) as u64; br = 1; } else { r.0[i] = t as u64; br = 0; } } r }
    fn bits(&self) -> u32 { for i in (0..16).rev() { if self.0[i] != 0 { return i as u32 * 64 + 64 - self.0[i].leading_zeros(); } } 0 }
    fn shl1(&self) -> Big { let mut r = Big([0; 16]); let mut c = 0u64; for i in 0..16 { r.0[i] = (self.0[i] << 1) | c; c = self.0[i] >> 63; } r }
    fn bit(&self, k: u32) -> bool { (self.0[(k / 64) as usize] >> (k % 64)) & 1 == 1 }
    fn divrem(&self, d: &Big) -> (Big, Big) { // binary long division
        let mut q = Big([0; 16]); let mut r = Big([0; 16]);
        for k in (0..self.bits()).rev() { r = r.shl1(); if self.bit(k) { r.0[0] |= 1; }
            if r.cmp(d) != std::cmp::Ordering::Less { r = r.sub(d); q.0[(k / 64) as usize] |= 1 << (k % 64); } }
        (q, r) }
    fn to_string(&self) -> String { let mut s = String::new(); let mut x = *self; let ten = Big::from_u64(10);
        if x.is_zero() { return "0".into(); } while !x.is_zero() { let (q, r) = x.divrem(&ten); s.push((b'0' + r.0[0] as u8) as char); x = q; } s.chars().rev().collect() }
    fn mod_small(&self, m: u64) -> u64 { let mut r: u128 = 0; for i in (0..16).rev() { r = ((r << 64) | self.0[i] as u128) % m as u128; } r as u64 }
}
fn prime_by_trial_mod(x: &Big) -> Option<bool> { // Some(true) if fits u64 and is prime, Some(false) if fits and not, None if too large
    if x.bits() > 64 { return None; } Some(is_prime(x.0[0])) }
// exact forced-prime test: Some(l) if (42R - 41R') divides (41R + 1764) with positive quotient
fn forced(s: &[u64], d: u64, dp: u64, d2: &Big) -> Option<Big> {
    let mut r = Big::from_u64(1); let mut rp = Big::from_u64(0);
    for &p in s { rp = rp.mul_small(p).add(&r); r = r.mul_small(p); }
    let a = r.mul_small(d); let b = rp.mul_small(dp);
    if a.cmp(&b) != std::cmp::Ordering::Greater { return None; }
    let delta = a.sub(&b);
    let num = rp_num(&r, dp, d2);
    let (q, rem) = num.divrem(&delta);
    if rem.is_zero() { Some(q) } else { None }
}
fn rp_num(r: &Big, dp: u64, d2: &Big) -> Big { r.mul_small(dp).add(d2) }
fn leaf_test(ctx: &Ctx, s: &[u64], sigma: DD, tag: &str) {
    let delta = dd_add(ctx.t, dd_neg(sigma));
    let need_exact = if delta.hi <= 1e-11 { true } else {
        let x = (1.0 / delta.hi) * (1.0 - delta.lo / delta.hi); (x - x.round()).abs() < 1e-4 };
    if !need_exact { return; }
    ctx.exact.fetch_add(1, Ordering::Relaxed);
    if let Some(l) = forced(s, ctx.d, ctx.dp, &ctx.d2) {
        ctx.found.fetch_add(1, Ordering::Relaxed);
        let mut f = ctx.results.lock().unwrap();
        writeln!(f, "{} S={:?} l={} l_prime_if_u64={:?}", tag, s, l.to_string(), prime_by_trial_mod(&l)).unwrap();
    }
}
fn dfs(ctx: &Ctx, i: usize, need: usize, mass: f64, sig: DD, s: &mut Vec<u64>, lo: f64, hi: f64, n: usize, phase2: bool) {
    if need == 0 { ctx.leaves.fetch_add(1, Ordering::Relaxed); if mass >= lo - 1e-9 && mass < hi + 1e-9 { ctx.in_window.fetch_add(1, Ordering::Relaxed); if phase2 { phase2_leaf(ctx, s, sig) } else { leaf_test(ctx, s, sig, "P1") } } return; }
    if i + need > n { return; }
    let maxm = mass + ctx.pre_max[i][need]; let minm = mass + ctx.suf_min[i][need];
    if maxm < lo - 1e-9 || minm >= hi + 1e-9 { return; }
    let p = ctx.allowed[i]; s.push(p);
    dfs(ctx, i + 1, need - 1, mass + ctx.invf[i], dd_add(sig, ctx.inv[i]), s, lo, hi, n, phase2);
    s.pop();
    dfs(ctx, i + 1, need, mass, sig, s, lo, hi, n, phase2);
}
fn phase2_leaf(ctx: &Ctx, s: &mut Vec<u64>, sig: DD) {
    let allowed_max = *ctx.allowed.last().unwrap();
    let delta = dd_add(ctx.t, dd_neg(sig));
    // Soundness guard: delta = Delta(R)/(41 R) is an exact positive rational whenever the set is feasible, but it could in
    // principle be below double-double resolution.  Any set with delta.hi <= 1e-11 is resolved exactly and reported;
    // if Delta(R) > 0 there, the l_2 range (1/delta, 2/delta] is too large to enumerate and the run is NOT a proof.
    if delta.hi <= 1e-11 {
        let mut r = Big::from_u64(1); let mut rp = Big::from_u64(0); for &p in s.iter() { rp = rp.mul_small(p).add(&r); r = r.mul_small(p); }
        let pos = r.mul_small(ctx.d).cmp(&rp.mul_small(ctx.dp)) == std::cmp::Ordering::Greater;
        let mut f = ctx.results.lock().unwrap(); writeln!(f, "P2-TINY-DELTA S={:?} delta.hi={:e} Delta_positive={} {}", s, delta.hi, pos, if pos { "UNRESOLVED" } else { "infeasible (sigma(S) >= 42/41)" }).unwrap();
        if pos { ctx.found.fetch_add(1, Ordering::Relaxed); } return; }
    // track the smallest delta seen (as bits of f64) and the largest l_2 upper bound
    let bits = delta.hi.to_bits(); ctx.min_delta.fetch_min(bits, Ordering::Relaxed);
    let lo2 = ((1.0 / delta.hi).floor() as u64).max(allowed_max + 1); let hi2 = (2.0 / delta.hi).floor() as u64 + 2;
    ctx.max_hi2.fetch_max(hi2, Ordering::Relaxed);
    for l2 in lo2..=hi2 { if !is_prime(l2) { continue; }
        // No sign test here: a true l_1 may be so large that delta - 1/l_2 is below double-double resolution.
        // leaf_test routes any delta.hi <= 1e-11 (including <= 0) to the exact integer test, which rejects Delta <= 0.
        s.push(l2); leaf_test(ctx, s, dd_add(sig, dd_recip(l2)), "P2"); s.pop(); }
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let d: u64 = args[1].parse().unwrap(); let dp: u64 = args[2].parse().unwrap();
    let kk: usize = args[3].parse().unwrap(); let phase: u32 = args[4].parse().unwrap();
    let nthreads: usize = args.get(5).map(|s| s.parse().unwrap()).unwrap_or(8);
    let mut allowed = vec![]; let mut p = 2u64; while allowed.len() < 400 { if is_prime_small(p) && d % p != 0 && dp % p != 0 { allowed.push(p); } p += 1; }
    let n = args.get(6).map(|s| s.parse().unwrap()).unwrap_or(197usize);
    let a_next = allowed[n]; // A_{N+1}, the first prime beyond the truncation
    allowed.truncate(n);
    let invf: Vec<f64> = allowed.iter().map(|&q| 1.0 / q as f64).collect(); let inv: Vec<DD> = allowed.iter().map(|&q| dd_recip(q)).collect();
    // reorder: split primes (original indices SPLIT0..SPLIT0+D) first, then the rest in increasing order
    const D: usize = 16; let split0: usize = (n / 5).min(n.saturating_sub(D));
    let order: Vec<usize> = (split0..split0 + D).chain((0..n).filter(|&j| j < split0 || j >= split0 + D)).collect();
    let allowed: Vec<u64> = order.iter().map(|&j| allowed[j]).collect();
    let invf: Vec<f64> = order.iter().map(|&j| invf[j]).collect(); let inv: Vec<DD> = order.iter().map(|&j| inv[j]).collect();
    let kmax = kk + 2; // pruning tables must cover every count actually requested
    let mut pre_max = vec![vec![0.0; kmax]; n + 1]; let mut suf_min = vec![vec![0.0; kmax]; n + 1];
    for i in 0..n { let mut rem: Vec<f64> = invf[i..].to_vec(); rem.sort_by(|a, b| b.partial_cmp(a).unwrap());
        for c in 1..kmax { if c <= rem.len() { pre_max[i][c] = rem[..c].iter().sum(); suf_min[i][c] = rem[rem.len() - c..].iter().sum(); } else { pre_max[i][c] = f64::INFINITY; suf_min[i][c] = f64::INFINITY; } } }
    let t = dd_ratio(d as f64, dp as f64);
    let (k, lo, hi, phase2) = if phase == 1 { (kk - 1, t.hi - 1.0 / allowed[kk - 1] as f64, t.hi, false) } else { (kk - 2, t.hi - 2.0 / a_next as f64, t.hi, true) };
    let fname = format!("k64_phase{}_results.txt", phase); let ckname = format!("k64_phase{}_done.txt", phase);
    let done: std::collections::HashSet<usize> = std::fs::read_to_string(&ckname).unwrap_or_default().lines().filter_map(|l| l.parse().ok()).collect();
    let mut d2 = Big::from_u64(d); d2 = d2.mul_small(d);
    let ctx = Ctx { d, dp, d2, allowed, inv, invf, pre_max, suf_min, t, leaves: AtomicU64::new(0), in_window: AtomicU64::new(0), exact: AtomicU64::new(0), found: AtomicU64::new(0), min_delta: AtomicU64::new(f64::INFINITY.to_bits()), max_hi2: AtomicU64::new(0),
        results: Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&fname).unwrap()) };
    eprintln!("phase {}: N={} A_N={} k={} window=[{:.9},{:.9}) threads={} resumed_items={}", phase, n, ctx.allowed[n - 1], k, lo, hi, nthreads, done.len());
    let items = 1usize << D; let done_ct = AtomicUsize::new(0); let next = AtomicUsize::new(0); let ck = Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&ckname).unwrap());
    let t0 = std::time::Instant::now();
    std::thread::scope(|sc| {
        for _ in 0..nthreads { sc.spawn(|| { let mut s = Vec::with_capacity(64); loop {
            let it = next.fetch_add(1, Ordering::Relaxed); if it >= items { break; } if done.contains(&it) { continue; }
            s.clear(); let mut mass = 0.0; let mut sig = DD { hi: 0.0, lo: 0.0 };
            for j in 0..D { if it >> j & 1 == 1 { s.push(ctx.allowed[j]); mass += ctx.invf[j]; sig = dd_add(sig, ctx.inv[j]); } }
            if s.len() <= k { dfs(&ctx, D, k - s.len(), mass, sig, &mut s, lo, hi, n, phase2); }
            writeln!(ck.lock().unwrap(), "{}", it).unwrap(); let dc = done_ct.fetch_add(1, Ordering::Relaxed) + 1;
            if dc % 512 == 0 { let el = t0.elapsed().as_secs_f64(); eprintln!("  done {}/{}  leaves {:.3e}  exact {}  found {}  {:.0}s  ETA {:.0}s", dc, items - done.len(), ctx.leaves.load(Ordering::Relaxed) as f64, ctx.exact.load(Ordering::Relaxed), ctx.found.load(Ordering::Relaxed), el, el * (items - done.len() - dc) as f64 / dc as f64); }
        } }); }
    });
    if phase == 2 { println!("phase 2: min delta over window sets = {:e}   max l_2 upper bound = {}", f64::from_bits(ctx.min_delta.load(Ordering::Relaxed)), ctx.max_hi2.load(Ordering::Relaxed)); }
    println!("phase {} complete: leaves {}  in_window {}  exact_checks {}  integer_forced_primes_found_or_unresolved {}  ({:.0}s)", phase, ctx.leaves.load(Ordering::Relaxed), ctx.in_window.load(Ordering::Relaxed), ctx.exact.load(Ordering::Relaxed), ctx.found.load(Ordering::Relaxed), t0.elapsed().as_secs_f64());
}
