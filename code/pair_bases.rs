// pair_bases.rs -- enumerate the pair sector of level 60 (prop:sectors(ii)).
//
// A 60-element prime support U with T(U) > 2 is in the pair sector when T(U) - 2 < 1/max U.
// Writing p > q for the two largest elements and W for the remaining 58, this is equivalent to
//
//     T(W u {p}) < 2   and   T(W u {q}) < 2,
//
// so both of the two largest elements are needed to reach mass 2: such a U escapes every
// single-tail family, which is what makes the pair sector unreachable by the arity-one weapon of
// prop:immunedecide.
//
// Put delta = 2 - T(W) > 0. The conditions on the tail become
//
//     1/q < delta        (i.e. q > 1/delta)          and      1/q + 1/p > delta,
//
// with q > max W and p > q. A tail therefore exists only if max(max W, 1/delta) < 2/delta, and since
// q > max W this forces
//
//     max W * (2 - T(W)) < 2,
//
// which is the prune that makes the enumeration finite: T(W) must sit close to 2 and max W must stay
// below 2/delta <= 1587. All 27 primes <= 103 lie in W (they lie in every 60-support, and the tail
// primes exceed max W, hence exceed 103), leaving 31 free slots drawn from the primes in (103, 1587].
//
// f64 is used only for the branch bound, with a conservative slack, so no live branch is cut; every
// surviving leaf is then tested exactly in 512-bit integer arithmetic as maxW * (2*D - N) < 2*D.
//
// Build: rustc -O -o pair_bases code/pair_bases.rs
// Run:   ./pair_bases > pair_bases.txt
// Output: one line per base, "idx maxW qlo qhi p1 ... p58", where any tail (q, p) with
//   q prime in (qlo, qhi), p prime > q, 1/q + 1/p > delta   yields a pair-sector support.

const L: usize = 8;

#[derive(Clone, Copy, PartialEq, Eq)]
struct Big([u64; L]);
impl Big {
    fn zero() -> Big { Big([0; L]) }
    fn from(v: u64) -> Big { let mut r = Big::zero(); r.0[0] = v; r }
    fn cmp(&self, o: &Big) -> std::cmp::Ordering {
        for i in (0..L).rev() { if self.0[i] != o.0[i] { return self.0[i].cmp(&o.0[i]); } }
        std::cmp::Ordering::Equal
    }
    fn mul_small(&self, m: u64) -> Big {
        let mut r = Big::zero(); let mut c: u128 = 0;
        for i in 0..L { let t = self.0[i] as u128 * m as u128 + c; r.0[i] = t as u64; c = t >> 64; }
        assert!(c == 0, "overflow"); r
    }
    fn add(&self, o: &Big) -> Big {
        let mut r = Big::zero(); let mut c: u128 = 0;
        for i in 0..L { let t = self.0[i] as u128 + o.0[i] as u128 + c; r.0[i] = t as u64; c = t >> 64; }
        assert!(c == 0, "overflow"); r
    }
    fn sub(&self, o: &Big) -> Big {
        let mut r = Big::zero(); let mut b: i128 = 0;
        for i in 0..L {
            let t = self.0[i] as i128 - o.0[i] as i128 - b;
            if t < 0 { r.0[i] = (t + (1i128 << 64)) as u64; b = 1; } else { r.0[i] = t as u64; b = 0; }
        }
        assert!(b == 0, "underflow"); r
    }
    fn shl1(&self) -> Big {
        let mut r = Big::zero(); let mut c = 0u64;
        for i in 0..L { r.0[i] = (self.0[i] << 1) | c; c = self.0[i] >> 63; }
        assert!(c == 0, "overflow"); r
    }
    fn divrem_small(&self, d: u64) -> (Big, u64) {
        let mut q = Big::zero(); let mut rem: u128 = 0;
        for i in (0..L).rev() { let cur = (rem << 64) | self.0[i] as u128; q.0[i] = (cur / d as u128) as u64; rem = cur % d as u128; }
        (q, rem as u64)
    }
}

fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut d = 2; while d * d <= n { if n % d == 0 { return false; } d += 1; } true }

struct Ctx { forced: Vec<u64>, pool: Vec<u64>, inv: Vec<f64>, cum: Vec<f64>, tf: f64, primes: Vec<u64>, split_format: bool, shard_k: usize, shard_m: usize }

fn emit(ctx: &Ctx, chosen: &[usize], idx: &mut usize, out: &mut String) {
    let mut w: Vec<u64> = ctx.forced.clone();
    for &t in chosen { w.push(ctx.pool[t]); }
    let maxw = *w.iter().max().unwrap();
    // exact test: maxW * (2D - N) < 2D
    let mut d = Big::from(1);
    for &p in &w { d = d.mul_small(p); }
    let mut n = Big::zero();
    for &p in &w { let (qq, r) = d.divrem_small(p); assert!(r == 0); n = n.add(&qq); }
    let two_d = d.shl1();
    if n.cmp(&two_d) != std::cmp::Ordering::Less { return; } // T(W) >= 2 is not the pair sector
    let delta_num = two_d.sub(&n);                            // = (2 - T(W)) * D
    let lhs = delta_num.mul_small(maxw);                      // maxW * (2D - N)
    if lhs.cmp(&two_d) != std::cmp::Ordering::Less { return; } // maxW * (2 - T(W)) >= 2: no tail
    // q window: q > max(maxW, 1/delta), q < 2/delta.  1/delta = D/(2D-N), 2/delta = 2D/(2D-N).
    let (qlo_big, _) = d.divrem_small(1); let _ = qlo_big;
    // compute floor(D/(2D-N)) and floor(2D/(2D-N)) by binary search on multiplication
    let bound = |target: &Big| -> u64 {
        let (mut lo, mut hi) = (1u64, 4_000_000u64);
        while lo < hi { let mid = (lo + hi + 1) / 2;
            if delta_num.mul_small(mid).cmp(target) != std::cmp::Ordering::Greater { lo = mid; } else { hi = mid - 1; } }
        lo
    };
    let qlo = std::cmp::max(maxw, bound(&d));
    let qhi = bound(&two_d);
    if qhi <= qlo { return; }
    // a tail exists only if some prime sits strictly inside (qlo, qhi]
    if !ctx.primes.iter().any(|&r| r > qlo && r <= qhi) { return; }
    if ctx.split_format {
        // Emit each (W, q) as a 59-prime arity-one base in split_sieve.rs format:
        //   idx kronA kronB 0 p1 ... p59
        // Paper line 1071 keys the pair sector this way ("each an arity-one tail family"), the
        // largest element p being the tail. The Jacobi fields are set to 1 so that split_sieve
        // processes every base: for these bases T(S) < 2, so B_S is negative and the certificate of
        // prop:tailkill needs the |B_S| convention of cor:maxbound rather than the single-tail one.
        for &q in ctx.primes.iter() {
            if q <= qlo || q > qhi { continue; }
            // 1/q < delta, i.e. delta_num * q > D
            let dq = delta_num.mul_small(q);
            if dq.cmp(&d) != std::cmp::Ordering::Greater { continue; }
            // A tail p needs q < p < 1/(delta_W - 1/q) = D*q / ((2D - N)*q - D). The interval is
            // non-empty whenever q < 2/delta_W, but non-empty is not the same as containing a prime,
            // so the prime itself is required here: without one the base carries no family at all.
            let denom = dq.sub(&d);
            let plim = {
                let target = d.mul_small(q);
                let (mut lo, mut hi) = (0u64, 4_000_000u64);
                while lo < hi { let mid = (lo + hi + 1) / 2;
                    if denom.mul_small(mid).cmp(&target) != std::cmp::Ordering::Greater { lo = mid; } else { hi = mid - 1; } }
                lo
            };
            if !ctx.primes.iter().any(|&r| r > q && r <= plim) { continue; }
            let mut s = w.clone(); s.push(q); s.sort();
            *idx += 1;
            if ctx.shard_m > 1 && (*idx - 1) % ctx.shard_m != ctx.shard_k { continue; }
            out.push_str(&format!("{} 1 1 0", *idx));
            for &r in &s { out.push_str(&format!(" {}", r)); }
            out.push('\n');
        }
        return;
    }
    *idx += 1;
    out.push_str(&format!("{} {} {} {}", *idx, maxw, qlo, qhi));
    for &p in &w { out.push_str(&format!(" {}", p)); }
    out.push('\n');
}

fn dfs(i: usize, need: usize, cur: f64, chosen: &mut Vec<usize>, ctx: &Ctx, idx: &mut usize, out: &mut String) {
    if need == 0 { emit(ctx, chosen, idx, out); return; }
    let np = ctx.pool.len();
    if i + need > np { return; }
    // upper bound on the mass this branch can still reach
    let hi = ctx.cum[std::cmp::min(i + need, np)] - ctx.cum[i];
    let best_mass = ctx.tf + cur + hi;
    // the branch is dead unless maxW * (2 - T(W)) < 2 can still hold. maxW is at least pool[i-1]
    // once anything is chosen; use the smallest possible maxW for a conservative bound.
    let maxw_lo = if chosen.is_empty() { *ctx.forced.last().unwrap() } else { ctx.pool[*chosen.last().unwrap()] };
    if (maxw_lo as f64) * (2.0 - best_mass) >= 2.0 + 1e-12 { return; }
    chosen.push(i);
    dfs(i + 1, need - 1, cur + ctx.inv[i], chosen, ctx, idx, out);
    chosen.pop();
    dfs(i + 1, need, cur, chosen, ctx, idx, out);
}

fn main() {
    let forced: Vec<u64> = (2..104).filter(|&p| is_prime(p)).collect();
    let pool: Vec<u64> = (104..1588).filter(|&p| is_prime(p)).collect();
    let primes: Vec<u64> = (2..20000).filter(|&p| is_prime(p)).collect();
    assert_eq!(forced.len(), 27);
    let need = 58 - forced.len();
    let tf: f64 = forced.iter().map(|&p| 1.0 / p as f64).sum();
    let inv: Vec<f64> = pool.iter().map(|&p| 1.0 / p as f64).collect();
    let np = pool.len();
    let mut cum = vec![0.0f64; np + 1];
    for i in 0..np { cum[i + 1] = cum[i] + inv[i]; }
    eprintln!("forced {}, pool {} (103, 1587], choose {}", forced.len(), np, need);
    let split_format = std::env::args().any(|a| a == "--split");
    // --shard K/M writes only every M-th base, so the full 4 GB listing never has to be materialised.
    let (mut shard_k, mut shard_m) = (0usize, 1usize);
    let av: Vec<String> = std::env::args().collect();
    for i in 0..av.len() {
        if av[i] == "--shard" && i + 1 < av.len() {
            let parts: Vec<&str> = av[i + 1].split('/').collect();
            shard_k = parts[0].parse().unwrap(); shard_m = parts[1].parse().unwrap();
        }
    }
    let ctx = Ctx { forced, pool, inv, cum, tf, primes, split_format, shard_k, shard_m };
    let mut chosen = Vec::with_capacity(need);
    let mut out = String::new(); let mut idx = 0usize;
    dfs(0, need, 0.0, &mut chosen, &ctx, &mut idx, &mut out);
    print!("{}", out);
    eprintln!("{}: {}", if ctx.split_format { "pair-sector (W,q) arity-one bases" } else { "pair-sector bases" }, idx);
}
