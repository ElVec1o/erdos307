// antiholo_hunt.rs — census of ANTI-HOLOMORPHIC derivative cycles over Z[sqrt(-2)]:  D(a) = -conj(a).
//
// Element (x,y) = x + y*sqrt(-2);  norm(x,y) = x^2 + 2y^2 (positive definite, multiplicative).
// A cycle is a squarefree a = prod of DISTINCT Z[sqrt(-2)] primes pi_i with a Leibniz derivative of
// unit prime-values u_i in {+1,-1}:   D(a) = sum_i u_i (a/pi_i)  =  -conj(a).
// (Validated: a = -3163 - 1474 sqrt(-2), primes above 3,17,19,59,251, signs (-1,-1,1,1,1), is such a
//  cycle at norm 14,349,921 with omega=5.)
//
// PURPOSE: measure whether the count grows with the norm bound (=> infinitely many, a definite-form
// prime problem) or plateaus (=> finitely many, a resolvable cousin). Run at increasing NORMMAX.
//
// Build: rustc -O -o antiholo_hunt antiholo_hunt.rs
// Run:   ./antiholo_hunt [OMEGA_MIN OMEGA_MAX PMAX_NORM LOG10_NORMMAX]
//   defaults: 3 6 3000 8   (omega 3..6; prime-norm <= 3000; product-norm <= 1e8)
//   To catch the known omega=5 cycle you need PMAX_NORM >= 251 and NORMMAX >= 1.5e7 (LOG10 >= 8).
//
// Progress/ETA to stderr every ~3s; hits appended to antiholo_cycles.out; heartbeat to
// antiholo_hunt.progress. NOTE: only split/ramified primes (prime norm) are enumerated; a cycle using
// an inert prime (norm p^2) or a prime of norm > PMAX_NORM is not seen — widen PMAX_NORM to check.

use std::env;
use std::fs::OpenOptions;
use std::io::Write;
use std::time::Instant;

type E = (i64, i64);
#[inline] fn mul(a: E, b: E) -> E { (a.0 * b.0 - 2 * a.1 * b.1, a.0 * b.1 + a.1 * b.0) }
#[inline] fn conj(a: E) -> E { (a.0, -a.1) }
#[inline] fn nrm(a: E) -> i64 { a.0 * a.0 + 2 * a.1 * a.1 }
#[inline] fn add(a: E, b: E) -> E { (a.0 + b.0, a.1 + b.1) }

fn is_prime(n: i64) -> bool {
    if n < 2 { return false; }
    if n % 2 == 0 { return n == 2; }
    let mut i = 3;
    while i * i <= n { if n % i == 0 { return false; } i += 2; }
    true
}

struct Ctx {
    prims: Vec<E>,
    omega_min: usize,
    omega_max: usize,
    normmax: i64,
    supports: u64,
    cycles: std::collections::HashSet<(Vec<i64>, i64, i64)>,
}

fn check(ctx: &mut Ctx, chosen: &[usize], a: E) {
    ctx.supports += 1;
    let c = conj(a);
    let target = (-c.0, -c.1);
    let m = chosen.len();
    // cofactors c_i = a / pi_i = product of the OTHER primes
    let mut cof: Vec<E> = Vec::with_capacity(m);
    for i in 0..m {
        let mut p: E = (1, 0);
        for j in 0..m { if j != i { p = mul(p, ctx.prims[chosen[j]]); } }
        cof.push(p);
    }
    // want  sum_i s_i cof_i = target, s_i = +-1.  Let T = sum cof_i (all +). Flipping i subtracts 2 cof_i.
    // => sum_{flipped} cof_i = (T - target)/2.  Subset-sum over m elements.
    let mut t: E = (0, 0);
    for &c in &cof { t = add(t, c); }
    let need0 = t.0 - target.0;
    let need1 = t.1 - target.1;
    if need0 % 2 != 0 || need1 % 2 != 0 { return; }
    let need = (need0 / 2, need1 / 2);
    let mut found = false;
    for mask in 0u32..(1u32 << m) {
        let mut s: E = (0, 0);
        let mut i = 0;
        while i < m { if mask & (1 << i) != 0 { s = add(s, cof[i]); } i += 1; }
        if s == need { found = true; break; }
    }
    if !found { return; }
    let mut norms: Vec<i64> = chosen.iter().map(|&i| nrm(ctx.prims[i])).collect();
    norms.sort_unstable();
    let key = (norms.clone(), a.0.abs(), a.1.abs());
    if ctx.cycles.insert(key) {
        let msg = format!("CYCLE omega={} a=({},{}) N={} prime-norms={:?}\n",
                          m, a.0, a.1, nrm(a), norms);
        if let Ok(mut f) = OpenOptions::new().create(true).append(true).open("antiholo_cycles.out") {
            let _ = f.write_all(msg.as_bytes());
        }
        eprintln!("  {}", msg.trim_end());
    }
}

fn dfs(ctx: &mut Ctx, start_idx: usize, chosen: &mut Vec<usize>, a: E) {
    if chosen.len() >= ctx.omega_min { check(ctx, chosen, a); }
    if chosen.len() == ctx.omega_max { return; }
    let np = ctx.prims.len();
    let mut i = start_idx;
    while i < np {
        let na = mul(a, ctx.prims[i]);
        if nrm(na) > ctx.normmax { break; } // norms sorted asc + multiplicative => monotone
        chosen.push(i);
        dfs(ctx, i + 1, chosen, na);
        chosen.pop();
        i += 1;
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let g = |i: usize, d: i64| args.get(i).and_then(|s| s.parse().ok()).unwrap_or(d);
    let omega_min = g(1, 3) as usize;
    let omega_max = g(2, 6) as usize;
    let pmax = g(3, 3000);
    let normmax = 10f64.powi(g(4, 8) as i32) as i64;

    // generate split/ramified prime elements (prime norm), one rep per associate class of {+-1}
    let bnd = (pmax as f64).sqrt() as i64 + 2;
    let mut prims: Vec<E> = Vec::new();
    for x in 0..=bnd {
        for y in -bnd..=bnd {
            if !(x > 0 || (x == 0 && y > 0)) { continue; }
            let n = x * x + 2 * y * y;
            if n >= 2 && n <= pmax && is_prime(n) { prims.push((x, y)); }
        }
    }
    prims.sort_by_key(|&e| nrm(e));
    let np = prims.len();
    eprintln!("Z[sqrt-2] anti-holo census: {} prime elements (prime-norm <= {}); omega {}..{}; product-norm <= {}",
              np, pmax, omega_min, omega_max, normmax);

    let mut ctx = Ctx { prims, omega_min, omega_max, normmax, supports: 0, cycles: std::collections::HashSet::new() };
    let start = Instant::now();
    let mut last = Instant::now();

    for i0 in 0..np {
        let na = ctx.prims[i0];
        if nrm(na) > ctx.normmax { break; }
        let mut chosen = vec![i0];
        dfs(&mut ctx, i0 + 1, &mut chosen, na);
        if last.elapsed().as_secs_f64() > 3.0 || i0 + 1 == np {
            let el = start.elapsed().as_secs_f64();
            let frac = (i0 as f64 + 1.0) / np as f64;
            let eta = if frac > 1e-9 { el / frac - el } else { 0.0 };
            eprint!("\r  outer {}/{}  supports {}  cycles {}  {:.0}s  ETA~{:.0}s (front-loaded, over-est)   ",
                    i0 + 1, np, ctx.supports, ctx.cycles.len(), el, eta);
            let _ = std::io::stderr().flush();
            if let Ok(mut f) = OpenOptions::new().create(true).write(true).truncate(true).open("antiholo_hunt.progress") {
                let _ = writeln!(f, "outer {}/{} supports {} cycles {} elapsed {:.0}s eta~{:.0}s", i0 + 1, np, ctx.supports, ctx.cycles.len(), el, eta);
            }
            last = Instant::now();
        }
    }
    eprintln!();
    // summary by omega
    let mut by_omega = std::collections::BTreeMap::new();
    let mut smallest: Vec<(i64, usize)> = Vec::new();
    for (norms, _, _) in &ctx.cycles {
        *by_omega.entry(norms.len()).or_insert(0u64) += 1;
        let prod: i64 = norms.iter().product();
        smallest.push((prod, norms.len()));
    }
    smallest.sort_unstable();
    println!("\n=== Z[sqrt-2] anti-holomorphic cycle census ===");
    println!("supports tested: {}", ctx.supports);
    println!("distinct cycles: {}", ctx.cycles.len());
    for (w, c) in &by_omega { println!("   omega={}: {}", w, c); }
    println!("smallest 8 by product-norm: {:?}", &smallest[..smallest.len().min(8)]);
    println!("(run at increasing LOG10_NORMMAX: growth => infinite; plateau => finite. time {:.0}s)", start.elapsed().as_secs_f64());
}
