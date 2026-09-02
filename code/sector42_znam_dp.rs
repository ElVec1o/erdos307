// sector42_znam_dp.rs -- Bado's d=42 dynamic program with the Znam conditions at 5, 11, 13 adjoined.
// Build: rustc -O -o sector42_znam_dp sector42_znam_dp.rs   Run: ./sector42_znam_dp 70 75 5,11,13
// Sector d = 42 of the two-cycle: e = 42 + 41 q, e' = 42 q, supp(e) avoids {2,3,7,41}.
// Bado's conditions on T = supp(e):  prod T = 1 (mod 41), sum r^{-1} = 0 (mod 3), (mod 7), |T| even.
// NEW: Znam conditions.  For each r in T:  prod_{s in T, s != r} s = -42^2/41  (mod r).
// We impose them at r in ZR (assumed in T; the alternative is excluded by mass, checked separately).
// DP state: (k, u mod 41, v mod 3, w mod 7, P_r mod r for r in ZR); value = max mass.
use std::env;
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i * i <= n { if n % i == 0 { return false; } i += 1; } true }
fn inv(a: u64, m: u64) -> u64 { let mut r = 1u64; let mut b = a % m; let mut e = m - 2; while e > 0 { if e & 1 == 1 { r = r * b % m; } b = b * b % m; e >>= 1; } r }
fn main() {
    let args: Vec<String> = env::args().collect();
    let kmax: usize = args[1].parse().unwrap();
    let nprimes: usize = args[2].parse().unwrap();
    let zr: Vec<u64> = args[3].split(',').filter(|s| !s.is_empty()).map(|s| s.parse().unwrap()).collect();
    let d = 42u64; let dp = 41u64;
    let mut allowed = vec![]; let mut p = 5; while allowed.len() < nprimes { if is_prime(p) && ![2,3,7,41].contains(&p) { allowed.push(p); } p += 1; }
    let others: Vec<u64> = allowed.iter().cloned().filter(|p| !zr.contains(p)).collect();
    let zmod: u64 = zr.iter().product();
    let targets: Vec<u64> = zr.iter().map(|&r| (r - (d * d % r) * inv(dp % r, r) % r) % r).collect();
    // initial state: ZR primes already in T
    let mut k0 = zr.len(); let mut u0 = 1u64; let mut v0 = 0u64; let mut w0 = 0u64; let mut m0 = 0f64;
    let mut pz0: Vec<u64> = vec![1; zr.len()];
    for (i, &r) in zr.iter().enumerate() { u0 = u0 * (r % 41) % 41; v0 = (v0 + inv(r % 3, 3)) % 3; w0 = (w0 + inv(r % 7, 7)) % 7; m0 += 1.0 / r as f64;
        for (j, &s) in zr.iter().enumerate() { if j != i { pz0[j] = pz0[j] * (r % s) % s; } } }
    let zidx = |pz: &Vec<u64>| -> usize { let mut x = 0usize; for (j, &s) in zr.iter().enumerate() { x = x * s as usize + pz[j] as usize; } x };
    let nz = zmod as usize; let nres = 41 * 3 * 7;
    let size = (kmax + 1) * nres * nz;
    eprintln!("ZR={:?} targets={:?} states={} ({} MB)", zr, targets, size, size * 8 / 1_000_000);
    let neg = f64::NEG_INFINITY;
    let mut best = vec![neg; size];
    let idx = |k: usize, u: u64, v: u64, w: u64, z: usize| -> usize { ((k * nres) + (u as usize * 21 + v as usize * 7 + w as usize)) * nz + z };
    best[idx(k0, u0, v0, w0, zidx(&pz0))] = m0;
    // decode z -> pz vector
    let decode = |mut z: usize| -> Vec<u64> { let mut pz = vec![0u64; zr.len()]; for j in (0..zr.len()).rev() { pz[j] = (z % zr[j] as usize) as u64; z /= zr[j] as usize; } pz };
    let mut ztab: Vec<Vec<usize>> = vec![]; // ztab[prime index][z] -> new z
    for &s in &others { let mut t = vec![0usize; nz]; for z in 0..nz { let mut pz = decode(z); for (j, &r) in zr.iter().enumerate() { pz[j] = pz[j] * (s % r) % r; } t[z] = zidx(&pz); } ztab.push(t); }
    for (pi, &s) in others.iter().enumerate() {
        let su = s % 41; let sv = inv(s % 3, 3); let sw = inv(s % 7, 7); let ms = 1.0 / s as f64;
        for k in (k0..kmax).rev() { for u in 1..41u64 { for v in 0..3u64 { for w in 0..7u64 { for z in 0..nz {
            let cur = best[idx(k, u, v, w, z)]; if cur == neg { continue; }
            let ni = idx(k + 1, u * su % 41, (v + sv) % 3, (w + sw) % 7, ztab[pi][z]);
            if cur + ms > best[ni] { best[ni] = cur + ms; }
        }}}}}
        if pi % 10 == 9 { eprintln!("  prime {}/{}", pi + 1, others.len()); }
    }
    let target = 42.0 / 41.0;
    let zt = zidx(&targets);
    for k in (k0..=kmax).step_by(1) { if k % 2 == 1 { continue; }
        let mz = best[idx(k, 1, 0, 0, zt)];
        // also report max over ALL z (Bado's conditions only)
        let mut mb = neg; for z in 0..nz { let x = best[idx(k, 1, 0, 0, z)]; if x > mb { mb = x; } }
        println!("k={:3}  M_k(Bado)={:.15} {}   M_k(+Znam)={:.15} {}", k, mb, if mb < target {"< 42/41 EXCLUDED"} else {">= 42/41 open"}, mz, if mz < target {"< 42/41 EXCLUDED"} else {">= 42/41 open"});
    }
}
