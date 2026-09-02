// pairsector_factor.rs -- factoring stage over the pair-sector survivors of pairsector_kill.rs.
// Build: rustc -O (uses rug/GMP).  Run: ./pairsector_factor <trial-division limit> <threads>
// To 10^5: 3,943,096 of 7,777,504 survivors killed (50.7%), 3,834,408 still open.
// Factoring stage over the pair-sector survivors of the Jacobi certificate.
// Each survivor base R is stored as a 32-byte bitmask over the pool of primes < 1588.
// Reconstruct D = prod R, N = D', A = N + 2D, B = N - 2D.  A survivor has (D|A) = (D|B) = +1, so any
// kill needs an explicit prime l | A or l | B of ODD multiplicity with (D|l) = -1.  Trial divide both
// by the primes below LIMIT and test each such l.
use rug::Integer;
use std::io::Read;
use std::sync::atomic::{AtomicU64, Ordering};
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i * i <= n { if n % i == 0 { return false; } i += 1; } true }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let limit: u64 = a[1].parse().unwrap(); let nthreads: usize = a[2].parse().unwrap();
    let pool: Vec<u64> = (2..1588u64).filter(|&p| is_prime(p)).collect();
    let small: Vec<u64> = (2..limit).filter(|&p| is_prime(p)).collect();
    let mut buf = Vec::new(); std::fs::File::open("pair_survivors.bin").unwrap().read_to_end(&mut buf).unwrap();
    let recs = buf.len() / 32;
    eprintln!("survivors {}  trial primes {} (<{})  threads {}", recs, small.len(), limit, nthreads);
    let killed = AtomicU64::new(0); let done = AtomicU64::new(0);
    let t0 = std::time::Instant::now();
    let chunk = (recs + nthreads - 1) / nthreads;
    std::thread::scope(|sc| { for t in 0..nthreads { let (buf, pool, small, killed, done) = (&buf, &pool, &small, &killed, &done);
        sc.spawn(move || {
            for r in (t * chunk)..(((t + 1) * chunk).min(recs)) {
                let w = &buf[r * 32..r * 32 + 32];
                let mut d = Integer::from(1); let mut nn = Integer::from(0);
                for s in 0..pool.len() { if w[s / 8] >> (s % 8) & 1 == 1 {
                    nn = Integer::from(&nn * pool[s]) + &d; d *= pool[s]; } }
                let av = Integer::from(&nn + Integer::from(2) * &d);
                let bv = Integer::from(&nn - Integer::from(2) * &d);
                let mut hit = false;
                'outer: for &l in small.iter() {
                    for v in [&av, &bv] {
                        if v.is_divisible_u(l as u32) {
                            let mut m = 0u32; let mut x = Integer::from(v.clone());
                            while x.is_divisible_u(l as u32) { x /= l; m += 1; }
                            if m % 2 == 1 && Integer::from(d.clone()).jacobi(&Integer::from(l)) == -1 { hit = true; break 'outer; }
                        } } }
                if hit { killed.fetch_add(1, Ordering::Relaxed); }
                let dc = done.fetch_add(1, Ordering::Relaxed) + 1;
                if dc % 200000 == 0 { let el = t0.elapsed().as_secs_f64();
                    eprintln!("  {}/{}  killed {}  {:.0}s  ETA {:.0}s", dc, recs, killed.load(Ordering::Relaxed), el, el * (recs as f64 - dc as f64) / dc as f64); }
            } }); } });
    let k = killed.load(Ordering::Relaxed);
    println!("survivors {}  killed by trial division to {}: {}  still open {}  ({:.1}% of survivors)  {:.0}s",
        recs, limit, k, recs as u64 - k, 100.0 * k as f64 / recs as f64, t0.elapsed().as_secs_f64());
}
