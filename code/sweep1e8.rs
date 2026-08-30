// sweep1e8.rs -- extend the near-miss frontier one decade, as a test of prop:frontier.
//
// PRE-REGISTERED (Rule I15): prop:frontier gives R(10^8) <= 0.67270. The empirical frontier
// 0.333, 0.345, 0.502, 0.502, 0.536, 0.554 at 10^2..10^7 suggests a value in [0.55, 0.62].
// A returned R above 0.67270 falsifies prop:frontier.
//
// Rule 8: Rust, bounded memory (spf sieve to 4e8, 1.5 GB as u32), progress with ETA, checkpoint.
use std::io::Write;
fn main() {
    let a_max: usize = 100_000_000;
    let lim: usize = 400_000_000;
    eprintln!("sieving spf to {} ({:.1} GB) ...", lim, (lim as f64) * 4.0 / (1u64 << 30) as f64);
    let mut spf = vec![0u32; lim + 1];
    let mut i = 2usize;
    while i <= lim {
        if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } }
        i += 1;
    }
    eprintln!("sieve done");
    let dec = |mut n: usize| -> Option<(u128, f64)> {
        if n == 1 { return Some((0, 0.0)); }
        let orig = n as u128; let mut d: u128 = 0; let mut s = 0f64;
        while n > 1 {
            let p = spf[n] as usize; n /= p;
            if n % p == 0 { return None; }
            d += orig / p as u128; s += 1.0 / p as f64;
        }
        Some((d, s))
    };
    let t0 = std::time::Instant::now();
    let (mut best, mut arg) = (0f64, 0usize);
    let mut decade = 2usize;
    let mut marks: Vec<(usize, f64, usize)> = Vec::new();
    for a in 2..=a_max {
        if a % 5_000_000 == 0 {
            let el = t0.elapsed().as_secs_f64();
            let frac = a as f64 / a_max as f64;
            eprintln!("  a={:>11}  {:>5.1}%  elapsed {:>6.0}s  ETA {:>6.0}s  best={:.6} at {}",
                      a, 100.0 * frac, el, el / frac - el, best, arg);
            let _ = std::fs::write("/tmp/sweep1e8.ckpt.tmp",
                format!("a={} best={} arg={}\n", a, best, arg))
                .and_then(|_| std::fs::rename("/tmp/sweep1e8.ckpt.tmp", "/tmp/sweep1e8.ckpt"));
        }
        while decade <= 8 && a == 10usize.pow(decade as u32) {
            marks.push((decade, best, arg)); decade += 1;
        }
        let (da, sa) = match dec(a) { Some(v) => v, None => continue };
        if da == 0 || da as usize > lim { continue; }
        let (_, sda) = match dec(da as usize) { Some(v) => v, None => continue };
        let r = sa * sda;
        if r > best { best = r; arg = a; }
    }
    marks.push((8, best, arg));
    println!();
    println!("frontier by decade:");
    for (d, b, g) in &marks { println!("   10^{:<2} : max r = {:.6}   at a = {}", d, b, g); }
    println!();
    println!("R(10^8) = {:.6} at a = {}", best, arg);
    println!("prop:frontier bound  = 0.67270");
    println!("prediction held      = {}", best <= 0.67270);
    let _ = std::io::stdout().flush();
}
