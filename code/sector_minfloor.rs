// sector_minfloor.rs -- the minimum of the mass floor 1 + omega(d) + K(d) over sectors.
// Result: 60, attained at d = 2*3*7*23*41, over 109,293 sectors (primes <= 59, omega <= 10).

// LOAD-BEARING for the floor-gap route: the minimum mass floor 1 + omega(d) + K(d) over sectors.
// If it is never below 60, then "the floor value is never attained" would give |P u Q| >= 62 everywhere.
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut i = 2; while i*i <= n { if n % i == 0 { return false; } i += 1; } true }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let cap: u64 = a[1].parse().unwrap(); let wmax: usize = a[2].parse().unwrap();
    let pool: Vec<u64> = (2..=cap).filter(|&p| is_prime(p)).collect();
    let all: Vec<u64> = (2..60000u64).filter(|&p| is_prime(p)).collect();
    let mut best = usize::MAX; let mut arg: Vec<u64> = vec![]; let mut cnt: u64 = 0;
    let n = pool.len();
    // iterate over all subsets up to size wmax
    let mut idx: Vec<usize> = vec![];
    fn rec(pool: &[u64], all: &[u64], i: usize, wmax: usize, cur: &mut Vec<u64>,
           best: &mut usize, arg: &mut Vec<u64>, cnt: &mut u64) {
        if !cur.is_empty() {
            *cnt += 1;
            let d: u128 = cur.iter().fold(1u128, |a,&p| a.saturating_mul(p as u128));
            if d != u128::MAX {
                let dp: u128 = cur.iter().map(|&p| d / p as u128).sum();
                if dp > 0 {
                    let t = d as f64 / dp as f64;
                    // excluded primes: those dividing d, and (approximately) those dividing d'
                    let mut s = 0.0f64; let mut k = 0usize;
                    for &p in all {
                        if cur.contains(&p) { continue; }
                        if dp % p as u128 == 0 { continue; }
                        s += 1.0 / p as f64; k += 1;
                        if s >= t { break; }
                    }
                    if s >= t {
                        let mut kk = k;
                        if cur[0] == 2 && kk % 2 == 1 { kk += 1; }
                        let u = 1 + cur.len() + kk;
                        if u < *best { *best = u; *arg = cur.clone(); }
                    }
                }
            }
        }
        if cur.len() >= wmax || i >= pool.len() { return; }
        for j in i..pool.len() { cur.push(pool[j]); rec(pool, all, j+1, wmax, cur, best, arg, cnt); cur.pop(); }
    }
    let mut cur = vec![];
    rec(&pool, &all, 0, wmax, &mut cur, &mut best, &mut arg, &mut cnt);
    let _ = idx.pop();
    println!("sectors examined {}   MINIMUM mass floor = {}   at d = {:?}", cnt, best, arg);
}
