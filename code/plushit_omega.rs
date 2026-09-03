// plushit_omega.rs -- searches odd squarefree v with v'+2v a perfect square and reports omega(v) and
// t = #{p | v : p = 3 mod 4}.  Regression: 137 odd plus-hits below 1e6, matching the A396915 b-file.
// Out of sample to 2e7: 598 hits, omega even in every one, t = 0 or 1 mod 4 in every one.

// FROZEN STATEMENT (I5): every ODD squarefree composite v with v' + 2v a perfect square has omega(v) EVEN.
// Ground so far: 137 odd plus-hits below 1e6, all omega even.  Null: omega parity is ~50/50, so the
// statement has real power -- a single odd-omega hit refutes it.
// Out-of-sample range: 1e6 .. LIMIT, disjoint from the b-file.
fn main() {
    let lim: u64 = std::env::args().nth(1).unwrap().parse().unwrap();
    let lo: u64 = std::env::args().nth(2).unwrap().parse().unwrap();
    // smallest prime factor sieve
    let mut spf = vec![0u32; (lim + 1) as usize];
    let mut i = 2usize;
    while i <= lim as usize { if spf[i] == 0 { let mut j = i; while j <= lim as usize { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } i += 1; }
    let mut hits = 0u64; let mut oddhits = 0u64; let mut bad = 0u64;
    for v in lo..=lim {
        if v % 2 == 0 { continue; }            // odd only
        // factor via spf, require squarefree and composite
        let mut m = v; let mut omega = 0u32; let mut deriv: u128 = 0; let mut sq = false;
        let mut ps: Vec<u64> = vec![];
        while m > 1 {
            let p = spf[m as usize] as u64; let mut e = 0;
            while m % p == 0 { m /= p; e += 1; }
            if e > 1 { sq = true; break; }
            omega += 1; ps.push(p);
        }
        if sq || omega < 2 { continue; }
        for &p in &ps { deriv += (v / p) as u128; }
        let s = deriv + 2 * v as u128;
        let r = (s as f64).sqrt() as u128;
        let mut rr = r; while rr * rr > s { rr -= 1; } while (rr + 1) * (rr + 1) <= s { rr += 1; }
        if rr * rr == s {
            hits += 1; oddhits += 1;
            let t = ps.iter().filter(|&&p| p % 4 == 3).count();
            if omega % 2 == 1 { bad += 1; println!("OMEGA-ODD v={} omega={} t={}", v, omega, t); }
            if t % 4 != 0 && t % 4 != 1 { println!("T-VIOLATION v={} omega={} t={}", v, omega, t); }
            println!("HIT v={} omega={} t={} u={}", v, omega, t, omega as usize - t);
        }
    }
    println!("range {}..{}: odd plus-hits {}, of which omega ODD: {}", lo, lim, oddhits, bad);
}
