// Exhaustive scan of the two-member route (prop:twoside) at small beta.
//
// A solution with |A| = 2 is a coprime family B with product beta and D(B) = u(beta-u) for an
// integer u >= 1 -- equivalently, beta^2 - 4 D(B) is a perfect square. u = 1 is the primary
// pseudoperfect case (A contains the member 1); u >= 2 is the 1-free case.
//
// For every beta below the bound this enumerates EVERY coprime factorisation -- the set partitions
// of beta's prime powers -- and tests the discriminant. It is a check on the claim that
// u ~ sum_B 1/b, so that u >= 2 forces mass >= 2 and hence beta beyond any reachable range.

fn main() {
    let limit: u64 = 40_000_000;
    let mut spf = vec![0u32; (limit + 1) as usize];
    for i in 2..=limit {
        if spf[i as usize] == 0 {
            let mut j = i;
            while j <= limit { if spf[j as usize] == 0 { spf[j as usize] = i as u32; } j += i; }
        }
    }
    let isqrt = |n: u128| -> u128 {
        if n == 0 { return 0; }
        let mut x = (n as f64).sqrt() as u128;
        while x > 0 && x * x > n { x -= 1; }
        while (x + 1) * (x + 1) <= n { x += 1; }
        x
    };

    let (mut ppn, mut free, mut scanned) = (0u64, 0u64, 0u64);
    let mut max_u_seen = 1u64;
    let mut parts: Vec<u64> = Vec::with_capacity(10);

    for beta in 2..=limit {
        // prime-power factorisation
        parts.clear();
        let mut n = beta;
        while n > 1 {
            let p = spf[n as usize] as u64;
            let mut q = 1u64;
            while n % p == 0 { n /= p; q *= p; }
            parts.push(q);
        }
        let k = parts.len();
        if k > 9 { continue; }
        scanned += 1;
        // every set partition of the prime powers, via restricted growth strings
        let mut rgs = vec![0usize; k];
        loop {
            let nblocks = rgs.iter().max().map_or(0, |&m| m + 1);
            let mut blocks = vec![1u64; nblocks];
            for i in 0..k { blocks[rgs[i]] *= parts[i]; }
            // D(B) = sum beta / b
            let mut d: u128 = 0;
            for &b in &blocks { d += (beta as u128) / (b as u128); }
            let disc = (beta as u128) * (beta as u128);
            if disc >= 4 * d {
                let r = isqrt(disc - 4 * d);
                if r * r == disc - 4 * d {
                    let u = ((beta as u128) - r) / 2;
                    if (beta as u128 - r) % 2 == 0 && u >= 1 && u < beta as u128 {
                        let v = beta as u128 - u;
                        if u * v == d && gcd(u as u64, v as u64) == 1 {
                            if u == 1 { ppn += 1; }
                            else {
                                free += 1;
                                if u as u64 > max_u_seen { max_u_seen = u as u64; }
                                println!("*** 1-FREE: beta={} blocks={:?} u={} v={}", beta, blocks, u, v);
                            }
                        }
                    }
                }
            }
            // next restricted growth string (standard successor)
            let mut advanced = false;
            let mut i = k;
            while i > 1 {
                i -= 1;
                let mmax = rgs[..i].iter().max().copied().unwrap_or(0);
                if rgs[i] <= mmax {
                    rgs[i] += 1;
                    for j in (i + 1)..k { rgs[j] = 0; }
                    advanced = true;
                    break;
                }
            }
            if !advanced { break; }
        }
        if beta % 5_000_000 == 0 { eprintln!("  ... beta = {}", beta); }
    }
    println!("\nscanned beta up to {} ({} values with <= 9 prime powers)", limit, scanned);
    println!("u = 1  (primary pseudoperfect, member 1 present) : {}", ppn);
    println!("u >= 2 (1-free)                                  : {}", free);
    println!("largest u attained                               : {}", max_u_seen);
}

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
