// plus_automatic.rs — the family on which the PLUS square is automatic, and what the minus becomes.
//
// Slot calculus (prop:slot): for a squarefree base N0 with E0 = N0' + 2N0, the slot r makes
// N = N0 r a plus-hit exactly when r = (s^2 - N0)/E0. So on the family
//
//     F(N0) = { N0 r : r = (s^2 - N0)/E0 },
//
// the plus-square N' + 2N = s^2 holds IDENTICALLY -- one of the two squares is free.
//
// What does the minus-square cost there? With k0 = 2N0 - N0' (> 0 iff sigma(N0) < 2),
//     N' - 2N = N0 - k0 r = (4 N0^2 - k0 s^2)/E0,
// so the minus-square N'-2N = d^2 becomes the BINARY QUADRATIC FORM equation
//
//     k0 s^2  +  E0 d^2  =  4 N0^2 .                                    (prop:form)
//
// This is the decoupling asked for. Its consequence is structural: for sigma(N0) < 2 the form is
// POSITIVE DEFINITE, so 4N0^2 has only FINITELY many representations -- a finite check per base --
// where the coupled tail family had an exponential Pell orbit. The residual primality is then
// "is r = (s^2-N0)/E0 prime" over finitely many candidates per base, not over a Lehmer sequence.
//
// This program enumerates every representation for every squarefree base in range and reports the
// slots r, flagging any that is a live prime slot (r prime, r ∤ N0).
//
// Build: rustc -O -o plus_automatic plus_automatic.rs
// Run:   ./plus_automatic [LIMIT]        default 200000

fn is_prime(n: i128) -> bool {
    if n < 2 { return false; }
    if n % 2 == 0 { return n == 2; }
    let mut i = 3i128;
    while i * i <= n { if n % i == 0 { return false; } i += 2; }
    true
}

fn main() {
    let lim: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(200_000);

    let mut spf = vec![0u32; lim + 1];
    for i in 2..=lim { if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } }
    let mut der = vec![0i128; lim + 1];
    let mut sf = vec![false; lim + 1]; sf[1] = true;
    for n in 2..=lim {
        let p = spf[n] as usize; let m = n / p;
        if m % p == 0 || !sf[m] { continue; }
        sf[n] = true;
        der[n] = if m > 1 { der[m] * p as i128 + m as i128 } else { 1 };
    }

    let (mut bases, mut reps_total, mut live) = (0u64, 0u64, 0u64);
    let mut form_reps = 0u64; let mut smax_seen = 0i128; let mut max_per_base = 0u64;
    let mut ghost = 0u64;
    println!("representations of 4 N0^2 by  k0 s^2 + E0 d^2  (plus-square automatic on the slot family)\n");
    for n0 in 6..=lim {
        if !sf[n0] { continue; }
        let n0i = n0 as i128;
        let d0 = der[n0];
        let k0 = 2 * n0i - d0;                 // > 0 iff sigma < 2
        let e0 = d0 + 2 * n0i;
        if k0 <= 0 { continue; }               // form not positive definite: sigma >= 2
        bases += 1;
        let target = 4 * n0i * n0i;
        let before = form_reps;
        // positive definite: d^2 <= target/E0, s^2 <= target/k0
        let dmax = ((target / e0) as f64).sqrt() as i128 + 1;
        for d in 0..=dmax {
            let rest = target - e0 * d * d;
            if rest < 0 { break; }
            if rest % k0 != 0 { continue; }
            let s2 = rest / k0;
            let s = (s2 as f64).sqrt() as i128;
            for ss in [s - 1, s, s + 1] {
                if ss < 0 || ss * ss != s2 { continue; }
                // slot r = (s^2 - N0)/E0
                form_reps += 1;
                if smax_seen < ss { smax_seen = ss; }
                if (ss * ss - n0i) % e0 != 0 { continue; }
                let r = (ss * ss - n0i) / e0;
                if r <= 0 { continue; }
                reps_total += 1;
                let divides = n0i % r == 0;
                if r == 1 { ghost += 1; }
                else if is_prime(r) && !divides {
                    live += 1;
                    println!("  LIVE PRIME SLOT: N0 = {}  (s,d) = ({},{})  r = {}  -> N = {}",
                             n0, ss, d, r, n0i * r);
                }
            }
        }
        if form_reps - before > max_per_base { max_per_base = form_reps - before; }
    }
    println!("\nbases with sigma < 2 scanned: {}", bases);
    println!("FORM representations (k0 s^2 + E0 d^2 = 4N0^2): {}   max per base: {}", form_reps, max_per_base);
    println!("largest s encountered: {}", smax_seen);
    println!("representations found        : {}   (ghost slots r = 1: {})", reps_total, ghost);
    println!("LIVE prime slots             : {}", live);
    println!("\n=> plus automatic turns the minus-square into a FINITE representation problem per base");
    println!("   (positive definite form), replacing the coupled family's exponential Pell orbit.");
}
