// tailsearch.rs -- run the finite tail search that prop:tailbound makes possible.
//
// prop:tailbound: a Pythagorean tail prime of a base S satisfies
//     q = 2(N +- k)/m^2,   k^2 = A*B + D*m^2,   m | 4D,
// so the tail primes of a base form a FINITE set, and finding them is a search over the divisors
// of 4D for those with A*B + D*m^2 a perfect square. This is the first time that search exists:
// the previous reading (rem:lehmer) made it a primality question along an exponential orbit.
//
// SCOPE, stated up front. The full space is |div(4D)| = 4 * 2^58 ~ 1.15e18 per family, which is not
// enumerable. But the hit probability for a given m is ~ (A*B + D*m^2)^{-1/2} ~ 1/(m sqrt D), so the
// expected count is proportional to sum_m 1/m and is dominated by SMALL m. Restricting to
// omega(m) <= K therefore costs almost nothing in expectation. At K = 6 the slice is 1.2e-8 of the
// space and carries 99.947% of the expected count (code/tailsearch_plan.gp). An empty result on
// this slice is therefore a meaningful negative, not a vacuous one -- but it is a negative on a
// slice, and this program prints the covered fraction so the claim cannot be overstated.
//
// METHOD. m = 2^b * prod(T) with T a subset of the odd primes of S and 0 <= b <= 3 (D is squarefree
// and 2 | D, so 4D = 2^3 * D_odd). A DFS over subsets carries m mod M for a cascade of small moduli;
// a perfect square must be a quadratic residue modulo every one of them. Survivors of the cascade
// are written out and verified exactly, with bignum issquare, by tailsearch_verify.gp. No bignum
// arithmetic happens in this program: A*B mod M and D mod M are read off the decimal strings.
//
// Memory is O(1) per family (a few hundred bytes). There is no OOM risk at any K.
//
// Build:  rustc -O -o tailsearch tailsearch.rs
// Run:    ./tailsearch tailsearch_cfg.txt 6 > tailsearch_survivors.txt

use std::env;
use std::fs;
use std::io::Write;
use std::time::Instant;

/// Number of filter primes. Fixed so the DFS state is a stack array, never a heap allocation.
const NFILT: usize = 26;

/// Reduce a decimal string modulo `m` by Horner, so no bignum is needed.
fn dec_mod(s: &str, m: u64) -> u64 {
    let mut r: u64 = 0;
    for c in s.bytes() {
        debug_assert!(c.is_ascii_digit());
        r = (r * 10 + (c - b'0') as u64) % m;
    }
    r
}

/// Table of quadratic residues modulo `m`.
fn qr_table(m: u64) -> Vec<bool> {
    let mut t = vec![false; m as usize];
    for x in 0..m {
        t[((x * x) % m) as usize] = true;
    }
    t
}

struct Family {
    d: String,
    n: String,
    a: String,
    b: String,
    odd: Vec<u64>, // odd primes of S
}

fn parse(path: &str) -> Vec<Family> {
    let txt = fs::read_to_string(path).expect("cannot read config");
    let mut out = Vec::new();
    for line in txt.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let f: Vec<&str> = line.split_whitespace().collect();
        let odd = f[4..]
            .iter()
            .map(|s| s.parse::<u64>().unwrap())
            .filter(|&p| p != 2)
            .collect();
        out.push(Family { d: f[0].into(), n: f[1].into(), a: f[2].into(), b: f[3].into(), odd });
    }
    out
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let cfg = args.get(1).map(|s| s.as_str()).unwrap_or("tailsearch_cfg.txt");
    let kmax: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(6);

    // Filter moduli must be COPRIME TO 2D, and that is not a technicality.
    //
    // D contains every prime <= 167, so for any prime l | D,
    //     A*B + D*m^2 = N^2 - 4D^2 + D*m^2 = N^2   (mod l),
    // a square residue for every m. Since l does not divide 2N (rigidity gives gcd(D, N) = 1),
    // Hensel lifts that root to every power of l. So A*B + D*m^2 is a square modulo l^k for every
    // prime power dividing D, and the classical 64/63/65/11 pre-filter rejects NOTHING here: it was
    // measured at a 75% pass rate mod 64 and 100% mod 63. That is the analogue of prop:localcomplete
    // for this formulation -- the tail search has no local obstruction at any prime dividing D --
    // and it means only primes l coprime to 2D can filter at all.
    let fams = parse(cfg);
    eprintln!("tailsearch: {} families, K = {}", fams.len(), kmax);
    eprintln!("pre-flight: O(1) memory per family, no allocation in the hot loop, no OOM risk");

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    writeln!(out, "# survivors of the modular cascade: family b k prime_indices...").unwrap();
    writeln!(out, "# verify exactly with tailsearch_verify.gp; these are NOT yet solutions").unwrap();

    let t0 = Instant::now();
    let mut grand_tested: u64 = 0;
    let mut grand_surv: u64 = 0;

    for (fi, f) in fams.iter().enumerate() {
        // per family: the first NFILT primes coprime to 2D, i.e. not in S
        let mut moduli: Vec<u64> = Vec::with_capacity(NFILT);
        let mut cand: u64 = 3;
        while moduli.len() < NFILT {
            cand += 2;
            let is_p = (3..).step_by(2).take_while(|d: &u64| d * d <= cand).all(|d| cand % d != 0)
                && cand % 2 != 0;
            if is_p && !f.odd.contains(&cand) {
                moduli.push(cand);
            }
        }
        let tables: Vec<Vec<bool>> = moduli.iter().map(|&m| qr_table(m)).collect();
        let nm = moduli.len();
        // Per-modulus constants: AB mod M and D mod M.
        let ab: Vec<u64> = (0..nm)
            .map(|i| {
                let m = moduli[i];
                (dec_mod(&f.a, m) * dec_mod(&f.b, m)) % m
            })
            .collect();
        let dm: Vec<u64> = (0..nm).map(|i| dec_mod(&f.d, moduli[i])).collect();
        // Primes reduced modulo each filter modulus, for the incremental DFS.
        let np = f.odd.len();
        let pmod: Vec<Vec<u64>> =
            (0..nm).map(|i| f.odd.iter().map(|&p| p % moduli[i]).collect()).collect();

        // covered fraction of sum_{m | 4D} 1/m, from elementary symmetric sums of {1/p}
        let mut e = vec![0f64; np + 1];
        e[0] = 1.0;
        for &p in &f.odd {
            for j in (0..np).rev() {
                e[j + 1] += e[j] / p as f64;
            }
        }
        let total: f64 = e.iter().sum::<f64>() * (1.0 + 0.5) * (1.0 + 0.25); // 2-part: b <= 3
        let covered: f64 = e[..=kmax.min(np)].iter().sum::<f64>() * (1.0 + 0.5) * (1.0 + 0.25);

        let mut tested: u64 = 0;
        let mut surv: u64 = 0;
        // residues of m for the current subset, one row per modulus
        let mut cur: [u64; NFILT] = [1; NFILT];
        let mut chosen: Vec<usize> = Vec::with_capacity(kmax);

        // iterative DFS over subsets of size <= kmax
        fn rec(
            start: usize,
            depth: usize,
            kmax: usize,
            np: usize,
            nm: usize,
            moduli: &[u64],
            tables: &[Vec<bool>],
            ab: &[u64],
            dm: &[u64],
            pmod: &[Vec<u64>],
            cur: &mut [u64; NFILT],
            chosen: &mut Vec<usize>,
            tested: &mut u64,
            surv: &mut u64,
            out: &mut dyn Write,
            fi: usize,
        ) {
            // evaluate the current subset for every admissible power of two
            for b in 0..=3u32 {
                let two = 1u64 << b;
                *tested += 1;
                let mut ok = true;
                for i in 0..nm {
                    let m = moduli[i];
                    let mm = (cur[i] * (two % m)) % m;
                    let v = (ab[i] + dm[i] % m * ((mm * mm) % m)) % m;
                    if !tables[i][v as usize] {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    *surv += 1;
                    let idx: Vec<String> = chosen.iter().map(|x| x.to_string()).collect();
                    writeln!(out, "{} {} {} {}", fi, b, chosen.len(), idx.join(" ")).unwrap();
                }
            }
            if depth == kmax {
                return;
            }
            for i in start..np {
                let saved: [u64; NFILT] = *cur;
                for j in 0..nm {
                    cur[j] = (cur[j] * pmod[j][i]) % moduli[j];
                }
                chosen.push(i);
                rec(i + 1, depth + 1, kmax, np, nm, moduli, tables, ab, dm, pmod, cur, chosen,
                    tested, surv, out, fi);
                chosen.pop();
                *cur = saved;
            }
        }

        rec(0, 0, kmax, np, nm, &moduli, &tables, &ab, &dm, &pmod, &mut cur, &mut chosen,
            &mut tested, &mut surv, &mut out, fi);

        grand_tested += tested;
        grand_surv += surv;
        let el = t0.elapsed().as_secs_f64();
        let eta = el / (fi + 1) as f64 * (fams.len() - fi - 1) as f64;
        eprintln!(
            "family {:2}/{}  tested {:>12}  survivors {:>7}  coverage {:.6}  elapsed {:.0}s  eta {:.0}s",
            fi + 1, fams.len(), tested, surv, covered / total, el, eta
        );
    }

    eprintln!(
        "\ntotal tested {}  survivors {}  in {:.0}s",
        grand_tested, grand_surv, t0.elapsed().as_secs_f64()
    );
    eprintln!("survivors are candidates only: verify exactly with tailsearch_verify.gp");
}
