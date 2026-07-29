// a9prime_falsify.rs — falsification attempt on CRUX-A9' (Rule 3: falsify before proving).
//
// CRUX-A9' :  #{ m <= Z squarefree : (e m - m') | (m - c) }  <<  Z^(1/2+o(1)),  UNIFORMLY in (e,c).
//
// The uniformity is the exposed part of the claim. Earlier measurements looked only at
// (e,c) = (1,+-1), (2,+-1), (2,-4) and found counts of 21, 29, 0, 0, 1 against log Z = 16.8.
// If some other c makes the count blow up, A9' is FALSE as stated and must be repaired before
// any effort goes into proving it.
//
// Method: for each squarefree m the modulus k = e m - m' is determined, and m contributes to
// exactly those c in range with c = m (mod k). So sweep m once and scatter into a c-histogram;
// cost is sum_m 2C/|k|, which is O(C log Z) since |k| grows like m.
//
// Build: rustc -O -o a9prime_falsify a9prime_falsify.rs
// Run:   ./a9prime_falsify [Z CMAX]     default 20000000 400

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let lim: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(20_000_000);
    let cmax: i64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(400);

    let mut spf = vec![0u32; lim + 1];
    for i in 2..=lim { if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } }
    let mut der = vec![0i64; lim + 1];
    let mut sf = vec![false; lim + 1]; sf[1] = true;
    for n in 2..=lim {
        let p = spf[n] as usize; let q = n / p;
        if q % p == 0 || !sf[q] { continue; }
        sf[n] = true;
        der[n] = if q > 1 { der[q] * p as i64 + q as i64 } else { 1 };
    }

    let width = (2 * cmax + 1) as usize;
    for &e in &[1i64, 2, 3] {
        let mut hist = vec![0u32; width];              // index = c + cmax
        for m in 2..=lim {
            if !sf[m] { continue; }
            let k = e * m as i64 - der[m];
            if k == 0 { continue; }
            let ak = k.abs();
            // c must satisfy c = m (mod ak), c in [-cmax, cmax]
            let m64 = m as i64;
            // smallest c >= -cmax with c = m mod ak
            let r = ((m64 % ak) + ak) % ak;
            let mut c = -cmax + (((r - (-cmax)) % ak) + ak) % ak;
            while c <= cmax {
                hist[(c + cmax) as usize] += 1;
                c += ak;
            }
        }
        // report the worst c and the profile
        let (mut best, mut bc) = (0u32, 0i64);
        let mut total: u64 = 0;
        for i in 0..width {
            total += hist[i] as u64;
            if hist[i] > best { best = hist[i]; bc = i as i64 - cmax; }
        }
        let logz = (lim as f64).ln();
        let sqz = (lim as f64).sqrt();
        println!("e = {}:  worst c = {:<5} count = {:<8} (log Z = {:.1}, ratio {:.2};  Z^(1/2) = {:.0})",
                 e, bc, best, logz, best as f64 / logz, sqz);
        // show the top five offenders
        let mut idx: Vec<usize> = (0..width).collect();
        idx.sort_by_key(|&i| std::cmp::Reverse(hist[i]));
        let top: Vec<String> = idx.iter().take(5)
            .map(|&i| format!("c={} : {}", i as i64 - cmax, hist[i])).collect();
        println!("        top: {}", top.join(",  "));
        println!("        mean over c: {:.2}", total as f64 / width as f64);
    }
    println!("\nA9' survives iff every count stays far below Z^(1/2).");
}
