// invent_lyapunov.rs -- I5 definition tournament + I6 examples battery.
//
// GATE (I1). thm:ff kills cycles over K[t] because deg f' <= deg f - 1: a LYAPUNOV function that
// provably decreases. The missing property P for the NO direction over Z is a delta with
//        delta(n') < delta(n)  for every squarefree n with n' squarefree,
// since a two-cycle would then satisfy delta(a) < delta(a). A5 (Ostrowski) proves no ABSOLUTE
// VALUE supplies such a delta, so any candidate must fail to be one.
//
// I5: four candidates, each from a different representation. I6: battery = all squarefree n with
// n' squarefree in range, which contains the motivating instances (sigma(n) > 1) as a non-vacuity
// check. A candidate DIES on the first counterexample; the cause of death is recorded.
//
// I12 negative control: delta = log n MUST fail, since it fails exactly when sigma(n) >= 1, which
// is known to happen. A candidate battery that does not kill log n is not testing anything.
fn main() {
    let lim: usize = 20_000_000;
    let mut spf = vec![0u32; lim + 1];
    let mut i = 2usize;
    while i <= lim { if spf[i] == 0 { let mut j = i; while j <= lim { if spf[j] == 0 { spf[j] = i as u32; } j += i; } } i += 1; }
    let mut sf = vec![false; lim + 1]; sf[1] = true;
    let mut der = vec![0i64; lim + 1]; let mut om = vec![0u32; lim + 1]; let mut lpf = vec![0u32; lim + 1];
    for n in 2..=lim { let p = spf[n] as usize; let q = n / p;
        if q % p == 0 || !sf[q] { continue; }
        sf[n] = true; om[n] = om[q] + 1; lpf[n] = if q > 1 { lpf[q].max(p as u32) } else { p as u32 };
        der[n] = if q > 1 { der[q] * p as i64 + q as i64 } else { 1 }; }
    // candidates: (name, delta)
    let cands: Vec<(&str, Box<dyn Fn(usize) -> f64>)> = vec![
        ("log n                      (I12 control, must FAIL)", Box::new(|n: usize| (n as f64).ln())),
        ("log n - 1.0 * omega(n)     (combinatorial)",          Box::new(|n: usize| (n as f64).ln() - 1.0 * om[n] as f64)),
        ("log n - 3.0 * omega(n)     (combinatorial, heavier)", Box::new(|n: usize| (n as f64).ln() - 3.0 * om[n] as f64)),
        ("log n + 2.0 * sigma(n)     (analytic)",       Box::new(|n: usize| (n as f64).ln() + 2.0 * (der[n] as f64 / n as f64))),
        ("log n - log(P+(n))         (multiplicative)",         Box::new(|n: usize| (n as f64).ln() - (lpf[n].max(1) as f64).ln())),
        ("sum_{p|n} log log p        (additive, non-valuation)",Box::new(|n: usize| { let mut s=0.0; let mut t=n; while t>1 { let p=spf[t] as usize; s += ((p as f64).ln()).ln().max(0.0); while t%p==0 {t/=p;} } s })),
    ];
    println!("battery: squarefree n <= {} with n' squarefree\n", lim);
    for (name, d) in &cands {
        let (mut tested, mut viol) = (0u64, 0u64);
        let (mut first_n, mut first_sig) = (0usize, 0f64);
        for n in 2..=lim {
            if !sf[n] { continue; }
            let dn = der[n]; if dn <= 1 || dn as usize > lim || !sf[dn as usize] { continue; }
            tested += 1;
            if !(d(dn as usize) < d(n)) { viol += 1; if first_n == 0 { first_n = n; first_sig = der[n] as f64 / n as f64; } }
        }
        let verdict = if viol == 0 { "SURVIVES" } else { "DEAD" };
        println!("{:<52} tested {:>9}  violations {:>9}   {}", name, tested, viol, verdict);
        if viol > 0 { println!("{:54}first counterexample n = {}, sigma(n) = {:.4}", "", first_n, first_sig); }
    }
}
