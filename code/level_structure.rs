// level_structure.rs -- the level-minimal structure as a function of c (prop:levelstructure).
//
// prop:window and prop:band were derived at c = 2, but neither argument uses that value. At the
// minimal level n(c) = min{ n : T_n >= c } for any configuration forcing sum_{p in U} 1/p >= c:
//
//   forced core   every prime with 1/p >= T_{n(c)+1} - c lies in U
//   band ceiling  max(U) < 1/(c - T_{n(c)-1}), finite because T_{n(c)-1} < c at the minimal level
//   slack         T_{n(c)} - c, the total mass a support may waste
//
// The slack collapses as c grows and the forced fraction rises with it. At c = 2 (a two-cycle) the
// core is 39 of 59 primes, 66 per cent, and the ceiling is 793.68, reproducing prop:window and
// prop:band. At c = 3 (a three-cycle) the core is 314,407 of 361,139, 87 per cent: every prime up
// to 4,476,608 is forced, and max(U) < 6.19e6. A three-cycle has almost no freedom in its support.
//
// Run:  rustc -O -o level_structure level_structure.rs && ./level_structure
//
// The level-minimal structure as a function of c: forced core, band ceiling, slack.
fn main() {
    let lim: usize = 60_000_000;
    let mut s = vec![true; lim + 1];
    s[0] = false; s[1] = false;
    let mut i = 2usize;
    while i * i <= lim { if s[i] { let mut j = i * i; while j <= lim { s[j] = false; j += i; } } i += 1; }
    let ps: Vec<usize> = (2..=lim).filter(|&k| s[k]).collect();
    // prefix sums T_n
    let mut t = vec![0f64; ps.len() + 1];
    for k in 0..ps.len() { t[k + 1] = t[k] + 1.0 / ps[k] as f64; }

    println!("  c   | n(c)     | p_{{n(c)}}   |  T_n - c    | forced: all p <= | band: max(U) <");
    for &c in &[2.0f64, 2.25, 7.0/3.0, 2.5, 3.0] {
        // n(c) = least n with T_n >= c
        let mut n = 0usize;
        while n < ps.len() && t[n] < c { n += 1; }
        if n >= ps.len() { println!("  {:.4} | out of range", c); continue; }
        let slack = t[n] - c;
        // forced: p with 1/p >= T_{n+1} - c
        let thr = t[n + 1] - c;
        let forced_upto = if thr > 0.0 { (1.0 / thr) as usize } else { 0 };
        let nforced = ps.iter().take_while(|&&p| p <= forced_upto).count();
        // band: max(U) < 1/(c - T_{n-1}) when T_{n-1} < c
        let band = if t[n - 1] < c { 1.0 / (c - t[n - 1]) } else { f64::INFINITY };
        println!("  {:.4} | {:8} | {:9} | {:.3e} | {:9} ({:>6}) | {:.4e}",
                 c, n, ps[n - 1], slack, forced_upto, nforced, band);
    }
}
