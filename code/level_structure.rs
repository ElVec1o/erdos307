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
// The file also carries the restricted-prime reading (min prime >= P), which reproduces
// prop:twoparam from the structural side, and a capped traversal of the all-odd cell showing that
// 83 per cent forcing does NOT make it enumerable: 238 free places from 643 candidates, excess
// 2.069e-5, and a cap of 4e8 nodes reaches 1.977e8 admissible supports without exhausting. The
// slack per free place decides enumerability, not the forced fraction.
//
// It also carries the orphan census behind prop:nottree: level-60 admissible supports with no
// admissible 59-subset. These are V u {q} with |V| = 59, mass(V) <= 2, q > max V and
// q < 1/(2 - mass V). From V = {p <= 271} u {r} alone, r < 4000 gives 60,831 of them.
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
// prop:levelstructure at the all-odd cell: c = 2 carried by primes >= 3.
fn main() {
    let lim: usize = 60_000_000;
    let mut s = vec![true; lim + 1];
    s[0] = false; s[1] = false;
    let mut i = 2usize;
    while i * i <= lim { if s[i] { let mut j = i * i; while j <= lim { s[j] = false; j += i; } } i += 1; }
    for &pmin in &[2usize, 3, 5] {
        let ps: Vec<usize> = (pmin..=lim).filter(|&k| s[k]).collect();
        let mut t = vec![0f64; ps.len() + 1];
        for k in 0..ps.len() { t[k + 1] = t[k] + 1.0 / ps[k] as f64; }
        let c = 2.0f64;
        let mut n = 0usize;
        while n < ps.len() && t[n] < c { n += 1; }
        if n >= ps.len() { println!("min prime {}: out of range", pmin); continue; }
        let slack = t[n] - c;
        let thr = t[n + 1] - c;
        let forced_upto = if thr > 0.0 { (1.0 / thr) as usize } else { 0 };
        let nforced = ps.iter().take_while(|&&p| p <= forced_upto).count();
        let band = if t[n - 1] < c { 1.0 / (c - t[n - 1]) } else { f64::INFINITY };
        // product of the minimal support, log10
        let lg: f64 = ps[..n].iter().map(|&p| (p as f64).log10()).sum();
        println!("min prime >= {:2} : n = {:6}, last = {:8}, slack = {:.4e}, forced <= {:8} ({:6}, {:.0}%), max(U) < {:.4e}, prod = 10^{:.1}",
                 pmin, n, ps[n - 1], slack, forced_upto, nforced,
                 100.0 * nforced as f64 / n as f64, band, lg);
    }
}
// Is the all-odd cell an enumerable search, the way level 59 was?
fn main() {
    let lim: usize = 200_000;
    let mut s = vec![true; lim + 1];
    s[0] = false; s[1] = false;
    let mut i = 2usize;
    while i * i <= lim { if s[i] { let mut j = i * i; while j <= lim { s[j] = false; j += i; } } i += 1; }
    let ps: Vec<usize> = (3..=lim).filter(|&k| s[k]).collect();
    let mut t = vec![0f64; ps.len() + 1];
    for k in 0..ps.len() { t[k + 1] = t[k] + 1.0 / ps[k] as f64; }
    let c = 2.0f64;
    let mut n = 0usize; while t[n] < c { n += 1; }
    let thr = t[n + 1] - c;
    let forced_upto = (1.0 / thr) as usize;
    let nf = ps.iter().take_while(|&&p| p <= forced_upto).count();
    let band = 1.0 / (c - t[n - 1]);
    let ncand = ps.iter().take_while(|&&p| (p as f64) < band).count() - nf;
    let free = n - nf;
    let forced_mass: f64 = ps[..nf].iter().map(|&p| 1.0 / p as f64).sum();
    let target = c - forced_mass;
    println!("all-odd cell: n = {}, forced = {} (<= {}), free = {}, candidates = {}",
             n, nf, forced_upto, free, ncand);
    println!("forced mass = {:.12}, free {} must carry > {:.12}", forced_mass, free, target);
    let cand: Vec<f64> = ps[nf..nf + ncand].iter().map(|&p| 1.0 / p as f64).collect();
    // baseline: the `free` smallest candidates
    let base: f64 = cand[..free].iter().sum();
    println!("baseline (free smallest) = {:.12}, excess over target = {:.4e}", base, base - target);
    // capped DFS
    let mut best = vec![vec![f64::NEG_INFINITY; free + 1]; ncand + 2];
    for i in (0..=ncand).rev() {
        best[i][0] = 0.0;
        for j in 1..=free { if i + j <= ncand { best[i][j] = cand[i..i + j].iter().sum(); } }
    }
    let cap: u64 = 400_000_000;
    let mut count: u64 = 0; let mut nodes: u64 = 0; let mut capped = false;
    struct F { i: usize, c: usize, m: f64 }
    let mut st = vec![F { i: 0, c: 0, m: 0.0 }];
    while let Some(f) = st.pop() {
        nodes += 1;
        if nodes > cap { capped = true; break; }
        if f.c == free { if f.m > target { count += 1; } continue; }
        if f.i >= ncand { continue; }
        let need = free - f.c;
        if f.i + need > ncand { continue; }
        if f.m + best[f.i][need] <= target { continue; }
        st.push(F { i: f.i + 1, c: f.c, m: f.m });
        st.push(F { i: f.i + 1, c: f.c + 1, m: f.m + cand[f.i] });
    }
    if capped {
        println!("NODE CAP {} hit; count so far {} -- the all-odd cell is NOT enumerable this way", cap, count);
    } else {
        println!("admissible all-odd supports = {} (nodes {})", count, nodes);
    }
}
\p 30
{
my(T58, r, mV, lo, hi, cnt, tot, shown);
T58 = 0.0; forprime(p = 2, 271, T58 += 1.0/p);
print("Level-60 admissible supports with NO admissible 59-subset.");
print("Such a U is V u {q} with |V| = 59, mass(V) <= 2, q > max(V), and 1/q > 2 - mass(V),");
print("so q < 1/(2 - mass(V)). Taking V = {first 58 primes} u {r} with r > 794 (so mass(V) < 2):");
print("");
print("     r    |  mass(V)     | q ranges over (r, 1/(2-mass V)) | count of q");
tot = 0; shown = 0;
forprime(r = 797, 4000,
  mV = T58 + 1.0/r;
  if(mV >= 2, next);
  hi = 1.0/(2 - mV);
  cnt = 0;
  forprime(q = r+1, min(hi, 10^7), cnt++);
  tot += cnt;
  if(shown < 8, shown++;
    printf("  %6d  | %.10f | (%6d, %10.0f)          | %7d\n", r, mV, r, hi, cnt));
);
print("  ...");
printf("total orphan level-60 supports of this shape (r < 4000): %d\n", tot);
print("");
print("So they are abundant, not exceptional. Completing every one-new-prime family at level 60");
print("would still leave these untouched, since none of them contains an admissible 59-set.");
}
quit;
