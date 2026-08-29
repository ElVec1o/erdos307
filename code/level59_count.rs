// level59_count.rs -- derive the level-59 admissible-support count from the two pins.
//
// prop:window forces every prime <= 167 into U (39 of them, mass T_39) and prop:band caps
// max(U) <= 787. So an admissible support at level 59 is the forced core together with a choice of
// 20 primes from the 99 candidates in (167, 787], subject only to sigma(U) > 2, i.e. the chosen
// twenty must carry mass more than 2 - T_39.
//
// This program counts those 20-subsets directly. Agreement with the 49,961 of prop:close59, which
// was obtained by a different enumeration, is the check that the two pins characterise the level
// exactly and that nothing else is doing work.
//
// Arithmetic note. Sums are f64; the decision margin is ~1e-5 while f64 carries ~1e-17 here, so the
// comparison is safe provided no subset sum lands microscopically on the boundary. The program
// counts near-boundary cases (|sum - target| < 1e-12) and reports them, so the safety is measured
// rather than assumed.

fn primes_upto(n: usize) -> Vec<usize> {
    let mut s = vec![true; n + 1];
    s[0] = false;
    if n >= 1 { s[1] = false; }
    let mut i = 2;
    while i * i <= n { if s[i] { let mut j = i * i; while j <= n { s[j] = false; j += i; } } i += 1; }
    (2..=n).filter(|&k| s[k]).collect()
}

fn main() {
    let ps = primes_upto(787);
    let t39: f64 = ps.iter().filter(|&&p| p <= 167).map(|&p| 1.0 / p as f64).sum();
    let forced = ps.iter().filter(|&&p| p <= 167).count();
    let cand: Vec<f64> = ps.iter().filter(|&&p| p > 167).map(|&p| 1.0 / p as f64).collect();
    let n = cand.len();
    let k = 59 - forced;
    let target = 2.0 - t39;

    // suffix maxima: best[i][j] = sum of the j largest reciprocals available from position i
    // (candidates are increasing in p, so decreasing in 1/p: the j largest are cand[i..i+j])
    let mut best = vec![vec![f64::NEG_INFINITY; k + 1]; n + 2];
    for i in (0..=n).rev() {
        best[i][0] = 0.0;
        for j in 1..=k {
            if i + j <= n { best[i][j] = cand[i..i + j].iter().sum(); }
        }
    }

    println!("forced primes (p <= 167)      : {}", forced);
    println!("candidates in (167, 787]      : {}", n);
    println!("free primes to choose         : {}", k);
    println!("forced mass T_39              : {:.15}", t39);
    println!("free {} must carry more than  : {:.15}", k, target);
    println!("baseline (20 smallest cands)  : {:.15}", best[0][k]);
    println!();

    let mut count: u64 = 0;
    let mut near: u64 = 0;
    let mut nodes: u64 = 0;

    // iterative DFS
    struct Frame { i: usize, c: usize, m: f64 }
    let mut st = vec![Frame { i: 0, c: 0, m: 0.0 }];
    while let Some(f) = st.pop() {
        nodes += 1;
        if f.c == k {
            if f.m > target { count += 1; }
            if (f.m - target).abs() < 1e-12 { near += 1; }
            continue;
        }
        if f.i >= n { continue; }
        let need = k - f.c;
        if f.i + need > n { continue; }
        if f.m + best[f.i][need] <= target { continue; }
        st.push(Frame { i: f.i + 1, c: f.c, m: f.m });
        st.push(Frame { i: f.i + 1, c: f.c + 1, m: f.m + cand[f.i] });
    }

    println!("search nodes visited          : {}", nodes);
    println!("near-boundary subsets (1e-12) : {}", near);
    println!();
    println!("admissible 20-subsets counted : {}", count);
    println!("prop:close59 enumeration      : 49961");
    println!("match                         : {}", count == 49961);
}
