// pairsector_close.rs -- prop:pairclosed: the level-60 pair sector contains no two-cycle.
//
// Enumerates every 59-set R of primes with T(R) < 2 < T(R) + 1/max R (T = sum of reciprocals), deciding both
// inequalities exactly: each 1/p is carried as floor(2^120/p) in u128, so T(R) lies in a proven interval and a base is
// accepted or rejected only when that interval clears the boundary (0 ambiguous cases occur). For each R and every odd m
// with max R < m < 1/(2 - T(R)) it tests (m|p) = ((D/p)|p) at every odd p in R (D = prod R): a two-cycle on R u {m}
// has N' = a^2 + b^2 with N = ab = Dm, a nonzero square mod each odd p in R, while N' == (D/p) m (mod p).
// Legendre tables by Euler's criterion, each entry cross-checked against a Jacobi symbol by reciprocity.
// Output: 18,234,653 bases, 2,143,165,628 pairs (R, m), 0 survivors; about 4 CPU-minutes.
// Build: rustc -O -o pairsector_close pairsector_close.rs      Run: ./pairsector_close   |   ./pairsector_close control
use std::io::Write;
const K: usize = 59;
fn sieve(n: usize) -> Vec<u64> { let mut c = vec![true; n+1]; let mut v=vec![]; for i in 2..=n { if c[i] { v.push(i as u64); let mut j=i*i; while j<=n { c[j]=false; j+=i; } } } v }
fn powmod(mut b: u64, mut e: u64, m: u64) -> u64 { let mut r=1u64; b%=m; while e>0 { if e&1==1 { r=r*b%m; } b=b*b%m; e>>=1; } r }
// Jacobi by reciprocity (used only to cross-check the Euler tables)
fn jacobi(mut a: i64, mut n: i64) -> i32 { a%=n; if a<0 {a+=n;} let mut t=1; while a!=0 { while a%2==0 { a/=2; let r=n%8; if r==3||r==5 {t=-t;} } std::mem::swap(&mut a,&mut n); if a%4==3 && n%4==3 {t=-t;} a%=n; } if n==1 {t} else {0} }
struct St { pr: Vec<u64>, rec: Vec<u128>, pre: Vec<u128>, two: u128, qr: Vec<Vec<i8>>, idx: Vec<usize>,
  n_rnext: u64, n_rmax: u64, amb: u64, pairs_super: u64, pairs_sub: u64, surv: Vec<(Vec<u64>,u64)>, maxr: u64, maxM: u128, planted: Option<u64> }
fn leaf(st: &mut St, sel: &[usize], s: u128) {
  let r = st.pr[*sel.last().unwrap()]; let rnext = st.pr[sel.last().unwrap()+1];
  let thi = s + K as u128; // true T in [s, thi)
  // T<2 decision
  if s >= st.two { return; } // T>2 (T=2 impossible) -> not pair sector
  if thi > st.two { st.amb+=1; eprintln!("AMB T~2 {:?}", sel); return; }
  // brief's criterion T + 1/r > 2  and true criterion T + 1/rnext > 2
  let cnt = |q: u128, st: &mut St| -> bool { let lo = s+q; let hi = thi+q+1; if lo > st.two {true} else if hi <= st.two {false} else { st.amb+=1; eprintln!("AMB tail {:?}", sel); true } };
  let a = cnt(st.rec[*sel.last().unwrap()], st); if !a { return; } st.n_rmax += 1;
  let b = cnt(st.rec[sel.last().unwrap()+1], st); if b { st.n_rnext += 1; }
  if r > st.maxr { st.maxr = r; }
  let glo = st.two - thi; let ghi = st.two - s; // gap in (glo, ghi]
  let mhi = (1u128<<120) / glo; let msub = ((1u128<<120) - 1) / ghi; // 1/g <= 2^120/glo ; m< 1/g certainly if m <= msub? m*ghi<2^120
  if mhi > st.maxM { st.maxM = mhi; }
  let ps: Vec<u64> = sel.iter().map(|&i| st.pr[i]).filter(|&p| p!=2).collect();
  // targets: legendre(D/p mod p, p)
  let tg: Vec<i8> = ps.iter().map(|&p| { let mut x=1u64; for &i in sel { let q=st.pr[i]; if q!=p { x = x*(q%p)%p; } } st.qr[p as usize][x as usize] }).collect();
  let mut m = r + 2; let mhi = mhi as u64;
  while m <= mhi {
    st.pairs_super += 1; if (m as u128) <= msub { st.pairs_sub += 1; }
    let mut ok = true;
    for (j,&p) in ps.iter().enumerate() { let x = (m % p) as usize; if x==0 || st.qr[p as usize][x] != tg[j] { ok=false; break; } }
    if ok { st.surv.push((sel.iter().map(|&i| st.pr[i]).collect(), m)); }
    m += 2;
  }
}
fn dfs(st: &mut St, sel: &mut Vec<usize>, start: usize, s: u128) {
  let k = sel.len(); if k == K { leaf(st, sel, s); return; }
  let need = K - k; let n = st.pr.len();
  let mut i = start;
  while i + need < n {
    // best completion starting at i: primes i..i+need-1, r=pr[i+need-1]; bound T+1/r' <= s + pre + rec[r]; with rounding slack
    let best = s + (st.pre[i+need] - st.pre[i]) + st.rec[i+need-1] + (K as u128) + 2;
    if best <= st.two { break; } // monotone in i
    let s2 = s + st.rec[i];
    if s2 >= st.two + 0 && s2 > st.two { i+=1; continue; } // partial already >2: any completion T>2
    sel.push(i); dfs(st, sel, i+1, s2); sel.pop(); i += 1;
  }
}
fn main() {
  let args: Vec<String> = std::env::args().collect();
  let pr = sieve(4000);
  let rec: Vec<u128> = pr.iter().map(|&p| (1u128<<120)/(p as u128)).collect();
  let mut pre = vec![0u128]; for &x in &rec { let l=*pre.last().unwrap(); pre.push(l+x); }
  let mut qr = vec![vec![]; 4001];
  for &p in &pr { if p==2 {continue;} let mut t = vec![0i8; p as usize]; for x in 1..p { let e = powmod(x,(p-1)/2,p); t[x as usize] = if e==1 {1} else if e==p-1 {-1} else {panic!()}; let j=jacobi(x as i64,p as i64); assert_eq!(j as i8, t[x as usize]); } qr[p as usize]=t; }
  // prime bound: T(first 58)+2/r > 2 required
  let t58 = pre[58]; let mut rbound=0; for (i,&p) in pr.iter().enumerate() { if i>=58 && t58 + 2*rec[i] + 200 > (1u128<<121) { rbound=p; } }
  eprintln!("prime list max {} ; largest r allowed by bound {}", pr.last().unwrap(), rbound);
  let mut st = St{pr, rec, pre, two: 1u128<<121, qr, idx: vec![], n_rnext:0, n_rmax:0, amb:0, pairs_super:0, pairs_sub:0, surv: vec![], maxr:0, maxM:0, planted:None};
  let _ = &st.idx; let _ = st.planted;
  if args.len()>1 && args[1]=="control" { control(&mut st); return; }
  let mut sel = vec![]; dfs(&mut st, &mut sel, 0, 0);
  println!("bases(T+1/maxR>2, T<2) = {}", st.n_rmax);
  println!("bases(T+1/nextprime>2) = {}", st.n_rnext);
  println!("ambiguous = {}", st.amb);
  println!("max r = {}, max m bound = {}", st.maxr, st.maxM);
  println!("pairs tested (superset range) = {}, certainly-in-range subset = {}", st.pairs_super, st.pairs_sub);
  println!("survivors = {}", st.surv.len());
  let mut f = std::fs::File::create("survivors.txt").unwrap(); for (r,m) in &st.surv { writeln!(f,"{} {:?}", m, r).unwrap(); }
}
fn control(st: &mut St) {
  // R0 = primes<=271 plus 797
  let mut sel: Vec<usize> = (0..st.pr.len()).filter(|&i| st.pr[i]<=271).collect(); sel.push(st.pr.iter().position(|&p| p==797).unwrap());
  assert_eq!(sel.len(), 59);
  let s: u128 = sel.iter().map(|&i| st.rec[i]).sum();
  let g = (st.two - s) as f64 / 2f64.powi(120); println!("R0: T~{}, 1/(2-T)~{}", 2.0-g, 1.0/g);
  // negative control / real: run leaf
  leaf(st, &sel, s); println!("R0 real: pairs {} survivors {}", st.pairs_super, st.surv.len());
  // planted: overwrite targets using m0 by replacing qr lookups: simulate by choosing m0 and testing filter directly
  let m0: u64 = 123457; // odd, check coprime
  let ps: Vec<u64> = sel.iter().map(|&i| st.pr[i]).filter(|&p| p!=2).collect();
  assert!(ps.iter().all(|&p| m0%p!=0));
  let tg: Vec<i8> = ps.iter().map(|&p| st.qr[p as usize][(m0%p) as usize]).collect();
  let mut hits=vec![]; let mut m=799u64; while m<=190414 { if ps.iter().enumerate().all(|(j,&p)| {let x=(m%p) as usize; x!=0 && st.qr[p as usize][x]==tg[j]}) { hits.push(m);} m+=2; }
  println!("planted m0={} hits={:?}", m0, hits);
  // known answer {2,3,5}, q=1
  let t = |p: u64, d: u64| st.qr[p as usize][((d/p)%p) as usize];
  println!("{{2,3,5}} q=1: p=3 target {} m-sym {} ; p=5 target {} m-sym {}", t(3,30), st.qr[3][1], t(5,30), st.qr[5][1]);
  // toy negative control: base {3,5,7,11,13} all odd m<1e4 -- expect ~ 1/32 pass
  let base=[3u64,5,7,11,13]; let d:u64=base.iter().product(); let mut c=0; let mut m=15u64; while m<10000 { if base.iter().all(|&p| {let x=(m%p) as usize; x!=0 && st.qr[p as usize][x]==t(p,d)}) {c+=1;} m+=2;} println!("toy base passes {} (expected ~{:.0}: 1/32 of the odd m coprime to 15015)", c, 4993.0 * (2.0*4.0*6.0*10.0*12.0)/(3.0*5.0*7.0*11.0*13.0) / 32.0);
}
