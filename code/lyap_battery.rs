// lyap_battery.rs -- conj:lyap kill criterion at extended range, plus the ratio that would make
// the lower demand L provable.
//
// (*)  log sigma(n) < lambda (sigma(n) - sigma(n'))   for all squarefree n with n' squarefree.
// L = sup over sigma(n) > 1 of log sigma(n)/(sigma(n) - sigma(n')),
// U = inf over sigma(n) < 1 < ... of |log sigma(n)|/(sigma(n') - sigma(n)).
// conj:lyap holds iff L < U. KILL CRITERION: if L >= U at this range, the conjecture is FALSE.
//
// Also measured: rho = sup sigma(n')/sigma(n) over sigma(n) > 1. If rho <= c < 1 then
// sigma(n) - sigma(n') >= (1-c) sigma(n), so L <= 1/(e(1-c)) since log x / x <= 1/e. That would
// make the lower demand PROVABLE rather than measured.
//
// Rule 8: progress, ETA, checkpoint every 30s (atomic write), resume via argv[1].
use std::io::Write;
fn main(){
    let a: Vec<String> = std::env::args().collect();
    let resume: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
    let n_max: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(200_000_000);
    let cap: usize = 2*n_max + 10;
    eprintln!("sieving spf to {} ({:.2} GB)...", cap, 4.0*(cap as f64)/1.073741824e9);
    let mut spf = vec![0u32; cap+1];
    let mut i=2usize; while i<=cap { if spf[i]==0 { let mut j=i; while j<=cap { if spf[j]==0 {spf[j]=i as u32;} j+=i; } } i+=1; }
    eprintln!("sieve done; sweeping n from {} to {}", resume.max(2), n_max);
    let fac = |mut n: usize| -> Option<(f64,u128)> {   // (sigma, n') ; None if not squarefree
        if n==1 { return Some((0.0,0)); }
        let orig=n as u128; let (mut s,mut d)=(0.0f64,0u128);
        while n>1 { let p=spf[n] as usize; n/=p; if n%p==0 { return None; }
            s += 1.0/p as f64; d += orig/(p as u128); }
        Some((s,d))
    };
    let (mut lo, mut hi) = (f64::NEG_INFINITY, f64::INFINITY);
    let (mut rho, mut rn) = (0.0f64, 0usize);
    let (mut steps, mut lown, mut hin) = (0u64, 0usize, 0usize);
    let t0 = std::time::Instant::now(); let mut last = std::time::Instant::now();
    for n in resume.max(2)..=n_max {
        if let Some((s,d)) = fac(n) {
            if d>1 && (d as usize)<=cap {
                if let Some((s2,_)) = fac(d as usize) {
                    steps+=1;
                    let diff = s2-s;
                    if s>1.0 { let r=s2/s; if r>rho { rho=r; rn=n; } }
                    if diff.abs()>=1e-15 {
                        let b = -(s.ln())/diff;
                        if diff>0.0 { if b<hi { hi=b; hin=n; } } else if b>lo { lo=b; lown=n; }
                    }
                }
            }
        }
        if last.elapsed().as_secs_f64() > 30.0 {
            let el=t0.elapsed().as_secs_f64();
            let frac=(n-resume) as f64/((n_max-resume).max(1)) as f64;
            let eta=if frac>1e-9 {el/frac-el} else {0.0};
            eprint!("\r  n={:>11}/{}  {:.2}%  steps {}  lambda in ({:.6},{:.6})  rho {:.6}  ETA {:.0}m   ",
                    n, n_max, 100.0*frac, steps, lo, hi, rho, eta/60.0);
            let _=std::io::stderr().flush();
            let tmp="lyap_battery.progress.tmp";
            if let Ok(mut f)=std::fs::File::create(tmp) {
                let _=writeln!(f,"n {} steps {} lo {:.9} hi {:.9} rho {:.9} lown {} hin {} rhon {}",
                               n, steps, lo, hi, rho, lown, hin, rn);
                let _=std::fs::rename(tmp,"lyap_battery.progress");
            }
            last=std::time::Instant::now();
        }
    }
    println!("\n\nn <= {}: {} steps", n_max, steps);
    println!("  lambda must exceed {:.9}   (witness n = {})", lo, lown);
    println!("  lambda must be below {:.9}  (witness n = {})", hi, hin);
    println!("  admissible width {:.9}  => conj:lyap {}", hi-lo, if hi>lo {"SURVIVES at this range"} else {"is FALSE"});
    println!("  rho = sup sigma(n')/sigma(n) over sigma(n)>1 : {:.9} at n = {}", rho, rn);
    if rho < 1.0 { println!("  => L <= 1/(e(1-rho)) = {:.6}, a PROVABLE cap on the lower demand", 1.0/(std::f64::consts::E*(1.0-rho))); }
}
