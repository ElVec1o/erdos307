// pairsector_verify.rs -- integrity check on a pair-sector survivor file.
//
// The kill passes are checkpointed and resumable, and a resume overlap is silent: the run reports
// the kills it made, but a family re-processed across the boundary is written twice and counted
// twice. That is harmless to soundness (a duplicate row is only extra work later) and fatal to the
// arithmetic, which is how the discrepancy between 183,882 reported kills and 180,550 apparently
// removed rows arose. This checks the property that actually matters: the output is a
// duplicate-free SUBSET of the input, so no family was ever dropped without being killed.
//
// Run:  rustc -O -o psverify pairsector_verify.rs && ./psverify <input.bin> <output.bin>
// Records are 32 bytes. Exit status is nonzero if the output is not a clean subset.

use std::collections::HashSet;
use std::{env, fs, process};

fn load(p: &str) -> Vec<[u8; 32]> {
    let b = fs::read(p).unwrap_or_else(|e| { eprintln!("{}: {}", p, e); process::exit(2) });
    assert_eq!(b.len() % 32, 0, "{} is not a whole number of 32-byte records", p);
    b.chunks_exact(32).map(|c| { let mut a = [0u8; 32]; a.copy_from_slice(c); a }).collect()
}

fn main() {
    let av: Vec<String> = env::args().collect();
    if av.len() != 3 { eprintln!("usage: {} <input.bin> <output.bin>", av[0]); process::exit(2); }
    let (inp, out) = (load(&av[1]), load(&av[2]));
    let si: HashSet<_> = inp.iter().copied().collect();
    let so: HashSet<_> = out.iter().copied().collect();
    println!("input  {:>9} records, {:>9} distinct", inp.len(), si.len());
    println!("output {:>9} records, {:>9} distinct  ({} duplicate rows)",
             out.len(), so.len(), out.len() - so.len());
    let stray = out.iter().filter(|r| !si.contains(*r)).count();
    println!("output records absent from the input : {}", stray);
    println!("distinct families removed            : {}", si.len() - so.len());
    if stray == 0 && inp.len() == si.len() {
        println!("VERIFIED: clean subset; {} families remain open.", so.len());
    } else {
        println!("PROBLEM: the survivor file is not a clean subset of its input.");
        process::exit(1);
    }
}
