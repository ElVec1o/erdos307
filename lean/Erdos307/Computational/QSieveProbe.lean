import Mathlib.Tactic

/-! Timing probe (INSTRUMENT, proves nothing): the q-sieve inner loop for one base in compiled Lean, with the
mod-8 class. Usage: `qprobe <bases.txt> <line index> [qmax divisor]`. -/

def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1 % m
  let mut x := b % m
  let mut k := e
  while k > 0 do
    if k % 2 == 1 then r := r * x % m
    x := x * x % m
    k := k / 2
  return r

/-- 1 if (x | p) = target sign t (t = 1 or p-1 as residue), else 0 -/
def leg (x p : Nat) : Nat := powMod x ((p - 1) / 2) p

def main (args : List String) : IO Unit := do
  let txt ← IO.FS.readFile args[0]!
  let idx := args[1]!.toNat!
  let div := (args[2]?.bind String.toNat?).getD 1
  let lines := (txt.splitOn "\n").filter (· ≠ "")
  let toks := (lines[idx]!.splitOn " ").filter (· ≠ "") |>.map String.toNat!
  let S := toks.drop (toks.length - 59)
  let D := S.foldl (· * ·) 1
  let N := (S.map fun p => D / p).foldl (· + ·) 0
  let A := N + 2 * D
  let B := N - 2 * D
  let qmax := N * 2 ^ 40 / D / div
  -- q ≡ A (1 - D) mod 8
  let q0 := (A % 8) * ((8 + 1 - D % 8) % 8) % 8
  let odd := S.filter (· ≠ 2)
  let tabs : Array ByteArray := odd.toArray.map fun p =>
    let e := (D / p) % p
    let t := leg e p
    ByteArray.mk <| (Array.range p).map fun x => if x != 0 && leg x p == t then (1 : UInt8) else 0
  let ps := odd.toArray
  let k := 7
  let W := 8 * (ps.extract 0 k).foldl (· * ·) 1
  -- wheel residues
  let mut res : Array Nat := #[]
  let mut r := q0
  while r < W do
    let mut ok := true
    for i in [0:k] do
      if tabs[i]!.get! (r % ps[i]!) == 0 then ok := false
    if ok then res := res.push r
    r := r + 8
  IO.println s!"A bits {A.log2} qmax {qmax} wheel W={W} residues={res.size} q0={q0}"
  let t0 ← IO.monoMsNow
  let mut cand : Nat := 0
  let mut surv : Nat := 0
  for r0 in res do
    let mut q := r0
    while q ≤ qmax do
      cand := cand + 1
      let mut ok := true
      let mut i := k
      while ok && i < ps.size do
        if tabs[i]!.get! (q % ps[i]!) == 0 then ok := false
        i := i + 1
      if ok then surv := surv + 1
      q := q + W
  let t1 ← IO.monoMsNow
  IO.println s!"candidates {cand} survivors {surv} ms {t1 - t0} ns/cand {(t1 - t0) * 1000000 / (max cand 1)}"
