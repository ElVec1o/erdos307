import Erdos307.Computational.PairSectorEmpty

/-! Instrumented run (cross-check only). `count` mirrors `pdfs` counting visited leaves; `check` is the
exact Boolean whose truth `pair_sector_empty_of_check` consumes. -/

open Erdos307

def pcount : List ℕ → ℕ → ℚ → List ℕ → ℕ
  | _, 0, cur, chosen =>
    if cur < 2 ∧ (∃ r, chosen.head? = some r ∧ 2 < cur + (r : ℚ)⁻¹) then 1 else 0
  | [], _ + 1, _, _ => 0
  | x :: xs, need + 1, cur, chosen =>
    if 2 ≤ cur ∨ cur + rsum ((x :: xs).take (need + 1)) + (x : ℚ)⁻¹ ≤ 2 then 0
    else pcount xs need (cur + (x : ℚ)⁻¹) (x :: chosen) + pcount xs (need + 1) cur chosen

/-- Profiling mirror of `pdfs`: times `leaf` on every `stride`-th leaf. -/
partial def psample (tabs : Array (Array ℤ)) (stride : ℕ) (cnt tot : IO.Ref ℕ) (bad : IO.Ref ℕ) :
    List ℕ → ℕ → ℚ → List ℕ → IO Unit
  | _, 0, cur, chosen => do
    if cur < 2 ∧ (∃ r, chosen.head? = some r ∧ 2 < cur + (r : ℚ)⁻¹) then
      let c ← cnt.get
      cnt.set (c + 1)
      if c % stride == 0 then
        let t0 ← IO.monoNanosNow
        let ok := leaf tabs chosen.reverse
        if !ok then bad.modify (· + 1)
        let t1 ← IO.monoNanosNow
        tot.modify (· + (t1 - t0))
  | [], _ + 1, _, _ => pure ()
  | x :: xs, need + 1, cur, chosen => do
    if 2 ≤ cur ∨ cur + rsum ((x :: xs).take (need + 1)) + (x : ℚ)⁻¹ ≤ 2 then pure ()
    else
      psample tabs stride cnt tot bad xs need (cur + (x : ℚ)⁻¹) (x :: chosen)
      psample tabs stride cnt tot bad xs (need + 1) cur chosen

def main (args : List String) : IO Unit := do
  let mode := args.head?.getD "check"
  let k := (args[1]? >>= String.toNat?).getD 59
  let l := primesUpTo 1667
  if mode == "sample" then
    let tabs := mkTabs 1667
    let stride := (args[2]? >>= String.toNat?).getD 9000
    let cnt ← IO.mkRef 0
    let tot ← IO.mkRef 0
    let bad ← IO.mkRef 0
    psample tabs stride cnt tot bad l k 0 []
    let c ← cnt.get
    let t ← tot.get
    let b ← bad.get
    let n := (c + stride - 1) / stride
    IO.println s!"leaves={c} sampled={n} total_ns={t} mean_ms={(t / 1000) / (max n 1) / 1000} falseleaves={b}"
  else if mode == "count" then
    IO.println s!"leaves={pcount l k 0 []}"
  else
    let tabs := mkTabs 1667
    IO.println s!"tabs built: {tabs.size}"
    IO.println s!"check={pdfs (leaf tabs) l k 0 []}"
