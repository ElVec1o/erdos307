import Erdos307.Computational.PairEnum

/-! Instrumented run of the pair-sector enumeration (cross-check only, not part of any proof):
counts the leaves `pdfs` visits at K = 59 over the primes <= 1667, to compare with the Rust 18,234,653. -/

open Erdos307

def primesUpTo (n : Nat) : List Nat := (List.range (n + 1)).filter fun p => 2 ≤ p ∧ (List.range p).all fun d => d < 2 || p % d != 0

/-- Mirror of `pdfs` counting visited leaves. -/
def pcount : List ℕ → ℕ → ℚ → List ℕ → ℕ
  | _, 0, cur, chosen =>
    if cur < 2 ∧ (∃ r, chosen.head? = some r ∧ 2 < cur + (r : ℚ)⁻¹) then 1 else 0
  | [], _ + 1, _, _ => 0
  | x :: xs, need + 1, cur, chosen =>
    if 2 ≤ cur ∨ cur + rsum ((x :: xs).take (need + 1)) + (x : ℚ)⁻¹ ≤ 2 then 0
    else pcount xs need (cur + (x : ℚ)⁻¹) (x :: chosen) + pcount xs (need + 1) cur chosen

def main (args : List String) : IO Unit := do
  let k := (args.head?.bind String.toNat?).getD 59
  let bound := (args[1]? >>= String.toNat?).getD 1667
  let l := primesUpTo bound
  IO.println s!"primes={l.length} K={k}"
  IO.println s!"leaves={pcount l k 0 []}"
