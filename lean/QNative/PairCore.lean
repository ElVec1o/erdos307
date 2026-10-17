import QNative.QSieve

/-!
# The pair-sector search, as precompiled code

The executable definitions of the pair-sector check (`pdfs`, `leaf`, `loop`, `mism`, `mkTabs`, `nsum`), moved here so that
`precompileModules` runs them as native code during the `native_decide` of `Computational/PairNative.lean`. The theorems
about them (`pdfs_sound`, `leaf_sound`, …) stay in `Erdos307/Computational/PairEnum.lean` and `PairLeaf.lean`.
`rsumN` is `Erdos307.rsum` (equal by `rfl`, `Computational/PairEnum.lean`).
-/

namespace Erdos307

def rsumN (l : List Nat) : Rat := (l.map fun p : Nat => (p : Rat)⁻¹).sum

/-- The pruned DFS. `chosen` is descending (newest first); `cur = rsum chosen`. -/
def pdfs (leaf : List Nat → Bool) : List Nat → Nat → Rat → List Nat → Bool
  | _, 0, cur, chosen =>
    if cur < 2 ∧ (∃ r, chosen.head? = some r ∧ 2 < cur + (r : Rat)⁻¹) then leaf chosen.reverse else true
  | [], _ + 1, _, _ => true
  | x :: xs, need + 1, cur, chosen =>
    if 2 ≤ cur ∨ cur + rsumN ((x :: xs).take (need + 1)) + (x : Rat)⁻¹ ≤ 2 then true
    else pdfs leaf xs need (cur + (x : Rat)⁻¹) (x :: chosen) && pdfs leaf xs (need + 1) cur chosen

/-- `tabs[ℓ][x] = eulerSym ℓ x` for `ℓ ≤ B`, `x < ℓ`. -/
def mkTabs (B : Nat) : Array (Array Int) :=
  (Array.range (B + 1)).map fun ℓ => (Array.range ℓ).map fun x => eulerN ℓ x

/-- `csum` of a list. -/
def nsum (L : List Nat) : Nat := (L.map fun p => L.prod / p).sum

def mism (tabs : Array (Array Int)) (tg : List (Nat × Int)) (m : Nat) : Bool :=
  tg.any fun e => decide ((tabs[e.1]!)[m % e.1]! ≠ e.2)

def loop (tabs : Array (Array Int)) (tg : List (Nat × Int)) : Nat → Nat → Bool
  | _, 0 => true
  | m, f + 1 => mism tabs tg m && loop tabs tg (m + 2) f

def leaf (tabs : Array (Array Int)) (L : List Nat) : Bool :=
  let D := L.prod
  let N := nsum L
  match L.getLast? with
  | none => true
  | some r =>
    if 2 * D ≤ N then false
    else
      let M := D / (2 * D - N)
      let tg := (L.filter (· ≠ 2)).map fun ℓ => (ℓ, (tabs[ℓ]!)[(D / ℓ) % ℓ]!)
      loop tabs tg (r + 2) ((M - r) / 2)

end Erdos307
