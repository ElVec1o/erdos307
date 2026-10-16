import Erdos307.Computational.PairEnum
import Erdos307.Computational.Euler
import Erdos307.PairNecessary

/-!
# Track B, M3: the pair-sector leaf

For a base `R` (ascending list `L`, `r = max`), the leaf tests every odd `m ∈ (r, D/(2D - N)]` for a prime
`ℓ ∈ R`, `ℓ ≠ 2`, at which `(m|ℓ) ≠ ((D/ℓ)|ℓ)`, reading Legendre symbols from a precomputed table.
`leaf_sound` says that if the leaf returns `true`, no prime `p > r` can complete `R` to a cycle's support:
`p(2D - N) ≤ D` and the character conditions cannot both hold.

Paper: Proposition `prop:pairclosed`.
-/

namespace Erdos307

/-- `tabs[ℓ][x] = eulerSym ℓ x` for `ℓ ≤ B`, `x < ℓ`. -/
def mkTabs (B : ℕ) : Array (Array ℤ) :=
  (Array.range (B + 1)).map fun ℓ => (Array.range ℓ).map fun x => eulerSym ℓ x

theorem mkTabs_get {B ℓ x : ℕ} (hℓ : ℓ ≤ B) (hx : x < ℓ) : ((mkTabs B)[ℓ]!)[x]! = eulerSym ℓ x := by
  have h1 : ℓ < (mkTabs B).size := by simp [mkTabs]; omega
  have h2 : x < ((mkTabs B)[ℓ]'h1).size := by simp [mkTabs]; omega
  rw [getElem!_pos (mkTabs B) ℓ h1, getElem!_pos _ x h2]
  simp [mkTabs]

/-- `csum` of a list. -/
def nsum (L : List ℕ) : ℕ := (L.map fun p => L.prod / p).sum

def mism (tabs : Array (Array ℤ)) (tg : List (ℕ × ℤ)) (m : ℕ) : Bool :=
  tg.any fun e => decide ((tabs[e.1]!)[m % e.1]! ≠ e.2)

def loop (tabs : Array (Array ℤ)) (tg : List (ℕ × ℤ)) : ℕ → ℕ → Bool
  | _, 0 => true
  | m, f + 1 => mism tabs tg m && loop tabs tg (m + 2) f

theorem loop_sound (tabs : Array (Array ℤ)) (tg : List (ℕ × ℤ)) :
    ∀ (f m : ℕ), loop tabs tg m f = true → ∀ k < f, mism tabs tg (m + 2 * k) = true := by
  intro f
  induction f with
  | zero => intro m _ k hk; omega
  | succ f ih =>
    intro m h k hk
    rw [loop, Bool.and_eq_true] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := ih (m + 2) h.2 k (by omega)
      have e : m + 2 + 2 * k = m + 2 * (k + 1) := by ring
      rwa [e] at this

def leaf (tabs : Array (Array ℤ)) (L : List ℕ) : Bool :=
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

lemma nsum_sort (U : Finset ℕ) : nsum (U.sort (· ≤ ·)) = csum U := by
  unfold nsum csum
  rw [prod_sort]
  have h := (Finset.sort_perm_toList U (· ≤ ·)).map (fun p : ℕ => dprod U / p)
  rw [h.sum_eq]
  rw [list_sum_toList U (fun p => dprod U / p)]

theorem leaf_sound {B : ℕ} {R : Finset ℕ} {r : ℕ} (hR : ∀ x ∈ R, x.Prime) (hB : ∀ x ∈ R, x ≤ B)
    (hN : csum R < 2 * dprod R) (hr : (R.sort (· ≤ ·)).getLast? = some r) (hr2 : r ≠ 2)
    (hleaf : leaf (mkTabs B) (R.sort (· ≤ ·)) = true) :
    ∀ p : ℕ, p.Prime → r < p → (p : ℤ) * (2 * dprod R - csum R) ≤ dprod R →
      ∃ ℓ ∈ R, ℓ ≠ 2 ∧ ∃ _ : Fact ℓ.Prime,
        legendreSym ℓ (p : ℤ) ≠ legendreSym ℓ ((dprod (R.erase ℓ) : ℕ) : ℤ) := by
  intro p hp hrp hp1
  set L := R.sort (· ≤ ·) with hL
  have hprod : L.prod = dprod R := prod_sort R
  have hns : nsum L = csum R := nsum_sort R
  have hrmem : r ∈ R := by
    rw [← Finset.mem_sort (· ≤ ·)]; exact List.mem_of_getLast? hr
  have hrprime := hR r hrmem
  have hrodd : Odd r := hrprime.odd_of_ne_two hr2
  have hp2 : p ≠ 2 := by have := hrprime.two_le; omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hnlt : ¬ (2 * dprod R ≤ csum R) := not_le.2 hN
  unfold leaf at hleaf
  rw [hr] at hleaf
  simp only [hprod, hns, if_neg hnlt] at hleaf
  -- `p ≤ M`
  have hpM : p ≤ dprod R / (2 * dprod R - csum R) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have : ((p * (2 * dprod R - csum R) : ℕ) : ℤ) ≤ (dprod R : ℤ) := by
      push_cast [Nat.cast_sub hN.le]; exact hp1
    exact_mod_cast this
  -- p = r + 2 + 2k with k < fuel
  obtain ⟨a, ha⟩ := hrodd
  obtain ⟨b, hb⟩ := hpodd
  have hk : p = (r + 2) + 2 * (b - a - 1) := by omega
  have hkf : b - a - 1 < (dprod R / (2 * dprod R - csum R) - r) / 2 := by omega
  have hmism := loop_sound _ _ _ _ hleaf (b - a - 1) hkf
  rw [← hk] at hmism
  unfold mism at hmism
  rw [List.any_eq_true] at hmism
  obtain ⟨⟨ℓ, t⟩, hmem, hne⟩ := hmism
  rw [List.mem_map] at hmem
  obtain ⟨ℓ', hℓ', heq⟩ := hmem
  rw [List.mem_filter] at hℓ'
  obtain ⟨hℓL, hℓ2⟩ := hℓ'
  have hℓR : ℓ' ∈ R := (Finset.mem_sort (· ≤ ·)).1 hℓL
  have hℓ2' : ℓ' ≠ 2 := by simpa using hℓ2
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hℓp := hR ℓ' hℓR
  haveI : Fact ℓ'.Prime := ⟨hℓp⟩
  have hℓB := hB ℓ' hℓR
  refine ⟨ℓ', hℓR, hℓ2', ⟨hℓp⟩, ?_⟩
  simp only [decide_eq_true_eq] at hne
  have hdiv : dprod R / ℓ' = dprod (R.erase ℓ') := dprod_div R hℓR hℓp.pos
  have hlt1 : p % ℓ' < ℓ' := Nat.mod_lt _ hℓp.pos
  have hlt2 : (dprod R / ℓ') % ℓ' < ℓ' := Nat.mod_lt _ hℓp.pos
  rw [mkTabs_get hℓB hlt1, mkTabs_get hℓB hlt2] at hne
  rw [legendreSym_eq_eulerSym hℓ2' p, ← hdiv, legendreSym_eq_eulerSym hℓ2' (dprod R / ℓ')]
  exact hne

end Erdos307
