import Erdos307.PairSector

/-!
# Sector decomposition

`prop:sectors`: a prime support `U` with `T(U) > 2` either lies in the tail family of `U \ {max U}`
(single-tail sector) or, when `T(U) - 2 < 1/max U`, has both `59`-subsets `U \ {p}` and `U \ {q}`
(`p > q` the two largest elements) below mass `2` (pair sector).

Here `T U = ∑ 1/p`. The statement is for any finite set of naturals with a largest element `p` and
second-largest `q`; the cardinality `60` only enters through the size of the bases, not the logic.
The rigidity `T = 2` impossible (hypothesis `hrig`) is the oddness of the numerator
(`mass_ne_two` in `PairSector`), and the count `49,961` of admissible bases is a computation: neither
is part of this file.

Paper: Proposition `prop:sectors`.
-/

namespace Erdos307

open Finset

/-- Reciprocal mass of a finite set of naturals. -/
noncomputable def mass (U : Finset ℕ) : ℚ := ∑ p ∈ U, (p : ℚ)⁻¹

lemma mass_erase {U : Finset ℕ} {p : ℕ} (hp : p ∈ U) : mass (U.erase p) = mass U - (p : ℚ)⁻¹ := by
  unfold mass
  rw [← Finset.sum_erase_add U (fun p => (p : ℚ)⁻¹) hp]; ring

/-- **`prop:sectors`, case (i).** If `T(U) - 2 ≥ 1/max U` then the base `U \ {max U}` has mass `≥ 2`,
i.e. `U` lies in its tail family; with rigidity (`T ≠ 2` on the base) the base is strictly above `2`. -/
theorem sector_single {U : Finset ℕ} {p : ℕ} (hp : p ∈ U) (h : (p : ℚ)⁻¹ ≤ mass U - 2) :
    2 ≤ mass (U.erase p) := by
  rw [mass_erase hp]; linarith

theorem sector_single_strict {U : Finset ℕ} {p : ℕ} (hp : p ∈ U) (h : (p : ℚ)⁻¹ ≤ mass U - 2)
    (hrig : mass (U.erase p) ≠ 2) : 2 < mass (U.erase p) :=
  lt_of_le_of_ne (sector_single hp h) (Ne.symm hrig)

/-- **`prop:sectors`, case (ii).** If `T(U) - 2 < 1/p` with `p = max U`, and `q < p` is any other
element (in particular the second largest), then both `59`-subsets `U \ {p}` and `U \ {q}` have mass
`< 2`. -/
theorem sector_pair {U : Finset ℕ} {p q : ℕ} (hp : p ∈ U) (hq : q ∈ U) (hqp : q < p) (hq0 : 0 < q)
    (h : mass U - 2 < (p : ℚ)⁻¹) :
    mass (U.erase p) < 2 ∧ mass (U.erase q) < 2 := by
  refine ⟨by rw [mass_erase hp]; linarith, ?_⟩
  rw [mass_erase hq]
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq0
  have : (p : ℚ)⁻¹ < (q : ℚ)⁻¹ := inv_strictAnti₀ hq' (by exact_mod_cast hqp)
  linarith

/-- **`prop:sectors`, exclusivity and exhaustion.** For `T(U) > 2` and `p = max U` exactly one of
the two cases holds; in case (ii) both `59`-subsets lie below `2`, hence `U` is in no single-tail
family of a `59`-subset obtained by removing `p` or `q`. -/
theorem sectors {U : Finset ℕ} {p q : ℕ} (hp : p ∈ U) (hq : q ∈ U) (hqp : q < p) (hq0 : 0 < q) :
    ((p : ℚ)⁻¹ ≤ mass U - 2 ∧ 2 ≤ mass (U.erase p)) ∨
    (mass U - 2 < (p : ℚ)⁻¹ ∧ mass (U.erase p) < 2 ∧ mass (U.erase q) < 2) := by
  rcases le_or_gt ((p : ℚ)⁻¹) (mass U - 2) with h | h
  · exact Or.inl ⟨h, sector_single hp h⟩
  · exact Or.inr ⟨h, sector_pair hp hq hqp hq0 h⟩

end Erdos307
