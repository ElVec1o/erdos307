import Erdos307.Level61Bound
import Erdos307.Sectors
import Erdos307.Lvl60Factor

/-!
# Level 60 reduced to two explicit finite statements

`erdos307_sixtyone_of_level60` assumes `hL`: no solution has exactly `60` primes. This file replaces
`hL` by two named statements, one per sector of `prop:sectors`, so that what is *computed* and what
is *proved* are separated precisely.

* `PairSectorEmpty`: no two-cycle is supported on a `60`-set `U` whose largest element `p` has
  `T(U ∖ {p}) < 2` (the pair sector). Computed by `prop:pairclosed`.
* `TailSectorEmpty`: for every base `S` of `59` primes containing `2`, with `T(S) ≥ 2`, and every
  prime `q` larger than all of `S`, there are no integers `x, y` with `0 < x < A`, `x² = A q + D`,
  `y² = B q + D` (where `D = ∏S`, `N = csum S`, `A = N + 2D`, `B = N - 2D`). This is the
  arithmetic content of a two-cycle on `S ∪ {q}` by `lvl60_factor_ab`; it is what the Stage A and
  q-sieve computations decide.

`level60_empty_of_sectors` proves `hL` from the two, and `erdos307_sixtyone_of_sectors` the barrier
`61`. Everything the computations must establish is therefore the two `Prop`s above; nothing else
about level `60` is assumed. The two are *not* proved here: they are finite computations.

Paper: Proposition `prop:level60closed`.
-/

namespace Erdos307

open Finset

/-- A two-cycle on the support `U`: `U = P ⊔ Q`, `P' = ∏Q`, `Q' = ∏P`. -/
def IsCycle (U : Finset ℕ) : Prop :=
  ∃ P Q : Finset ℕ, Disjoint P Q ∧ P ∪ Q = U ∧ csum P = dprod Q ∧ csum Q = dprod P

/-- The pair sector at level `60` is empty. -/
def PairSectorEmpty : Prop :=
  ∀ U : Finset ℕ, (∀ r ∈ U, r.Prime) → U.card = 60 → ∀ p ∈ U, (∀ s ∈ U, s ≤ p) →
    mass (U.erase p) < 2 → ¬ IsCycle U

/-- The arithmetic content of a two-cycle on `S ∪ {q}`. -/
def TailArith (S : Finset ℕ) (q : ℕ) : Prop :=
  ∃ x y : ℤ, 0 < x ∧ x < (csum S : ℤ) + 2 * dprod S ∧
    x ^ 2 = ((csum S : ℤ) + 2 * dprod S) * q + dprod S ∧
    y ^ 2 = ((csum S : ℤ) - 2 * dprod S) * q + dprod S

/-- The single-tail sector at level `60` is empty. -/
def TailSectorEmpty : Prop :=
  ∀ S : Finset ℕ, (∀ r ∈ S, r.Prime) → 2 ∈ S → S.card = 59 → 2 ≤ mass S →
    ∀ q : ℕ, q.Prime → (∀ s ∈ S, s < q) → ¬ TailArith S q

lemma cycle_of_solution {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) : IsCycle (P ∪ Q) := by
  have hdP : (0 : ℚ) < (dprod P : ℚ) := by exact_mod_cast dprod_pos hP
  have hdQ : (0 : ℚ) < (dprod Q : ℚ) := by exact_mod_cast dprod_pos hQ
  have heq' : (csum P : ℚ) / (dprod P : ℚ) * ((csum Q : ℚ) / (dprod Q : ℚ)) = 1 := by
    rw [← recipSum_eq P hP, ← recipSum_eq Q hQ]; exact heq
  obtain ⟨hNPDQ, hNQDP⟩ :=
    solution_structure (rigidity_coprime P hP) (rigidity_coprime Q hQ)
      (by exact_mod_cast hdP.ne') (by exact_mod_cast hdQ.ne') heq'
  exact ⟨P, Q, solution_disjoint hP hQ hNQDP, rfl, hNPDQ, hNQDP⟩

lemma T61_lt : ∑ i ∈ Finset.range 61, (Nat.nth Nat.Prime i : ℚ)⁻¹ < 2.01 := by
  rw [sum_first61]; unfold N59 P59; norm_num

/-- A level-`60` solution contains `2`: otherwise adjoining `2` gives `61` primes of mass `< 2.5`,
but `T(U) ≥ 2` forces the mass of `U ∪ {2}` to be `≥ 2.5`. -/
lemma two_mem_of_solution {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) (hc : (P ∪ Q).card = 60) :
    2 ∈ P ∪ Q := by
  by_contra h2
  have hU : ∀ r ∈ P ∪ Q, r.Prime := by
    intro r hr; rcases Finset.mem_union.mp hr with h | h
    · exact hP r h
    · exact hQ r h
  obtain ⟨_, hNQDP⟩ := (by
    have hdP : (0 : ℚ) < (dprod P : ℚ) := by exact_mod_cast dprod_pos hP
    have hdQ : (0 : ℚ) < (dprod Q : ℚ) := by exact_mod_cast dprod_pos hQ
    have heq' : (csum P : ℚ) / (dprod P : ℚ) * ((csum Q : ℚ) / (dprod Q : ℚ)) = 1 := by
      rw [← recipSum_eq P hP, ← recipSum_eq Q hQ]; exact heq
    exact solution_structure (rigidity_coprime P hP) (rigidity_coprime Q hQ)
      (by exact_mod_cast hdP.ne') (by exact_mod_cast hdQ.ne') heq')
  have hdisj : Disjoint P Q := solution_disjoint hP hQ hNQDP
  have hs0 : (∑ p ∈ P, (p : ℚ)⁻¹) ≠ 0 := by
    intro h; rw [h, zero_mul] at heq; norm_num at heq
  have hs_pos : 0 < ∑ p ∈ P, (p : ℚ)⁻¹ :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun p hp => by positivity)) (Ne.symm hs0)
  have hT : (2 : ℚ) ≤ ∑ r ∈ P ∪ Q, (r : ℚ)⁻¹ := by
    rw [Finset.sum_union hdisj]; exact recip_sum_ge_two hs_pos heq
  have hV : ∀ r ∈ insert 2 (P ∪ Q), r.Prime := by
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | h
    · norm_num
    · exact hU r h
  have hcard : (insert 2 (P ∪ Q)).card = 61 := by rw [Finset.card_insert_of_notMem h2, hc]
  have h1 := recipSum_le_first_primes hV
  rw [hcard, Finset.sum_insert h2] at h1
  have := T61_lt
  have h3 : (2 : ℚ) ^ 0 = 1 := rfl
  norm_num at h1
  linarith

/-- **`hL` from the two sector statements.** -/
theorem level60_empty_of_sectors (hpair : PairSectorEmpty) (htail : TailSectorEmpty) :
    ∀ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ q ∈ Q, q.Prime) →
      (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1 → (P ∪ Q).card ≠ 60 := by
  intro P Q hP hQ heq hc
  have hU : ∀ r ∈ P ∪ Q, r.Prime := by
    intro r hr; rcases Finset.mem_union.mp hr with h | h
    · exact hP r h
    · exact hQ r h
  have hcyc := cycle_of_solution hP hQ heq
  have h2 := two_mem_of_solution hP hQ heq hc
  have hne : (P ∪ Q).Nonempty := ⟨2, h2⟩
  set U := P ∪ Q with hUdef
  set p := U.max' hne with hp
  have hpU : p ∈ U := Finset.max'_mem U hne
  have hmax : ∀ s ∈ U, s ≤ p := fun s hs => Finset.le_max' U s hs
  by_cases hm : mass (U.erase p) < 2
  · exact hpair U hU hc p hpU hmax hm hcyc
  · push Not at hm
    obtain ⟨P', Q', hdisj, hUe, h1, h2'⟩ := hcyc
    set S := U.erase p with hS
    have hSp : ∀ r ∈ S, r.Prime := fun r hr => hU r (Finset.mem_of_mem_erase hr)
    have hpprime := hU p hpU
    have hpS : p ∉ S := Finset.notMem_erase p U
    have h2p : p ≠ 2 := by
      intro hp2
      have hsub : U ⊆ ({2} : Finset ℕ) := by
        intro s hs; have := hmax s hs; have := (hU s hs).two_le
        simp only [Finset.mem_singleton]; omega
      have := Finset.card_le_card hsub
      simp at this; omega
    have h2S : 2 ∈ S := Finset.mem_erase.2 ⟨fun h => h2p h.symm, h2⟩
    have hcardS : S.card = 59 := by rw [hS, Finset.card_erase_of_mem hpU, hc]
    have hUS : P' ∪ Q' = S ∪ {p} := by
      rw [hUe]
      ext x
      simp only [hS, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro hx; by_cases h : x = p
        · exact Or.inr h
        · exact Or.inl ⟨h, hx⟩
      · rintro (⟨-, hx⟩ | rfl)
        · exact hx
        · exact hpU
    obtain ⟨a, b, hab, hpos, hlt, hsq⟩ :=
      lvl60_factor_ab hSp hpprime hpS hdisj hUS h1 h2'
    have hlt' : ∀ s ∈ S, s < p := fun s hs =>
      lt_of_le_of_ne (hmax s (Finset.mem_of_mem_erase hs)) (Finset.ne_of_mem_erase hs)
    refine htail S hSp h2S hcardS hm p hpprime hlt' ⟨(a : ℤ) + b, (a : ℤ) - b, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hpos
    · exact_mod_cast hlt
    · exact_mod_cast hsq
    · have hab' : (a : ℤ) * b = dprod S * p := by exact_mod_cast hab
      have hsq' : ((a : ℤ) + b) ^ 2 = ((csum S : ℤ) + 2 * dprod S) * p + dprod S := by
        exact_mod_cast hsq
      nlinarith [hab', hsq']

/-- **The barrier `61` from the two sector statements.** -/
theorem erdos307_sixtyone_of_sectors (hpair : PairSectorEmpty) (htail : TailSectorEmpty)
    {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) :
    61 ≤ (P ∪ Q).card :=
  erdos307_sixtyone_of_level60 (level60_empty_of_sectors hpair htail) hP hQ heq

end Erdos307
