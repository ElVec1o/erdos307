import Erdos307.Rigidity
import Erdos307.Barrier

/-!
# Erdős #307 — Capstone: the barrier over genuine prime sets

This file wires the component theorems
* T1 `rigidity_coprime`  (the reciprocal-sum fraction is reduced),
* T2 `solution_structure` (`csum P = dprod Q`, `csum Q = dprod P`),
* T4 `barrier`           (the algebraic/numeric `D_P² ≥ 4·10¹¹²` engine)
into a **single** statement about two finite sets of primes `P, Q` with
`(∑_{p∈P} 1/p)(∑_{q∈Q} 1/q) = 1`.

The only classical ingredient still imported as an explicit hypothesis is the
smallest-primes extremality `hRatio` (target **T4′**); everything else — including the
disjointness of `P` and `Q` and the rigidity identity `R = s·D_P²` — is discharged here.

Status: **machine-checked**.  Compiles under `lake build` (Lean / mathlib v4.30.0); `#print axioms
erdos307_barrier` shows only `propext, Classical.choice, Quot.sound` — no `sorryAx`.  Confirmed green Jun 14 2026.
-/

namespace Erdos307

open Finset

/-- The product of a set of primes is positive. -/
lemma dprod_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : 0 < dprod S := by
  unfold dprod
  exact Finset.prod_pos fun p hp => (hS p hp).pos

/-- For a set of primes, `∑ 1/p = csum S / dprod S` as rationals. -/
lemma recipSum_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, (p : ℚ)⁻¹) = (csum S : ℚ) / (dprod S : ℚ) := by
  have hdpos : (0 : ℚ) < (dprod S : ℚ) := by exact_mod_cast dprod_pos hS
  rw [csum, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp0 : 0 < p := (hS p hp).pos
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp0
  have hdvd : p ∣ dprod S := by
    unfold dprod; exact Finset.dvd_prod_of_mem _ hp
  rw [Nat.cast_div hdvd (by exact_mod_cast hp0.ne')]
  field_simp

/-- **Disjointness.** Two prime sets whose reduced reciprocal sums multiply to `1` are disjoint.
A shared prime `r` would divide both `csum Q` (`= dprod P ∋ r`) and `dprod Q`, contradicting T1. -/
lemma solution_disjoint {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hNQDP : csum Q = dprod P) :
    Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro r hrP hrQ
  have hr : r.Prime := hP r hrP
  have ha : r ∣ dprod P := by unfold dprod; exact Finset.dvd_prod_of_mem _ hrP
  have hb : r ∣ dprod Q := by unfold dprod; exact Finset.dvd_prod_of_mem _ hrQ
  have ha' : r ∣ csum Q := hNQDP ▸ ha
  have hgcd : r ∣ Nat.gcd (csum Q) (dprod Q) := Nat.dvd_gcd ha' hb
  rw [rigidity_coprime Q hQ] at hgcd
  exact hr.one_lt.ne' (Nat.dvd_one.mp hgcd)

/-- **Erdős #307 barrier, over genuine prime sets.**
Let `P, Q` be finite sets of primes with `Q` nonempty and
`(∑_{p∈P} 1/p)(∑_{q∈Q} 1/q) = 1`.  Assume the smallest-primes extremality bound
`(4·10¹¹²)·(∑_{r∈P∪Q} 1/r) ≤ ∏_{r∈P∪Q} r` (target T4′).  Then `(∏_{p∈P} p)² ≥ 4·10¹¹²`,
i.e. `D_P ≥ 2·10⁵⁶`. -/
theorem erdos307_barrier {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hQne : Q.Nonempty)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1)
    (hRatio : (4 * 10 ^ 112 : ℚ) * (∑ r ∈ P ∪ Q, (r : ℚ)⁻¹) ≤ (dprod (P ∪ Q) : ℚ)) :
    (4 * 10 ^ 112 : ℚ) ≤ (dprod P : ℚ) ^ 2 := by
  have hdP : (0 : ℚ) < (dprod P : ℚ) := by exact_mod_cast dprod_pos hP
  have hdQ : (0 : ℚ) < (dprod Q : ℚ) := by exact_mod_cast dprod_pos hQ
  -- T2: solution structure, from the equation rewritten in `csum/dprod` form.
  have heq' : (csum P : ℚ) / (dprod P : ℚ) * ((csum Q : ℚ) / (dprod Q : ℚ)) = 1 := by
    rw [← recipSum_eq P hP, ← recipSum_eq Q hQ]; exact heq
  obtain ⟨hNPDQ, hNQDP⟩ :=
    solution_structure (rigidity_coprime P hP) (rigidity_coprime Q hQ)
      (by exact_mod_cast hdP.ne') (by exact_mod_cast hdQ.ne') heq'
  -- Disjointness, hence `∏_{P∪Q} = ∏_P · ∏_Q` and `∑_{P∪Q} = ∑_P + ∑_Q`.
  have hdisj : Disjoint P Q := solution_disjoint hP hQ hNQDP
  have hRnat : dprod (P ∪ Q) = dprod P * dprod Q := by
    unfold dprod; rw [Finset.prod_union hdisj]
  have hTsplit : (∑ r ∈ P ∪ Q, (r : ℚ)⁻¹)
      = (∑ p ∈ P, (p : ℚ)⁻¹) + (∑ q ∈ Q, (q : ℚ)⁻¹) :=
    Finset.sum_union hdisj
  -- Abbreviations matching `barrier`.
  set s : ℚ := ∑ p ∈ P, (p : ℚ)⁻¹ with hs
  set t : ℚ := ∑ q ∈ Q, (q : ℚ)⁻¹ with ht
  have ht_pos : 0 < t := by
    rw [ht]; refine Finset.sum_pos (fun q hq => ?_) hQne
    exact inv_pos.mpr (by exact_mod_cast (hQ q hq).pos)
  have hs_nonneg : 0 ≤ s := by
    rw [hs]; refine Finset.sum_nonneg (fun p hp => ?_)
    exact inv_nonneg.mpr (by exact_mod_cast (hP p hp).pos.le)
  -- Apply the abstract barrier with `T = s + t`, `R = ∏_{P∪Q}`.
  refine barrier (DP := (dprod P : ℚ)) (s := s) (T := s + t)
      (R := (dprod (P ∪ Q) : ℚ)) ?_ ?_ ?_ ?_
  · -- 0 < T
    linarith
  · -- s ≤ T
    linarith
  · -- (4·10¹¹²)·T ≤ R
    rw [hTsplit] at hRatio; exact hRatio
  · -- R = s · D_P²   (rigidity identity: s = csum P/dprod P = dprod Q/dprod P)
    have hsval : s = (dprod Q : ℚ) / (dprod P : ℚ) := by
      rw [hs, recipSum_eq P hP, hNPDQ]
    rw [hRnat, hsval]
    push_cast
    field_simp

end Erdos307
