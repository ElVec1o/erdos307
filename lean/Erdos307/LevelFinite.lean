import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Each level of #307 carries only finitely many solutions

`prop:levelbarrier` shows the admissible *supports* at every level above `59` are infinite, and
`rem:levelbarrier` concluded that the level-by-level programme has no continuation. This file proves
that the *solutions* at each level are nevertheless finite: for every pair of cardinalities `(m,n)`,
the equation `(∑_P 1/p)(∑_Q 1/q) = 1` has only finitely many solutions in sets of integers `≥ 2` of
those sizes, primes in particular. So every level of #307 is a finite question after all; what is
infinite is only the haystack, not the needles.

The proof is an induction on `m + n` through the inhomogeneous form
`(c₁ + ∑_A 1/a)(c₂ + ∑_B 1/b) = 1` with constants `c₁, c₂ ≥ 0`. Writing `u, v` for the two sums and
`ε = 1 - c₁c₂`, expanding gives `c₁v + u(c₂ + v) = ε`, and any solution forces `ε > 0`. One of the
two terms is `≥ ε/2`. If `u(c₂+v) ≥ ε/2` then, since `v ≤ n/2`, the sum `u` is bounded below, so `A`
contains an element `a₀ ≤ m(2c₂+n)/ε`; moving `a₀` into the constant recurses at `m - 1`. The other
case is symmetric with `b₀ ≤ 2c₁n/ε`. Either way a bounded element exists, and the solution set
injects into finitely many smaller problems.

Paper: Proposition `prop:levelfinite`, Remark `rem:levelbarrier`.
-/

namespace Erdos307

open Finset

/-- The solutions of the inhomogeneous level equation at cardinalities `(m, n)`. -/
def sols (m n : ℕ) (c₁ c₂ : ℚ) : Set (Finset ℕ × Finset ℕ) :=
  {AB | (∀ a ∈ AB.1, 2 ≤ a) ∧ (∀ b ∈ AB.2, 2 ≤ b) ∧ AB.1.card = m ∧ AB.2.card = n ∧
    (c₁ + ∑ a ∈ AB.1, ((a : ℚ))⁻¹) * (c₂ + ∑ b ∈ AB.2, ((b : ℚ))⁻¹) = 1}

/-- A set of integers `≥ 2` of size `n` has reciprocal sum at most `n/2`. -/
lemma rsum_le_half_card {B : Finset ℕ} (h2 : ∀ b ∈ B, 2 ≤ b) :
    ∑ b ∈ B, ((b : ℚ))⁻¹ ≤ (B.card : ℚ) / 2 := by
  have h := Finset.sum_le_card_nsmul B (fun b => ((b : ℚ))⁻¹) (1 / 2) ?_
  · rwa [nsmul_eq_mul, mul_one_div] at h
  · intro b hb
    have hb2 : (2 : ℚ) ≤ (b : ℚ) := by exact_mod_cast h2 b hb
    rw [one_div]
    exact inv_anti₀ (by norm_num) hb2

/-- A nonempty set whose reciprocal sum is `u` contains an element `≤ card/u`. -/
lemma exists_small_of_sum {A : Finset ℕ} {u : ℚ} (hA : A.Nonempty) (hu : 0 < u)
    (hsum : ∑ a ∈ A, ((a : ℚ))⁻¹ = u) (h2 : ∀ a ∈ A, 2 ≤ a) :
    ∃ a₀ ∈ A, (a₀ : ℚ) ≤ (A.card : ℚ) / u := by
  have hcard : (0 : ℚ) < (A.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have havg : ∑ _a ∈ A, u / (A.card : ℚ) ≤ ∑ a ∈ A, ((a : ℚ))⁻¹ := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ (ne_of_gt hcard)]
    exact hsum.ge
  obtain ⟨a₀, ha₀, hle⟩ := Finset.exists_le_of_sum_le hA havg
  refine ⟨a₀, ha₀, ?_⟩
  have ha₀pos : (0 : ℚ) < (a₀ : ℚ) := by
    have := h2 a₀ ha₀
    have : (2 : ℚ) ≤ (a₀ : ℚ) := by exact_mod_cast this
    linarith
  rw [div_le_iff₀ hcard] at hle
  rw [le_div_iff₀ hu]
  have h2' : (a₀ : ℚ) * u ≤ (a₀ : ℚ) * ((a₀ : ℚ))⁻¹ * (A.card : ℚ) := by
    have := mul_le_mul_of_nonneg_left hle (le_of_lt ha₀pos)
    calc (a₀ : ℚ) * u ≤ (a₀ : ℚ) * ((a₀ : ℚ)⁻¹ * (A.card : ℚ)) := this
    _ = (a₀ : ℚ) * ((a₀ : ℚ))⁻¹ * (A.card : ℚ) := by ring
  rwa [mul_inv_cancel₀ (ne_of_gt ha₀pos), one_mul] at h2'

/-- **Per-level finiteness.** For every cardinality pair and nonnegative constants, the level
equation has finitely many solutions. -/
theorem sols_finite : ∀ (k m n : ℕ), m + n = k → ∀ (c₁ c₂ : ℚ), 0 ≤ c₁ → 0 ≤ c₂ →
    (sols m n c₁ c₂).Finite := by
  intro k
  induction k with
  | zero =>
    intro m n hmn c₁ c₂ _ _
    have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst hm; subst hn
    refine Set.Finite.subset (Set.finite_singleton ((∅ : Finset ℕ), (∅ : Finset ℕ))) ?_
    rintro ⟨A, B⟩ ⟨_, _, hA, hB, _⟩
    simp only [Finset.card_eq_zero] at hA hB
    simp [hA, hB]
  | succ k ih =>
    intro m n hmn c₁ c₂ hc₁ hc₂
    set e : ℚ := 1 - c₁ * c₂ with he_def
    -- the two covers, guarded so the inductive hypothesis always applies
    set NB : ℕ := ⌊(m : ℚ) * (2 * c₂ + n) / e⌋₊ with hNB
    set NA : ℕ := ⌊2 * c₁ * (n : ℚ) / e⌋₊ with hNA
    classical
    set L : Set (Finset ℕ × Finset ℕ) :=
      if 1 ≤ m then
        ⋃ a₀ ∈ (↑(Finset.Iic NB) : Set ℕ),
          (fun P : Finset ℕ × Finset ℕ => (insert a₀ P.1, P.2)) ''
            sols (m - 1) n (c₁ + ((a₀ : ℚ))⁻¹) c₂
      else ∅ with hL
    set R : Set (Finset ℕ × Finset ℕ) :=
      if 1 ≤ n then
        ⋃ b₀ ∈ (↑(Finset.Iic NA) : Set ℕ),
          (fun P : Finset ℕ × Finset ℕ => (P.1, insert b₀ P.2)) ''
            sols m (n - 1) c₁ (c₂ + ((b₀ : ℚ))⁻¹)
      else ∅ with hR
    have hLfin : L.Finite := by
      rw [hL]
      split_ifs with hm
      · refine Set.Finite.biUnion (Finset.Iic NB).finite_toSet fun a₀ _ => ?_
        exact Set.Finite.image _ (ih (m - 1) n (by omega) _ _ (by positivity) hc₂)
      · exact Set.finite_empty
    have hRfin : R.Finite := by
      rw [hR]
      split_ifs with hn
      · refine Set.Finite.biUnion (Finset.Iic NA).finite_toSet fun b₀ _ => ?_
        exact Set.Finite.image _ (ih m (n - 1) (by omega) _ _ hc₁ (by positivity))
      · exact Set.finite_empty
    refine Set.Finite.subset (hLfin.union hRfin) ?_
    rintro ⟨A, B⟩ ⟨h2A, h2B, hcA, hcB, heq⟩
    replace h2A : ∀ a ∈ A, 2 ≤ a := h2A
    replace h2B : ∀ b ∈ B, 2 ≤ b := h2B
    replace hcA : A.card = m := hcA
    replace hcB : B.card = n := hcB
    replace heq : (c₁ + ∑ a ∈ A, ((a : ℚ))⁻¹) * (c₂ + ∑ b ∈ B, ((b : ℚ))⁻¹) = 1 := heq
    set u : ℚ := ∑ a ∈ A, ((a : ℚ))⁻¹ with hu_def
    set v : ℚ := ∑ b ∈ B, ((b : ℚ))⁻¹ with hv_def
    have hu0 : 0 ≤ u := Finset.sum_nonneg fun a _ => by positivity
    have hv0 : 0 ≤ v := Finset.sum_nonneg fun b _ => by positivity
    have hkey : c₁ * v + u * (c₂ + v) = e := by
      rw [he_def]; linear_combination heq
    have hepos : 0 < e := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- A empty, so u = 0; the equation forces c₁ > 0 and v > 0
        have hAe : A = ∅ := Finset.card_eq_zero.mp (hm ▸ hcA)
        have hu' : u = 0 := by rw [hu_def, hAe]; simp
        have hn : 1 ≤ n := by omega
        have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
        have hvpos : 0 < v := by
          rw [hv_def]
          refine Finset.sum_pos (fun b hb => by have := h2B b hb; positivity) hBne
        have hc₁pos : 0 < c₁ := by
          rcases lt_or_eq_of_le hc₁ with h | h
          · exact h
          · exfalso
            rw [← h, hu'] at heq
            norm_num at heq
        rw [← hkey, hu']
        nlinarith [hvpos, hc₁pos]
      · have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
        have hupos : 0 < u := by
          rw [hu_def]
          exact Finset.sum_pos (fun a ha => by have := h2A a ha; positivity) hAne
        have hcv : 0 < c₂ + v := by
          rcases lt_or_eq_of_le (by positivity : (0:ℚ) ≤ c₂ + v) with h | h
          · exact h
          · exfalso
            rw [← h, mul_zero] at heq
            norm_num at heq
        rw [← hkey]
        nlinarith [hupos, hcv, hc₁, hv0]
    by_cases hcase : e / 2 ≤ u * (c₂ + v)
    · -- case B: the A side contains a bounded element
      left
      have hucv : 0 < u * (c₂ + v) := lt_of_lt_of_le (by linarith) hcase
      have hupos : 0 < u := by
        rcases lt_or_eq_of_le hu0 with h | h
        · exact h
        · exfalso; rw [← h] at hucv; simp at hucv
      have hcvpos : 0 < c₂ + v := by
        by_contra hcon
        push_neg at hcon
        nlinarith [hucv, hupos, hcon]
      have hAne : A.Nonempty := by
        by_contra hA
        rw [Finset.not_nonempty_iff_eq_empty] at hA
        rw [hu_def, hA] at hupos; simp at hupos
      have hm : 1 ≤ m := by
        rw [← hcA]; exact Finset.card_pos.mpr hAne
      have hvhalf : v ≤ (n : ℚ) / 2 := by
        rw [hv_def, ← hcB]; exact rsum_le_half_card h2B
      have hub : e / (2 * c₂ + (n : ℚ)) ≤ u := by
        have hden : 0 < 2 * c₂ + (n : ℚ) := by
          have : c₂ + v ≤ c₂ + (n : ℚ) / 2 := by linarith
          nlinarith [hcvpos, this]
        rw [div_le_iff₀ hden]
        nlinarith [hcase, hvhalf, hupos, mul_nonneg hu0 (by linarith [hvhalf] : (0:ℚ) ≤ (n : ℚ) - 2 * v)]
      obtain ⟨a₀, ha₀, ha₀le⟩ := exists_small_of_sum hAne hupos hu_def.symm h2A
      have hden' : (0:ℚ) < 2 * c₂ + (n : ℚ) := by nlinarith [hcvpos, hvhalf]
      have hβ : (0:ℚ) < e / (2 * c₂ + (n : ℚ)) := by positivity
      have ha₀D : (a₀ : ℚ) ≤ (m : ℚ) * (2 * c₂ + (n : ℚ)) / e := by
        have h1 : (a₀ : ℚ) ≤ (A.card : ℚ) / u := ha₀le
        have h2 : (A.card : ℚ) / u ≤ (A.card : ℚ) / (e / (2 * c₂ + (n : ℚ))) :=
          div_le_div_of_nonneg_left (by positivity) hβ hub
        have h3 : (A.card : ℚ) / (e / (2 * c₂ + (n : ℚ)))
            = (m : ℚ) * (2 * c₂ + (n : ℚ)) / e := by
          rw [hcA, div_div_eq_mul_div]
        linarith
      have ha₀NB : a₀ ∈ Finset.Iic NB := by
        rw [Finset.mem_Iic, hNB]
        exact Nat.le_floor ha₀D
      -- assemble the membership
      rw [hL, if_pos hm]
      refine Set.mem_biUnion (Finset.mem_coe.mpr ha₀NB) ?_
      refine ⟨(A.erase a₀, B), ⟨?_, h2B, ?_, hcB, ?_⟩, ?_⟩
      · intro a ha; exact h2A a (Finset.mem_of_mem_erase ha)
      · rw [Finset.card_erase_of_mem ha₀, hcA]
      · have hsplit : (a₀ : ℚ)⁻¹ + ∑ a ∈ A.erase a₀, ((a : ℚ))⁻¹ = u := by
          rw [hu_def]; exact Finset.add_sum_erase A (fun x => ((x : ℚ))⁻¹) ha₀
        have : c₁ + ((a₀ : ℚ))⁻¹ + ∑ a ∈ A.erase a₀, ((a : ℚ))⁻¹ = c₁ + u := by
          linarith [hsplit]
        rw [this]
        exact heq
      · simp [Finset.insert_erase ha₀]
    · -- case A: the B side contains a bounded element
      right
      have hcase' : e / 2 ≤ c₁ * v := by linarith [hkey]
      have hc₁v : 0 < c₁ * v := lt_of_lt_of_le (by linarith) hcase'
      have hc₁pos : 0 < c₁ := by
        rcases lt_or_eq_of_le hc₁ with h | h
        · exact h
        · exfalso; rw [← h] at hc₁v; simp at hc₁v
      have hvpos : 0 < v := by
        rcases lt_or_eq_of_le hv0 with h | h
        · exact h
        · exfalso; rw [← h] at hc₁v; simp at hc₁v
      have hBne : B.Nonempty := by
        by_contra hB
        rw [Finset.not_nonempty_iff_eq_empty] at hB
        rw [hv_def, hB] at hvpos; simp at hvpos
      have hn : 1 ≤ n := by
        rw [← hcB]; exact Finset.card_pos.mpr hBne
      have hvb : e / (2 * c₁) ≤ v := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hcase']
      obtain ⟨b₀, hb₀, hb₀le⟩ := exists_small_of_sum hBne hvpos hv_def.symm h2B
      have hb₀D : (b₀ : ℚ) ≤ 2 * c₁ * (n : ℚ) / e := by
        have h1 : (b₀ : ℚ) ≤ (B.card : ℚ) / v := hb₀le
        have h2 : (B.card : ℚ) / v ≤ (B.card : ℚ) / (e / (2 * c₁)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hvb
        have h3 : (B.card : ℚ) / (e / (2 * c₁)) = 2 * c₁ * (n : ℚ) / e := by
          rw [hcB, div_div_eq_mul_div]
          ring
        linarith
      have hb₀NA : b₀ ∈ Finset.Iic NA := by
        rw [Finset.mem_Iic, hNA]
        exact Nat.le_floor hb₀D
      rw [hR, if_pos hn]
      refine Set.mem_biUnion (Finset.mem_coe.mpr hb₀NA) ?_
      refine ⟨(A, B.erase b₀), ⟨h2A, ?_, hcA, ?_, ?_⟩, ?_⟩
      · intro b hb; exact h2B b (Finset.mem_of_mem_erase hb)
      · rw [Finset.card_erase_of_mem hb₀, hcB]
      · have hsplit : (b₀ : ℚ)⁻¹ + ∑ b ∈ B.erase b₀, ((b : ℚ))⁻¹ = v := by
          rw [hv_def]; exact Finset.add_sum_erase B (fun x => ((x : ℚ))⁻¹) hb₀
        have : c₂ + ((b₀ : ℚ))⁻¹ + ∑ b ∈ B.erase b₀, ((b : ℚ))⁻¹ = c₂ + v := by
          linarith [hsplit]
        rw [this]
        exact heq
      · simp [Finset.insert_erase hb₀]

/-- **Every level of #307 is finite.** For each pair of cardinalities there are only finitely many
pairs of prime sets with reciprocal-sum product `1`. The supports at every level above `59` are
infinite (`prop:levelbarrier`), but the solutions are not. -/
theorem erdos307_level_finite (m n : ℕ) :
    {PQ : Finset ℕ × Finset ℕ | (∀ p ∈ PQ.1, p.Prime) ∧ (∀ q ∈ PQ.2, q.Prime) ∧
      PQ.1.card = m ∧ PQ.2.card = n ∧
      (∑ p ∈ PQ.1, ((p : ℚ))⁻¹) * (∑ q ∈ PQ.2, ((q : ℚ))⁻¹) = 1}.Finite := by
  refine Set.Finite.subset (sols_finite (m + n) m n rfl 0 0 le_rfl le_rfl) ?_
  rintro ⟨P, Q⟩ ⟨h1, h2, h3, h4, h5⟩
  exact ⟨fun p hp => (h1 p hp).two_le, fun q hq => (h2 q hq).two_le, h3, h4, by
    simpa using h5⟩

/-! ### The largest element is explicitly bounded at every level

`sols_finite` is effective but crude: its height bound compounds doubly exponentially, because the
generic induction uses only the sizes of the two sides. At a support the square conditions are
available too, and they bound the largest element by an explicit function of the others. The two
regimes are separated by whether the remaining elements already carry mass `2`.
-/

/-- **The mass regime.** If the support minus its largest element carries mass below `2`, the
largest element is pinned by the deficit alone: it must supply what is missing. At the base of the
first `58` primes this gives `q ≤ 793.67…`, recovering the bound `795` that `Sixty.lean` proves by a
separate route. -/
theorem max_le_of_mass_deficit {σ q : ℚ} (hq : 0 < q) (hσ : σ < 2) (hmass : 2 ≤ σ + 1 / q) :
    q ≤ 1 / (2 - σ) := by
  have hd : 0 < 2 - σ := by linarith
  have h1 : 2 - σ ≤ 1 / q := by linarith
  rw [le_div_iff₀ hd]
  rw [le_div_iff₀ hq] at h1
  linarith

/-- The mass regime in the arithmetic form used at a support: `D` the product of the other
elements, `N` their cofactor sum, so `σ = N/D`. -/
theorem max_le_of_mass_deficit' {D N q : ℚ} (hD : 0 < D) (hq : 0 < q)
    (hσ : N < 2 * D) (hmass : 2 ≤ N / D + 1 / q) :
    q ≤ D / (2 * D - N) := by
  have h := max_le_of_mass_deficit hq (by rw [div_lt_iff₀ hD]; linarith) hmass
  have hd : 0 < 2 - N / D := by rw [sub_pos, div_lt_iff₀ hD]; linarith
  refine h.trans (le_of_eq ?_)
  field_simp

end Erdos307

