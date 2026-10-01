import Erdos307.Closed
import Erdos307.Sixtyone

/-!
# The product bound at the level-61 barrier

`cor:level61bound`: every solution has `∏ U ≥ Π₆₁ > 6.97·10¹¹⁷` and
`min(∏P, ∏Q) > 5.89·10⁵⁸`, given the level-`60` hypothesis of `erdos307_sixtyone_of_level60`.

Proof, as in `Closed.lean` but with the constant `c = (589·10⁵⁶)²`: the smallest-primes ratio
`c·T_k ≤ Π_k` holds at `k = 61` by the numerals `np0..np60`, and propagates to every `k ≥ 61` since
adjoining a prime `p ≥ 283` multiplies `Π` by `p` and adds `1/p` to `T`. Then
`min² ≥ ∏U / T(U) ≥ c`.

Paper: Corollary `cor:level61bound`.
-/

set_option maxRecDepth 40000

namespace Erdos307

open Finset

lemma np60 : Nat.nth Nat.Prime 60 = 283 := by
  have h : Nat.count Nat.Prime 283 = 60 := by decide
  calc Nat.nth Nat.Prime 60 = Nat.nth Nat.Prime (Nat.count Nat.Prime 283) := by rw [h]
    _ = 283 := Nat.nth_count (by norm_num)

/-- The constant `(589·10⁵⁶)²`. -/
def C61 : ℚ := 589 ^ 2 * 10 ^ 112

lemma prod_first61 : ∏ i ∈ Finset.range 61, (Nat.nth Nat.Prime i : ℚ) = (P59 : ℚ) * 281 * 283 := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, prod_first59, np59, np60]; norm_num

lemma sum_first61 : ∑ i ∈ Finset.range 61, (Nat.nth Nat.Prime i : ℚ)⁻¹ =
    (N59 : ℚ) / (P59 : ℚ) + (281 : ℚ)⁻¹ + (283 : ℚ)⁻¹ := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, sum_first59, np59, np60]; norm_num

lemma base_case61 :
    C61 * (∑ i ∈ Finset.range 61, (Nat.nth Nat.Prime i : ℚ)⁻¹)
      ≤ ∏ i ∈ Finset.range 61, (Nat.nth Nat.Prime i : ℚ) := by
  rw [sum_first61, prod_first61]
  unfold C61 N59 P59
  norm_num

lemma hmono61 : ∀ k, 61 ≤ k →
    C61 * (∑ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℚ)⁻¹)
      ≤ ∏ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℚ) := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 61 with hn | hn
    · have h61 : n + 1 = 61 := by omega
      rw [h61]; exact base_case61
    · have ihn := ih hn
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      set S := ∑ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℚ)⁻¹ with hSdef
      set Pr := ∏ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℚ) with hPrdef
      set p := (Nat.nth Nat.Prime n : ℚ) with hpdef
      have hp_ge : (283 : ℚ) ≤ p := by
        rw [hpdef]
        have hm : Nat.nth Nat.Prime 60 ≤ Nat.nth Nat.Prime n :=
          Nat.nth_monotone Nat.infinite_setOf_prime (by omega)
        rw [np60] at hm
        exact_mod_cast hm
      have hpos : (0 : ℚ) < p := by linarith
      have hPr_ge : (P59 : ℚ) * 281 * 283 ≤ Pr := by
        rw [hPrdef, ← prod_first61]
        have hsub : Finset.range 61 ⊆ Finset.range n := by
          intro x hx; rw [Finset.mem_range] at hx ⊢; omega
        have hnat : ∏ i ∈ Finset.range 61, Nat.nth Nat.Prime i
                  ≤ ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i := by
          apply Finset.prod_le_prod_of_subset_of_one_le' hsub
          intro i _ _; exact (Nat.prime_nth_prime i).one_lt.le
        calc ∏ i ∈ Finset.range 61, (Nat.nth Nat.Prime i : ℚ)
            = ((∏ i ∈ Finset.range 61, Nat.nth Nat.Prime i : ℕ) : ℚ) := by push_cast; ring
          _ ≤ ((∏ i ∈ Finset.range n, Nat.nth Nat.Prime i : ℕ) : ℚ) := by exact_mod_cast hnat
          _ = ∏ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℚ) := by push_cast; ring
      have hQpos : (0 : ℚ) ≤ (P59 : ℚ) * 281 * 283 := by positivity
      have hstep : C61 * p⁻¹ ≤ Pr * (p - 1) := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpos]
        have e1 : ((P59 : ℚ) * 281 * 283) * 282 ≤ Pr * (p - 1) :=
          mul_le_mul hPr_ge (by linarith) (by norm_num) (le_trans hQpos hPr_ge)
        have e2 : ((P59 : ℚ) * 281 * 283) * 282 * 283 ≤ Pr * (p - 1) * p :=
          mul_le_mul e1 hp_ge (by norm_num) (le_trans (by positivity) e1)
        have hnum : C61 ≤ ((P59 : ℚ) * 281 * 283) * 282 * 283 := by unfold C61 P59; norm_num
        linarith [e2, hnum]
      have hPrp : Pr * p = Pr + Pr * (p - 1) := by ring
      have hdist : C61 * (S + p⁻¹) = C61 * S + C61 * p⁻¹ := by ring
      linarith [ihn, hstep, hPrp, hdist]

/-- General-constant form of `hRatio_of_extremal`. -/
lemma ratio_of_extremal {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) {c : ℚ} (hc : 0 ≤ c)
    (hmono : c * (∑ i ∈ Finset.range U.card, ((Nat.nth Nat.Prime i : ℚ))⁻¹)
              ≤ ∏ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ)) :
    c * (∑ p ∈ U, (p : ℚ)⁻¹) ≤ (dprod U : ℚ) := by
  have h1 := recipSum_le_first_primes hU
  have h2 : (∏ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ)) ≤ (dprod U : ℚ) := by
    have hnat := prod_first_primes_le hU
    calc (∏ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ))
        = ((∏ i ∈ Finset.range U.card, Nat.nth Nat.Prime i : ℕ) : ℚ) := by push_cast; ring
      _ ≤ (dprod U : ℚ) := by unfold dprod; exact_mod_cast hnat
  calc c * (∑ p ∈ U, (p : ℚ)⁻¹) ≤ c * (∑ i ∈ Finset.range U.card, ((Nat.nth Nat.Prime i : ℚ))⁻¹) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ ≤ _ := hmono
    _ ≤ _ := h2

/-- The product of a level-`≥61` support is at least `Π₆₁`. -/
theorem dprod_ge_P61 {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) (hc : 61 ≤ U.card) :
    (P59 : ℚ) * 281 * 283 ≤ (dprod U : ℚ) := by
  have hnat := prod_first_primes_le hU
  have hsub : Finset.range 61 ⊆ Finset.range U.card := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have h3 : ∏ i ∈ Finset.range 61, Nat.nth Nat.Prime i
      ≤ ∏ i ∈ Finset.range U.card, Nat.nth Nat.Prime i :=
    Finset.prod_le_prod_of_subset_of_one_le' hsub fun i _ _ => (Nat.prime_nth_prime i).one_lt.le
  have : (∏ i ∈ Finset.range 61, (Nat.nth Nat.Prime i : ℚ)) ≤ (dprod U : ℚ) := by
    calc (∏ i ∈ Finset.range 61, (Nat.nth Nat.Prime i : ℚ))
        = ((∏ i ∈ Finset.range 61, Nat.nth Nat.Prime i : ℕ) : ℚ) := by push_cast; ring
      _ ≤ (dprod U : ℚ) := by unfold dprod; exact_mod_cast h3.trans hnat
  rwa [prod_first61] at this

/-- **The minimal side, from the extremal ratio.** For a solution with `|P ∪ Q| ≥ 61`:
`(589·10⁵⁶)² ≤ (∏P)²`. -/
theorem min_side_sq {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hQne : Q.Nonempty) (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1)
    (hcard : 61 ≤ (P ∪ Q).card) : C61 ≤ (dprod P : ℚ) ^ 2 := by
  have hUprime : ∀ r ∈ P ∪ Q, r.Prime := by
    intro r hr; rcases Finset.mem_union.mp hr with h | h
    · exact hP r h
    · exact hQ r h
  have hdP : (0 : ℚ) < (dprod P : ℚ) := by exact_mod_cast dprod_pos hP
  have hdQ : (0 : ℚ) < (dprod Q : ℚ) := by exact_mod_cast dprod_pos hQ
  have heq' : (csum P : ℚ) / (dprod P : ℚ) * ((csum Q : ℚ) / (dprod Q : ℚ)) = 1 := by
    rw [← recipSum_eq P hP, ← recipSum_eq Q hQ]; exact heq
  obtain ⟨hNPDQ, hNQDP⟩ :=
    solution_structure (rigidity_coprime P hP) (rigidity_coprime Q hQ)
      (by exact_mod_cast hdP.ne') (by exact_mod_cast hdQ.ne') heq'
  have hdisj : Disjoint P Q := solution_disjoint hP hQ hNQDP
  have hRnat : dprod (P ∪ Q) = dprod P * dprod Q := by
    unfold dprod; rw [Finset.prod_union hdisj]
  have hTsplit : (∑ r ∈ P ∪ Q, (r : ℚ)⁻¹)
      = (∑ p ∈ P, (p : ℚ)⁻¹) + (∑ q ∈ Q, (q : ℚ)⁻¹) := Finset.sum_union hdisj
  set s : ℚ := ∑ p ∈ P, (p : ℚ)⁻¹ with hs
  set t : ℚ := ∑ q ∈ Q, (q : ℚ)⁻¹ with ht
  have ht_pos : 0 < t := by
    rw [ht]; refine Finset.sum_pos (fun q hq => ?_) hQne
    exact inv_pos.mpr (by exact_mod_cast (hQ q hq).pos)
  have hs_nonneg : 0 ≤ s := by
    rw [hs]; refine Finset.sum_nonneg (fun p hp => ?_)
    exact inv_nonneg.mpr (by exact_mod_cast (hP p hp).pos.le)
  have hratio := ratio_of_extremal hUprime (by unfold C61; norm_num) (hmono61 _ hcard)
  rw [hTsplit] at hratio
  have hsval : s = (dprod Q : ℚ) / (dprod P : ℚ) := by
    rw [hs, recipSum_eq P hP, hNPDQ]
  have hR : (dprod (P ∪ Q) : ℚ) = s * (dprod P : ℚ) ^ 2 := by
    rw [hRnat, hsval]; push_cast; field_simp
  exact barrier_algebraic (DP := (dprod P : ℚ)) (s := s) (T := s + t) (R := dprod (P ∪ Q))
    (B := C61) (by linarith) (by linarith) (by rw [hR]; ring) hratio


lemma ne_empty_of_eq {P Q : Finset ℕ} (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) :
    Q.Nonempty ∧ P.Nonempty := by
  constructor
  · rw [Finset.nonempty_iff_ne_empty]; rintro rfl
    rw [Finset.sum_empty, mul_zero] at heq; exact absurd heq (by norm_num)
  · rw [Finset.nonempty_iff_ne_empty]; rintro rfl
    rw [Finset.sum_empty, zero_mul] at heq; exact absurd heq (by norm_num)

/-- `Π₆₁ > 6.97·10¹¹⁷`. -/
lemma P61_gt : (6.97 * 10 ^ 117 : ℚ) < (P59 : ℚ) * 281 * 283 := by unfold P59; norm_num

/-- **`cor:level61bound`.** Given the level-`60` hypothesis, every solution has
`∏(P ∪ Q) ≥ Π₆₁ > 6.97·10¹¹⁷` and both `∏P` and `∏Q` at least `589·10⁵⁶ = 5.89·10⁵⁸`. -/
theorem level61_bound
    (hL : ∀ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ q ∈ Q, q.Prime) →
      (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1 → (P ∪ Q).card ≠ 60)
    {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) :
    (6.97 * 10 ^ 117 : ℚ) < (dprod (P ∪ Q) : ℚ) ∧
      (589 * 10 ^ 56 : ℚ) ≤ (dprod P : ℚ) ∧ (589 * 10 ^ 56 : ℚ) ≤ (dprod Q : ℚ) := by
  have hcard := erdos307_sixtyone_of_level60 hL hP hQ heq
  have hUprime : ∀ r ∈ P ∪ Q, r.Prime := by
    intro r hr; rcases Finset.mem_union.mp hr with h | h
    · exact hP r h
    · exact hQ r h
  obtain ⟨hQne, hPne⟩ := ne_empty_of_eq heq
  have heq2 : (∑ q ∈ Q, (q : ℚ)⁻¹) * (∑ p ∈ P, (p : ℚ)⁻¹) = 1 := by rw [mul_comm]; exact heq
  have h1 := min_side_sq hP hQ hQne heq hcard
  have h2 := min_side_sq hQ hP hPne heq2 (by rwa [Finset.union_comm])
  have hC : (589 * 10 ^ 56 : ℚ) ^ 2 = C61 := by unfold C61; norm_num
  have hsq : ∀ d : ℚ, 0 ≤ d → C61 ≤ d ^ 2 → (589 * 10 ^ 56 : ℚ) ≤ d := fun d hd h =>
    by rw [← hC] at h; exact le_of_sq_le_sq h hd
  exact ⟨lt_of_lt_of_le P61_gt (dprod_ge_P61 hUprime hcard),
    hsq _ (by positivity) h1, hsq _ (by positivity) h2⟩

end Erdos307
