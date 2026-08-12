import Erdos307.Capstone
import Erdos307.Extremal
import Erdos307.Numeral

/-!
# Erdős #307 — the closed barrier (no extremality hypothesis)

Assembles the proven extremality (`Extremal`) and the numeral bridge (`Numeral`) into the
hypothesis-free `erdos307_barrier_closed`: any two finite sets of primes `P, Q` with
`(∑ 1/p)(∑ 1/q) = 1` satisfy `(∏ p∈P) ≥ 2·10⁵⁶`.

Note the constant. The paper's `thm:barrier` states the sharp `2.09·10⁵⁶`; what is machine-checked
here is the rounded `2·10⁵⁶`, which is what the explicit rational core `barrier_numeric` carries.
The sharp value is a paper result, not a Lean one.

Since v1.4.6 the numeral bridge is kernel-checked by `decide`, so these results do **not** inherit
`Lean.ofReduceBool`: `card_ge_59` and `erdos307_barrier_closed` are on the three standard axioms.
The project's only `native_decide` site is `dfs_run` in `Sixty.lean`.

Paper: Lemma `lem:59`, Theorem `thm:barrier` in closed form.
-/

namespace Erdos307

open Finset

/-- **The smallest-prime ratio bound, for every `k ≥ 59`** (target `hmono`).
`(4·10¹¹²)·∑_{i<k} 1/pᵢ ≤ ∏_{i<k} pᵢ`, by induction from `base_case` (k=59). -/
lemma hmono_all : ∀ k, 59 ≤ k →
    (4 * 10 ^ 112 : ℚ) * (∑ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℚ)⁻¹)
      ≤ ∏ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℚ) := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 59 with hn | hn
    · have h59 : n + 1 = 59 := by omega
      rw [h59]; exact base_case
    · have ihn := ih hn
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      set S := ∑ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℚ)⁻¹ with hSdef
      set Pr := ∏ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℚ) with hPrdef
      set p := (Nat.nth Nat.Prime n : ℚ) with hpdef
      have hp_ge : (281 : ℚ) ≤ p := by
        rw [hpdef]
        have hm : Nat.nth Nat.Prime 59 ≤ Nat.nth Nat.Prime n :=
          Nat.nth_monotone Nat.infinite_setOf_prime hn
        rw [np59] at hm
        exact_mod_cast hm
      have hpos : (0 : ℚ) < p := by linarith
      have hP59pos : (0 : ℚ) ≤ (P59 : ℚ) := by positivity
      have hPr_ge : (P59 : ℚ) ≤ Pr := by
        rw [hPrdef]
        have hsub59 : Finset.range 59 ⊆ Finset.range n := by
          intro x hx; rw [Finset.mem_range] at hx ⊢; omega
        have hnat : ∏ i ∈ Finset.range 59, Nat.nth Nat.Prime i
                  ≤ ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i := by
          apply Finset.prod_le_prod_of_subset_of_one_le' hsub59
          intro i _ _; exact (Nat.prime_nth_prime i).one_lt.le
        calc (P59 : ℚ) = ((∏ i ∈ Finset.range 59, Nat.nth Nat.Prime i : ℕ) : ℚ) := by
              rw [prod_first59_nat]
          _ ≤ ((∏ i ∈ Finset.range n, Nat.nth Nat.Prime i : ℕ) : ℚ) := by exact_mod_cast hnat
          _ = ∏ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℚ) := by push_cast; ring
      have hstep : (4 * 10 ^ 112 : ℚ) * p⁻¹ ≤ Pr * (p - 1) := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpos]
        have e1 : (P59 : ℚ) * 280 ≤ Pr * (p - 1) :=
          mul_le_mul hPr_ge (by linarith) (by norm_num) (le_trans hP59pos hPr_ge)
        have e2 : (P59 : ℚ) * 280 * 281 ≤ Pr * (p - 1) * p :=
          mul_le_mul e1 hp_ge (by norm_num) (le_trans (by positivity) e1)
        have hnum2 : (4 * 10 ^ 112 : ℚ) ≤ (P59 : ℚ) * 280 * 281 := by unfold P59; norm_num
        linarith [e2, hnum2]
      have hPrp : Pr * p = Pr + Pr * (p - 1) := by ring
      have hdist : (4 * 10 ^ 112 : ℚ) * (S + p⁻¹)
          = (4 * 10 ^ 112 : ℚ) * S + (4 * 10 ^ 112 : ℚ) * p⁻¹ := by ring
      linarith [ihn, hstep, hPrp, hdist]

/-- AM–GM: if `s·t = 1` with `s > 0` then `s + t ≥ 2`. -/
lemma recip_sum_ge_two {s t : ℚ} (hs : 0 < s) (hst : s * t = 1) : 2 ≤ s + t := by
  nlinarith [sq_nonneg (s - 1), hst, hs]

/-- **B3.**  Any prime-set solution has `|P ∪ Q| ≥ 59`. -/
lemma card_ge_59 {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) :
    59 ≤ (P ∪ Q).card := by
  have hUprime : ∀ r ∈ P ∪ Q, r.Prime := by
    intro r hr; rcases Finset.mem_union.mp hr with h | h
    · exact hP r h
    · exact hQ r h
  have heq' : (csum P : ℚ) / (dprod P : ℚ) * ((csum Q : ℚ) / (dprod Q : ℚ)) = 1 := by
    rw [← recipSum_eq P hP, ← recipSum_eq Q hQ]; exact heq
  obtain ⟨_, hNQDP⟩ := solution_structure (rigidity_coprime P hP) (rigidity_coprime Q hQ)
    (by exact_mod_cast (dprod_pos hP).ne') (by exact_mod_cast (dprod_pos hQ).ne') heq'
  have hdisj : Disjoint P Q := solution_disjoint hP hQ hNQDP
  have hs0 : (∑ p ∈ P, (p : ℚ)⁻¹) ≠ 0 := by
    intro h; rw [h, zero_mul] at heq; norm_num at heq
  have hs_pos : 0 < ∑ p ∈ P, (p : ℚ)⁻¹ :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun p hp => by positivity)) (Ne.symm hs0)
  have hT_ge : (2 : ℚ) ≤ ∑ r ∈ P ∪ Q, (r : ℚ)⁻¹ := by
    rw [Finset.sum_union hdisj]; exact recip_sum_ge_two hs_pos heq
  by_contra hlt
  rw [not_le] at hlt
  have hc58 : (P ∪ Q).card ≤ 58 := by omega
  have hsub58 : Finset.range (P ∪ Q).card ⊆ Finset.range 58 := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have h1 : (∑ r ∈ P ∪ Q, (r : ℚ)⁻¹)
      ≤ ∑ i ∈ Finset.range (P ∪ Q).card, (Nat.nth Nat.Prime i : ℚ)⁻¹ :=
    recipSum_le_first_primes hUprime
  have h2 : ∑ i ∈ Finset.range (P ∪ Q).card, (Nat.nth Nat.Prime i : ℚ)⁻¹
      ≤ ∑ i ∈ Finset.range 58, (Nat.nth Nat.Prime i : ℚ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub58
    intro i _ _; positivity
  have hP58pos : (0 : ℚ) < (P58 : ℚ) := by unfold P58; norm_num
  have h3 : ∑ i ∈ Finset.range 58, (Nat.nth Nat.Prime i : ℚ)⁻¹ < 2 := by
    rw [sum_first58, div_lt_iff₀ hP58pos]
    exact_mod_cast recipSum58_lt_two
  linarith [hT_ge, h1, h2, h3]

/-- **Erdős #307 barrier — closed form (no extremality hypothesis).**
For finite sets of primes `P, Q` with `Q` nonempty and `(∑ 1/p)(∑ 1/q) = 1`,
`(∏_{p∈P} p)² ≥ 4·10¹¹²`, i.e. `D_P ≥ 2·10⁵⁶`. -/
theorem erdos307_barrier_closed {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hQne : Q.Nonempty)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) :
    (4 * 10 ^ 112 : ℚ) ≤ (dprod P : ℚ) ^ 2 := by
  refine erdos307_barrier hP hQ hQne heq ?_
  have hUprime : ∀ r ∈ P ∪ Q, r.Prime := by
    intro r hr; rcases Finset.mem_union.mp hr with h | h
    · exact hP r h
    · exact hQ r h
  have hmono := hmono_all (P ∪ Q).card (card_ge_59 hP hQ heq)
  have hr := hRatio_of_extremal hUprime hmono
  rw [dprod]
  exact hr

end Erdos307
