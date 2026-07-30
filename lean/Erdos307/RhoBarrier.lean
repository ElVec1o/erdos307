import Erdos307.Closed

/-!
# The mass ratio is below one, up to the barrier

`thm:rhobarrier`. The Lyapunov criterion of Section~\ref{sec:lyap} needs
`ρ = sup{σ(n')/σ(n) : σ(n) > 1}` to be less than `1`. That is provable, and by the barrier's own
mechanism rather than by any new input: if `σ(n') ≥ σ(n) > 1` then the two masses sum to more than
`2`, and since `n` and `n'` are coprime and squarefree their union of prime factors carries that
combined mass. A set of primes of mass `≥ 2` has at least `59` elements, because the first `58`
primes fall short.

The content is therefore the counting statement below; the passage to `n · n' ≥ Π₅₉` is the same
step as in `Erdos307.Barrier`.

Paper: Theorem `thm:rhobarrier`.
-/

namespace Erdos307

open Finset

/-- A set of primes whose reciprocals sum to at least `2` has at least `59` elements. This is the
mass estimate underlying the barrier, isolated. -/
theorem card_ge_59_of_recipSum_ge_two {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime)
    (h : (2 : ℚ) ≤ ∑ p ∈ U, (p : ℚ)⁻¹) : 59 ≤ U.card := by
  by_contra hlt
  push_neg at hlt
  have hsub58 : Finset.range U.card ⊆ Finset.range 58 := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have h1 : (∑ p ∈ U, (p : ℚ)⁻¹) ≤ ∑ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ)⁻¹ :=
    recipSum_le_first_primes hU
  have h2 : ∑ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ)⁻¹
      ≤ ∑ i ∈ Finset.range 58, (Nat.nth Nat.Prime i : ℚ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub58
    intro i _ _; positivity
  have hP58pos : (0 : ℚ) < (P58 : ℚ) := by unfold P58; norm_num
  have h3 : ∑ i ∈ Finset.range 58, (Nat.nth Nat.Prime i : ℚ)⁻¹ < 2 := by
    rw [sum_first58, div_lt_iff₀ hP58pos]
    exact_mod_cast recipSum58_lt_two
  linarith

/-- **`ρ < 1` in counting form.** If two disjoint sets of primes both carry mass exceeding `1`,
their union has at least `59` elements. Applied to the prime supports of `n` and `n'`, which are
disjoint by `Theorem thm:structure`, this is the statement that `σ(n') ≥ σ(n) > 1` forces
`n · n'` past the barrier. -/
theorem card_union_ge_59_of_masses {S T : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) (hd : Disjoint S T)
    (h1 : (1 : ℚ) < ∑ p ∈ S, (p : ℚ)⁻¹) (h2 : (1 : ℚ) < ∑ p ∈ T, (p : ℚ)⁻¹) :
    59 ≤ (S ∪ T).card := by
  apply card_ge_59_of_recipSum_ge_two (U := S ∪ T)
  · intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact hT p h
  · rw [Finset.sum_union hd]
    linarith

end Erdos307
