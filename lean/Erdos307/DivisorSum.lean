import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# Divisor-sum upper bounds, elementarily

`prop:plusthin` (atom A6) reduces the semiprime plus-layer count to `∑_{s ≤ Y} τ(2s² + 1)` in
`PlusThin.lean`, and then cites Dirichlet's asymptotics

  `∑_{u ≤ Z} τ(u) ∼ Z log Z`,   `∑_{u ≤ Z} τ(u)/u ∼ ½(log Z)²`

to reach `O(√X (log X)²)`. Mathlib has neither, and A6 has carried that as its recorded blocker.

**The asymptotics are not what a thinness statement needs.** A density-zero conclusion consumes only
the *upper* halves, and those are elementary double counting with no analysis in them at all. Both
are proved here, stated with the harmonic sum `H_Z = ∑_{d ≤ Z} 1/d` in place of `log Z`, which
removes the last analytic ingredient:

  `∑_{u ≤ Z} τ(u)/u ≤ H_Z²`     (`sum_tau_div_le_harmonic_sq`)

which is the half carrying the `(log Z)²` that `prop:plusthin` needs.

The proof of each is the same one line of counting: `τ(u)` is the number of pairs `(d, m)` with
`dm = u`, so summing over `u ≤ Z` is summing over pairs with `dm ≤ Z`, and that set of pairs sits
inside the full square `[1,Z] × [1,Z]`, where the sum factors.

`H_Z ≤ 1 + log Z` recovers the usual shape when wanted, but nothing here needs it, and keeping the
statements harmonic is what makes them formal rather than cited.

What this does **not** do: the asymptotic `∼` remains unavailable, so any step of `prop:plusthin`
needing a matching lower bound, or the exact constant `½`, is still cited. A6 keeps its star; what
changes is that its blocker is now the *lower* bounds and the constant, not the divisor sums as a
whole.

Paper: Proposition `prop:plusthin`, Proposition `prop:plus`.
-/

namespace Erdos307

open Finset

/-- The pairs `(d, m)` with `dm = u`, for `u` ranging over `[1, Z]`, all sit inside the square
`[1, Z] × [1, Z]`: each coordinate divides `u ≤ Z` and is at least `1`. -/
theorem divisorsAntidiagonal_subset_square {Z u : ℕ} (hu : u ∈ Icc 1 Z) :
    u.divisorsAntidiagonal ⊆ Icc 1 Z ×ˢ Icc 1 Z := by
  intro p hp
  rw [Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨hmul, hne⟩ := hp
  rw [mem_Icc] at hu
  have h1 : 1 ≤ p.1 := by
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h, zero_mul] at hmul; omega
    · exact h
  have h2 : 1 ≤ p.2 := by
    rcases Nat.eq_zero_or_pos p.2 with h | h
    · rw [h, mul_zero] at hmul; omega
    · exact h
  refine mem_product.mpr ⟨mem_Icc.mpr ⟨h1, ?_⟩, mem_Icc.mpr ⟨h2, ?_⟩⟩
  · calc p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right _ h2
      _ = u := hmul
      _ ≤ Z := hu.2
  · calc p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left _ h1
      _ = u := hmul
      _ ≤ Z := hu.2

/-- The antidiagonals of distinct `u` are disjoint: a pair determines its product. -/
theorem divisorsAntidiagonal_pairwiseDisjoint (Z : ℕ) :
    ((Icc 1 Z : Finset ℕ) : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
  intro a _ b _ hab
  simp only [Function.onFun, disjoint_left]
  intro p hpa hpb
  rw [Nat.mem_divisorsAntidiagonal] at hpa hpb
  exact hab (hpa.1 ▸ hpb.1 ▸ rfl)

/-- `τ(u)/u` is the antidiagonal sum of `1/(dm)`: on the antidiagonal `dm = u`, so every term is
`1/u` and there are `τ(u)` of them. -/
theorem tau_div_eq_antidiagonal_sum {u : ℕ} (hu : u ≠ 0) :
    (u.divisors.card : ℚ) / u = ∑ p ∈ u.divisorsAntidiagonal, (1 : ℚ) / (p.1 * p.2) := by
  rw [Nat.sum_divisorsAntidiagonal (fun d m => (1 : ℚ) / (d * m))]
  rw [Finset.sum_congr rfl (fun d hd => ?_), Finset.sum_const, nsmul_eq_mul]
  · rw [div_eq_mul_inv, mul_comm]
  · have hd' : (d : ℚ) * ((u / d : ℕ) : ℚ) = (u : ℚ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    rw [hd', one_div]

/-- **The reciprocal-weighted bound.** `∑_{u ≤ Z} τ(u)/u ≤ H_Z²`, where `H_Z = ∑_{d ≤ Z} 1/d`.

This is the upper half of Dirichlet's `∑_{u≤Z} τ(u)/u ∼ ½(log Z)²`, and it is what a density-zero
conclusion actually consumes. Pure counting: the pairs `(d,m)` with `dm ≤ Z` inject into the square
`[1,Z] × [1,Z]`, on which the sum factors as a product of harmonic sums. -/
theorem sum_tau_div_le_harmonic_sq (Z : ℕ) :
    ∑ u ∈ Icc 1 Z, (u.divisors.card : ℚ) / u ≤ (∑ d ∈ Icc 1 Z, (1 : ℚ) / d) ^ 2 := by
  have hterm : ∀ u ∈ Icc 1 Z, (u.divisors.card : ℚ) / u
      = ∑ p ∈ u.divisorsAntidiagonal, (1 : ℚ) / (p.1 * p.2) := by
    intro u hu
    rw [mem_Icc] at hu
    exact tau_div_eq_antidiagonal_sum (by omega)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_biUnion (divisorsAntidiagonal_pairwiseDisjoint Z)]
  have hsub : (Icc 1 Z).biUnion Nat.divisorsAntidiagonal ⊆ Icc 1 Z ×ˢ Icc 1 Z := by
    intro p hp
    obtain ⟨u, hu, hpu⟩ := Finset.mem_biUnion.mp hp
    exact divisorsAntidiagonal_subset_square hu hpu
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (le_of_eq ?_)
  · intro p _ _
    positivity
  · rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl ?_
    intro p _
    exact (one_div_mul_one_div _ _).symm

end Erdos307
