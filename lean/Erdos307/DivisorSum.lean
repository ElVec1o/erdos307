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
  `∑_{u ≤ Z} τ(u)   ≤ Z · H_Z²`  (`sum_tau_le_mul_harmonic_sq`)

and `prop:plusthin` consumes exactly these two, as `Y·∑τ(u)/u + ∑τ(u)`.

The proof of each is the same one line of counting: `τ(u)` is the number of pairs `(d, m)` with
`dm = u`, so summing over `u ≤ Z` is summing over pairs with `dm ≤ Z`, and that set of pairs sits
inside the full square `[1,Z] × [1,Z]`, where the sum factors.

`H_Z ≤ 1 + log Z` recovers the usual shape when wanted, but nothing here needs it, and keeping the
statements harmonic is what makes them formal rather than cited.

**Why the upper halves suffice.** `prop:plusthin` concludes `O(√X (log X)²)`, an upper bound, and an
upper bound needs only upper bounds on its inputs. Citing the asymptotic `∼` was citing more than the
argument uses. The lower halves and the constant `½` are needed only for a matching *lower* bound,
which `prop:plusthin` does not assert.

What this does **not** do: it does not finish A6. The divisor sums are no longer the blocker, but the
assembly around them is not formalised either, namely the range count
`#{s ≤ Y : u ∣ 2s²+1} ≤ (roots mod u)·(Y/u + 1)`, the bound `roots ≤ 2^ω(u) ≤ τ(u)` by CRT from
`two_roots_quadratic`, and `H_Z ≤ 1 + log Z` if the statement is wanted with logarithms. A6 keeps its
star, with that assembly as the recorded blocker in place of the divisor sums.

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

/-- **The unweighted bound.** `∑_{u ≤ Z} τ(u) ≤ Z · H_Z²`.

Weaker than Dirichlet's `Z log Z` by one harmonic factor, and free: every `u` in range satisfies
`u ≤ Z`, so `τ(u) = (τ(u)/u)·u ≤ Z·(τ(u)/u)`, and `sum_tau_div_le_harmonic_sq` finishes it.

The loss costs nothing where it is used. `prop:plusthin` combines the two sums as
`Y·∑τ(u)/u + ∑τ(u)`, and with `Z ≍ Y` both terms are `O(Y·H²)`, which is the `√X (log X)²` shape it
reports. A sharper `Z·H_Z` would need the per-`d` count `⌊Z/d⌋`, a different argument, and would not
change the stated rate. -/
theorem sum_tau_le_mul_harmonic_sq (Z : ℕ) :
    ∑ u ∈ Icc 1 Z, (u.divisors.card : ℚ) ≤ (Z : ℚ) * (∑ d ∈ Icc 1 Z, (1 : ℚ) / d) ^ 2 := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_tau_div_le_harmonic_sq Z) (by positivity))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro u hu
  rw [mem_Icc] at hu
  have hu0 : (0 : ℚ) < u := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hu.1
  have huZ : (u : ℚ) ≤ Z := by exact_mod_cast hu.2
  rw [mul_div_assoc']
  rw [le_div_iff₀ hu0]
  have hnn : (0 : ℚ) ≤ (u.divisors.card : ℚ) := by positivity
  calc (u.divisors.card : ℚ) * u ≤ (u.divisors.card : ℚ) * Z :=
        mul_le_mul_of_nonneg_left huZ hnn
    _ = (Z : ℚ) * (u.divisors.card : ℚ) := mul_comm _ _

end Erdos307
