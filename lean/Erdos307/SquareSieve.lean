import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# The square sieve, counting skeleton

`thm:a9` and `cor:a9rate` rest on Heath-Brown's square sieve. Its analytic content is the estimation
of the character sums; its *combinatorial* content is elementary and is what this file records.

If `a` is a perfect square coprime to every `p` in a set `P`, then every symbol `(a/p)` equals `1`,
so the inner sum `∑_{p ∈ P} (a/p)` attains its maximum `|P|`. Squaring and summing over all `a`
therefore bounds `|P|²` times the number of squares by a double sum over pairs `(p,q)`, which is
where the character sums enter. Formally the argument is: a subset on which a real-valued function
is constantly `c` contributes `c² · card` to a sum of squares, and sums of squares only grow when
the index set grows.

Paper: Theorem `thm:a9`, Corollary `cor:a9rate`.
-/

namespace Erdos307

open Finset

/-- **Square-sieve core.** If `F` is constantly `c` on `B ⊆ A`, then `c² · |B|` is at most the sum
of `F²` over `A`. Applied with `F a = ∑_{p ∈ P} (a/p)` and `c = |P|`, this is the inequality that
converts "every symbol is `1` at a square" into a bound on the number of squares. -/
theorem sieve_core {ι : Type*} [DecidableEq ι] (A B : Finset ι) (hBA : B ⊆ A)
    (F : ι → ℤ) (c : ℤ) (hB : ∀ i ∈ B, F i = c) :
    c ^ 2 * B.card ≤ ∑ i ∈ A, (F i) ^ 2 := by
  have h1 : ∑ i ∈ B, (F i) ^ 2 = c ^ 2 * B.card := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [hB i hi]), Finset.sum_const,
      nsmul_eq_mul, mul_comm]
  have h2 : ∑ i ∈ B, (F i) ^ 2 ≤ ∑ i ∈ A, (F i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hBA (fun i _ _ => pow_two_nonneg _)
  exact h1 ▸ h2

/-- Expanding the square of the inner sum turns the right-hand side into the double sum over pairs
of moduli, which is where the character-sum input is consumed. -/
theorem sum_sq_expand {ι : Type*} (A : Finset ι) (P : Finset ℕ) (f : ι → ℕ → ℤ) :
    ∑ i ∈ A, (∑ p ∈ P, f i p) ^ 2 = ∑ p ∈ P, ∑ q ∈ P, ∑ i ∈ A, f i p * f i q := by
  simp only [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- **The square sieve.** Combining the two: the number of elements of `B` is bounded by the double
sum over pairs of moduli, divided by `|P|²`. Stated multiplicatively to avoid division. -/
theorem square_sieve {ι : Type*} [DecidableEq ι] (A B : Finset ι) (hBA : B ⊆ A)
    (P : Finset ℕ) (f : ι → ℕ → ℤ) (hB : ∀ i ∈ B, ∑ p ∈ P, f i p = (P.card : ℤ)) :
    (P.card : ℤ) ^ 2 * B.card ≤ ∑ p ∈ P, ∑ q ∈ P, ∑ i ∈ A, f i p * f i q := by
  rw [← sum_sq_expand]
  exact sieve_core A B hBA (fun i => ∑ p ∈ P, f i p) (P.card : ℤ) hB

end Erdos307
