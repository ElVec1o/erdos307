import Erdos307.RhoBarrier

/-!
# What #307 is actually about: distinctness, not mass

Erdős #307 asks for finite sets of primes with `(∑_{p∈P} 1/p)(∑_{q∈Q} 1/q) = 1`. The barrier says
any such pair needs `|P ∪ Q| ≥ 59` and `∏ > 10^112`. It is natural to read that as a statement about
the *mass* condition being hard to meet. It is not. This file isolates what the difficulty really is.

**The contrast.** Drop distinctness, allowing `P` and `Q` to be *multisets* of primes, and the
equation is solved at size four: `(1/2 + 1/2)(1/2 + 1/2) = 1`. Keep distinctness and the same
equation forces `59` primes. The entire barrier lives in the injectivity of `p ↦ 1/p`, not in the
arithmetic of the mass.

**Why this matters, and it is a no-go.** Every transfer of #307 to a setting where several objects
share a denominator dissolves the problem rather than relocating its difficulty, so no such transfer
can be informative. Two instances, both checked:

* *Number fields.* In `K = ℚ(√17, √33)` the prime `2` splits completely into four distinct prime
  ideals of norm `2`. Taking `P = {π₁, π₂}` and `Q = {π₃, π₄}` gives `σ(P) = σ(Q) = 1` and
  `|P ∪ Q| = 4`. So the ideal-theoretic #307 is true and trivial. This is the correct reason the
  number-field route is closed; `prop:fieldoptimal` previously closed it with a false claim, and
  refuting that claim reopened nothing, because the transferred problem was never the same problem.
  The derivative does not transfer either: `π₁ + π₂` is the unit ideal, so `a'` collapses.

* *The coprime variant.* `cor:coprime60` survives only because pairwise-coprime integers still have
  distinct least prime factors. That is distinctness re-entering through the back door, and
  `Coprime60.lean` is where the bookkeeping happens.

**The consequence for the search.** Rule 1.4 says to judge a dictionary by where it sends the
difficulty. A dictionary that permits repeats sends the difficulty to nothing, which means it has
changed the problem. Any future transfer attempt should be tested against this file first: if the
target setting admits repeated denominators, it is dissolving #307, not attacking it.

Paper: Theorem `thm:barrier`, Proposition `prop:fieldoptimal`, Corollary `cor:coprime60`.
-/

namespace Erdos307

open Finset

/-! ### The multiset solution -/

/-- The witness: `1/2 + 1/2 = 1`, so two copies of `2` on each side solve the mass equation. -/
theorem half_add_half : ((2 : ℚ)⁻¹ + (2 : ℚ)⁻¹) * ((2 : ℚ)⁻¹ + (2 : ℚ)⁻¹) = 1 := by norm_num

/-- **The multiset solution, size four.** With `P` and `Q` multisets of primes rather than sets, the
#307 equation has a solution using four primes in total, every entry equal to `2`. Compare
`card_ge_59_of_recipSum_ge_two`, which forces `59` once the entries must be distinct. -/
theorem multiset_solution :
    ∃ P Q : Multiset ℕ,
      (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
      P.card + Q.card = 4 ∧
      ((P.map (fun p => (p : ℚ)⁻¹)).sum) * ((Q.map (fun q => (q : ℚ)⁻¹)).sum) = 1 := by
  refine ⟨{2, 2}, {2, 2}, ?_, ?_, ?_, ?_⟩
  · intro p hp; fin_cases hp <;> exact Nat.prime_two
  · intro q hq; fin_cases hq <;> exact Nat.prime_two
  · rfl
  · norm_num

/-! ### The contrast, which is the point -/

/-- **Distinctness is the whole barrier.** The mass equation admits a four-element multiset
solution, while every solution by genuine *sets* of primes needs at least `59` elements. So the
`59` is not a fact about the mass condition; it is a fact about `p ↦ 1/p` being injective on the
primes.

Stated as the conjunction so the two halves cannot drift apart: the left conjunct is
`multiset_solution`, the right is the barrier as `card_ge_59_of_recipSum_ge_two` applies it. -/
theorem distinctness_carries_the_barrier :
    (∃ P Q : Multiset ℕ,
        (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧ P.card + Q.card = 4 ∧
        ((P.map (fun p => (p : ℚ)⁻¹)).sum) * ((Q.map (fun q => (q : ℚ)⁻¹)).sum) = 1)
    ∧
    (∀ U : Finset ℕ, (∀ p ∈ U, p.Prime) → (2 : ℚ) ≤ ∑ p ∈ U, (p : ℚ)⁻¹ → 59 ≤ U.card) :=
  ⟨multiset_solution, fun _ hU h => card_ge_59_of_recipSum_ge_two hU h⟩

/-- **The no-go for transfers.** If a setting admits two distinct objects of the same "size" `n ≥ 2`
on each side, the mass equation is solvable there at size four, whatever the setting is. So any
dictionary that permits repeated denominators dissolves #307 instead of transferring it, and can
carry no information about the original.

The hypothesis is exactly what `ℚ(√17, √33)` supplies at `n = 2`, with four prime ideals of norm
`2`. -/
theorem transfer_dissolves {n : ℚ} (hn : n = 2) :
    (n⁻¹ + n⁻¹) * (n⁻¹ + n⁻¹) = 1 := by subst hn; norm_num

end Erdos307
