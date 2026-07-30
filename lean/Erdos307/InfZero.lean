import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The near-miss infimum is zero

`prop:infzero`. Over finite disjoint prime sets `P, Q`,
`inf |σ(P)σ(Q) - 1| = 0`, and \#307 asks exactly whether the infimum is attained.

The paper proves this by the classical subseries theorem, which produces infinite `P, Q` with
`σ(P) = σ(Q) = 1` exactly and then truncates. For the *infimum* that is more than is needed: it
suffices to get each mass into `(1-δ, 1)`, and that follows from a greedy block argument requiring
only that the terms tend to `0` and the tail sums are unbounded. `exists_block_sum_near` is that
argument, and `infimum_zero` assembles the two blocks.

As in `Erdos307.HalfLyap` and `Erdos307.NoInvariant`, the arithmetic input is cited rather than
reproved: that the primes split into two infinite classes each of which has reciprocal terms tending
to `0` and unbounded partial sums. (Both classes diverge because `p` is monotone in its index, so
convergence of one class would force convergence of the other and hence of `∑ 1/p`.) Everything
downstream of that input is proved here.

Nothing here decides \#307. What it shows is that closeness is cheap, so no near-miss, however
good, is evidence that the infimum is attained.

Paper: Proposition `prop:infzero`.
-/

namespace Erdos307

open Finset

/-- **Greedy block lemma.** If the terms `a i` are positive, are all below `ε` from index `N` on,
and have unbounded partial sums from `N`, then some consecutive block `[N, M)` has sum strictly
inside `(T - ε, T)`. Taking the first block to exceed `T - ε`, it overshoots by less than one term,
hence by less than `ε`. Positivity of the terms is carried for readability but is not used: the
argument needs only minimality of the first exceeding index and the bound on the last term. -/
theorem exists_block_sum_near {a : ℕ → ℝ} {N : ℕ} {ε T : ℝ}
    (_hpos : ∀ i, 0 < a i) (hsmall : ∀ i, N ≤ i → a i < ε)
    (hdiv : ∀ B : ℝ, ∃ M, B < ∑ i ∈ Finset.Ico N M, a i) (hεT : ε < T) :
    ∃ M, T - ε < ∑ i ∈ Finset.Ico N M, a i ∧ ∑ i ∈ Finset.Ico N M, a i < T := by
  classical
  have hex : ∃ M, T - ε < ∑ i ∈ Finset.Ico N M, a i := hdiv (T - ε)
  have hspec := Nat.find_spec hex
  -- blocks ending at or before N are empty, so the first exceeding index is past N
  have hNlt : N < Nat.find hex := by
    by_contra hcon
    have hle : Nat.find hex ≤ N := not_lt.mp hcon
    rw [Finset.Ico_eq_empty_of_le hle, Finset.sum_empty] at hspec
    linarith
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hNk : N ≤ k := by omega
  -- minimality: the previous block did not exceed T - ε
  have hprev : ∑ i ∈ Finset.Ico N k, a i ≤ T - ε := not_lt.mp (Nat.find_min hex (by omega))
  rw [hk] at hspec
  refine ⟨k + 1, hspec, ?_⟩
  rw [Finset.sum_Ico_succ_top hNk]
  have hak : a k < ε := hsmall k hNk
  linarith

/-- **`prop:infzero`.** Two such sequences, one for each side, give finite blocks whose masses are
each within `δ` of `1` from below, hence a product within `ε` of `1`. Since `ε` is arbitrary the
infimum of `|σ(P)σ(Q) - 1|` over finite sets is `0`. -/
theorem infimum_zero {a b : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hapos : ∀ i, 0 < a i) (hbpos : ∀ i, 0 < b i)
    (hasmall : ∀ δ : ℝ, 0 < δ → ∃ N, ∀ i, N ≤ i → a i < δ)
    (hbsmall : ∀ δ : ℝ, 0 < δ → ∃ N, ∀ i, N ≤ i → b i < δ)
    (hadiv : ∀ (N : ℕ) (B : ℝ), ∃ M, B < ∑ i ∈ Finset.Ico N M, a i)
    (hbdiv : ∀ (N : ℕ) (B : ℝ), ∃ M, B < ∑ i ∈ Finset.Ico N M, b i) :
    ∃ (P Q : Finset ℕ),
      |(∑ i ∈ P, a i) * (∑ i ∈ Q, b i) - 1| < ε := by
  -- work with δ = min (ε/3) (1/2), so that δ < 1 and 2δ < ε
  set δ : ℝ := min (ε / 3) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  obtain ⟨Na, hNa⟩ := hasmall δ hδpos
  obtain ⟨Nb, hNb⟩ := hbsmall δ hδpos
  obtain ⟨Ma, ha1, ha2⟩ :=
    exists_block_sum_near (T := 1) hapos hNa (hadiv Na) (by linarith)
  obtain ⟨Mb, hb1, hb2⟩ :=
    exists_block_sum_near (T := 1) hbpos hNb (hbdiv Nb) (by linarith)
  refine ⟨Finset.Ico Na Ma, Finset.Ico Nb Mb, ?_⟩
  set A := ∑ i ∈ Finset.Ico Na Ma, a i
  set B := ∑ i ∈ Finset.Ico Nb Mb, b i
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hpos1 : (0:ℝ) < 1 - δ := by linarith
  have h1 : (1 - δ) * (1 - δ) < A * B := by nlinarith
  have h2 : A * B < 1 := by nlinarith
  rw [abs_lt]
  refine ⟨by nlinarith, by linarith⟩

end Erdos307
