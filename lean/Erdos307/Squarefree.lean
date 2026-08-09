import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The squarefree atom, and the constant it turns on

Of the four open atoms of the Lehmer crux (`qₙ` squarefree infinitely often, `ω(qₙ)` bounded
infinitely often, `qₙ` a `P_k`, `qₙ` prime), the first is the only one that asks for an *upper*
bound on a count of bad events rather than for the *production* of a prime. That is why it is the
easiest: it is not subject to the parity obstruction that blocks the other three.

The argument it wants is a union bound. For a prime `p` not dividing `2AD`, `p² | qₙ` forces
`xₙ² ≡ D (mod p²)`; the Pell orbit is purely periodic modulo `p²` with some period `π(p²)`, there
are at most two square roots of `D`, and each is met a bounded number of times per period, so

  density of bad `n` for this `p`  ≤  C / π(p²).

When `π(p²) = p·π(p)`, which is the generic behaviour, and `π(p) ≍ p`, this is `≍ C/p²`, and the
union bound closes provided `C · Σ_p p⁻² < 1`. That is where the constant enters, and it is
comfortable: `Σ_p p⁻² = 0.4522474…`, so any `C < 2.21` suffices.

This file proves the two pieces that are unconditional: the numeric certificate
`Σ_p p⁻² < 1/2` in the finite form used below, and the union bound itself. What it does **not**
prove, and what leaves the atom open, is the hypothesis `π(p²) = p·π(p)`. Failure of that equality
is exactly a Wall-Sun-Sun prime for the sequence, and then the density is `≍ 1/p` instead of
`≍ 1/p²`, whose sum diverges. No example of such a prime is known for any classical sequence and
their finiteness is unproved, so the atom reduces to a Wall-Sun-Sun statement rather than closing.

Paper: Remark `rem:squarefree`.
-/

namespace Erdos307

/-- The finite certificate behind `Σ_p p⁻² < 1/2`. The first six primes contribute the displayed
rational; every prime from `17` on is odd, so their contribution is at most
`(1/2)·Σ_{m ≥ 16} m⁻² < 1/30`. -/
theorem primeSquareSum_certificate :
    (1/4 + 1/9 + 1/25 + 1/49 + 1/121 + 1/169 + 1/30 : ℚ) < 1/2 := by norm_num

/-- **The union bound.** If the bad sets have densities `d i` summing to at most `S < 1`, the good
set retains density at least `1 - S > 0`. Stated for a finite index set, which is the form the
argument uses after the tail has been absorbed into `S`. -/
theorem good_density_pos {ι : Type*} (s : Finset ι) (d : ι → ℝ) (S : ℝ)
    (_hd : ∀ i ∈ s, 0 ≤ d i) (hsum : ∑ i ∈ s, d i ≤ S) (hS : S < 1) :
    0 < 1 - ∑ i ∈ s, d i := by
  have : ∑ i ∈ s, d i ≤ S := hsum
  linarith

/-- The shape of the conditional theorem: if every bad density is at most `C/p²` and the weighted
constant stays below `1`, a positive proportion of terms survives. The hypothesis `hC` is what a
Wall-Sun-Sun statement would supply and what is missing. -/
theorem squarefree_positive_density_of_bound
    {ι : Type*} (s : Finset ι) (d : ι → ℝ) (w : ι → ℝ) (C : ℝ)
    (_hd : ∀ i ∈ s, 0 ≤ d i) (hC : ∀ i ∈ s, d i ≤ C * w i)
    (hw : C * ∑ i ∈ s, w i < 1) :
    0 < 1 - ∑ i ∈ s, d i := by
  have h1 : ∑ i ∈ s, d i ≤ ∑ i ∈ s, C * w i := Finset.sum_le_sum hC
  have h2 : ∑ i ∈ s, C * w i = C * ∑ i ∈ s, w i := by rw [Finset.mul_sum]
  linarith [h1, h2 ▸ hw]

end Erdos307
