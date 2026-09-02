import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The tail-prime quadratic and why its maximum sits at `α = 1`

`prop:tailbound` bounds the Pythagorean tail prime. Most of it is formalised in `TailBound.lean`
(the factorisation, the quadratic, the discriminant in both `m` and `α` forms, and the bounds
`q ≤ 4N` and `q ≤ N`). One step was not: that the root is decreasing in `α`, which is what licenses
taking the maximum at `α = 1`. Given a base `S` of primes with `D = ∏ S`,
`N = ∑ D/p`, a tail prime `q` making `Aq + D` and `Bq + D` both squares forces, for a divisor
`α ∣ D` with `β = D/α`,
`α²q² − Nq + (β² − D) = 0`, hence `q = (N + √(N² − 4D² + 4α²D)) / (2α²)`,
and the paper then takes the maximum over `α` by observing that this is decreasing in `α`. That
last step is the whole content of the bound, and it is elementary; it is formalised here. The
enumeration of divisors `α ∣ D` is not, and is not the point: the bound holds for each `α`
separately and the maximum is at `α = 1`.

The discriminant identity itself is already formalised, over `ℤ`, as
`Erdos307.tail_discriminant_alpha` in `TailBound.lean`; what was missing there is the monotonicity
that turns it into a bound, and only that is added here.

* `tail_root_antitone` — with `u = α²`, the root `(N + √(N² − 4D² + 4uD))/(2u)` is antitone in `u`
  for `u ≥ 1`, given `N ≥ 2D > 0`. The hypothesis `N ≥ 2D` is exactly `σ(S) ≥ 2`, which is where the
  proposition is applied; it is not decoration, since it is what makes `N² − 4D²` nonnegative and
  hence the numerator's growth slower than the denominator's.
* `tail_max_at_one` — the resulting bound: every admissible `α ≥ 1` gives a root at most the `α = 1`
  value `(N + √(N² − 4D² + 4D))/2`.

Paper: Proposition `prop:tailbound`.
-/

namespace Erdos307

/-- **The root is antitone in `α²`.** For `N ≥ 2D > 0` and `1 ≤ u ≤ v`, the larger root at `v` does
not exceed the larger root at `u`. Hence enlarging `α` can only decrease the bound. -/
theorem tail_root_antitone {N D u v : ℝ} (hD : 0 < D) (hN : 2 * D ≤ N)
    (hu : 1 ≤ u) (huv : u ≤ v) :
    (N + Real.sqrt (N ^ 2 - 4 * D ^ 2 + 4 * v * D)) / (2 * v)
      ≤ (N + Real.sqrt (N ^ 2 - 4 * D ^ 2 + 4 * u * D)) / (2 * u) := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le hupos huv
  set C := N ^ 2 - 4 * D ^ 2 with hC
  have hCnn : 0 ≤ C := by rw [hC]; nlinarith [hD, hN]
  have hv0 : 0 ≤ C + 4 * v * D := by positivity
  have hu0 : 0 ≤ C + 4 * u * D := by positivity
  -- the key inequality: u * √(C + 4vD) ≤ v * √(C + 4uD)
  have hkey : u * Real.sqrt (C + 4 * v * D) ≤ v * Real.sqrt (C + 4 * u * D) := by
    have hsq : (u * Real.sqrt (C + 4 * v * D)) ^ 2 ≤ (v * Real.sqrt (C + 4 * u * D)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hv0, Real.sq_sqrt hu0]
      nlinarith [mul_nonneg (sub_nonneg.mpr huv) hCnn, hD.le, hupos.le, hvpos.le,
                 mul_nonneg (mul_nonneg hupos.le hvpos.le) hD.le, sub_nonneg.mpr huv]
    have h1 : 0 ≤ u * Real.sqrt (C + 4 * v * D) := by positivity
    have h2 : 0 ≤ v * Real.sqrt (C + 4 * u * D) := by positivity
    nlinarith [hsq, h1, h2]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, huv, hupos, hvpos, Real.sqrt_nonneg (C + 4 * v * D)]

/-- **The maximum is at `α = 1`.** Every `u ≥ 1` gives a root at most the `u = 1` value. -/
theorem tail_max_at_one {N D u : ℝ} (hD : 0 < D) (hN : 2 * D ≤ N) (hu : 1 ≤ u) :
    (N + Real.sqrt (N ^ 2 - 4 * D ^ 2 + 4 * u * D)) / (2 * u)
      ≤ (N + Real.sqrt (N ^ 2 - 4 * D ^ 2 + 4 * D)) / 2 := by
  have h := tail_root_antitone hD hN le_rfl hu
  simpa using h

end Erdos307
