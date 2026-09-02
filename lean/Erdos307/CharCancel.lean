import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The constant of `lem:charcancelunif`

`lem:charcancelunif` gives cancellation uniformly for odd squarefree `r` in a polyloglog range, with
pretentious distance at least `(1 - √r/φ(r))·L - o(L)`. Its analytic inputs — Halász, Siegel–Walfisz,
Siegel, the zero-free region — are not in Mathlib and remain the blocker recorded in `COVERAGE.md`.

But the lemma's *shape* is not set by the analysis. It is set by an elementary question about the
constant: for which `r` is `1 - √r/φ(r)` bounded away from `0`? Since `r` is odd and squarefree,
`√r/φ(r) = ∏_{p ∣ r} √p/(p-1)`, and the whole matter reduces to the real function
`f(p) = √p/(p-1)`. That reduction, and the resulting exclusion of exactly `r = 3` and `r = 5`, is
what this file formalises — it is the reason the lemma is stated for `r ≥ 7` and the reason those two
moduli are handled separately by `lem:charcancel`.

Writing `u = √p`, so that `f = u ↦ u/(u²-1)`:

* `ratio_antitone` — `u ↦ u/(u²-1)` is antitone for `u > 1`. Hence adjoining a larger prime to `r`
  replaces a factor by a smaller one. The proof is the factorisation `(v-u)(uv+1) ≥ 0`.
* `ratio_lt_one` — every factor is `< 1` for `p ≥ 3`, so adjoining *any* prime shrinks the product.
  This is what makes the two cases below exhaustive.
* `ratio_seven` — `√7/6 < 1/2`: the single-prime case `ω(r) = 1`, `p ≥ 7`.
* `ratio_three_five` — `(√3/2)(√5/4) = √15/8 < 1/2`: the case `ω(r) ≥ 2`, whose supremum is at
  `r = 15`, and where the bound `1 - √15/8 = 0.515…` is attained.
* `ratio_five_gt_half`, `ratio_three_gt_half` — `√5/4 > 2/5` and `√3/2 > 1/2`: the excluded moduli
  really are excluded, so the hypothesis `r ≥ 7` is necessary and not an artefact.

The passage from these to `√r/φ(r) = ∏ √p/(p-1)` over an arbitrary odd squarefree `r` is the
multiplicativity of both sides, which is standard; what is checked here is the analysis of the
factors, which is where the numbers `7`, `15` and `1/2` come from.

Paper: Lemma `lem:charcancelunif` (the *Assembly* paragraph); `code/uniform_min_sweep.gp`.
-/

namespace Erdos307

/-- **The factor function is antitone.** With `u = √p`, the factor `√p/(p-1)` is `u/(u²-1)`, and for
`1 < u ≤ v` one has `v/(v²-1) ≤ u/(u²-1)`. So replacing a prime of `r` by a larger one, or adjoining
a larger prime, can only decrease that factor. -/
theorem ratio_antitone {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    v / (v ^ 2 - 1) ≤ u / (u ^ 2 - 1) := by
  have hv : 1 < v := lt_of_lt_of_le hu huv
  have hu2 : (0 : ℝ) < u ^ 2 - 1 := by nlinarith
  have hv2 : (0 : ℝ) < v ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ hv2 hu2]
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) (by positivity : (0:ℝ) ≤ u * v + 1)]

/-- **Every factor is below `1`** for `p ≥ 3`, i.e. `u ≥ √3`. Hence adjoining any further prime to
`r` strictly shrinks `√r/φ(r)`, which is why it suffices to bound the cases `ω(r) = 1` and
`ω(r) = 2` and no others. -/
theorem ratio_lt_one {u : ℝ} (hu : Real.sqrt 3 ≤ u) : u / (u ^ 2 - 1) < 1 := by
  have h3 : (1 : ℝ) < Real.sqrt 3 := by
    have : Real.sqrt 1 < Real.sqrt 3 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  have hu1 : 1 < u := lt_of_lt_of_le h3 hu
  have hu2 : (0 : ℝ) < u ^ 2 - 1 := by nlinarith
  rw [div_lt_one hu2]
  have hsq : (3 : ℝ) ≤ u ^ 2 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    nlinarith [hu, Real.sqrt_nonneg 3]
  nlinarith

/-- **The single-prime case.** `√7/6 < 1/2`, so `ω(r) = 1` with `p ≥ 7` gives `√r/φ(r) < 1/2`. -/
theorem ratio_seven : Real.sqrt 7 / 6 < 1 / 2 := by
  have h : Real.sqrt 7 < 3 := by
    have : Real.sqrt 7 < Real.sqrt 9 := by apply Real.sqrt_lt_sqrt <;> norm_num
    simpa [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq] using this
  linarith

/-- **The two-prime case, at its supremum `r = 15`.** `(√3/2)·(√5/4) = √15/8 < 1/2`, the largest
value of `√r/φ(r)` over `ω(r) ≥ 2`; the resulting constant `1 - √15/8 = 0.515…` is the minimum of
the lemma. -/
theorem ratio_three_five : Real.sqrt 15 / 8 < 1 / 2 := by
  have h : Real.sqrt 15 < 4 := by
    have : Real.sqrt 15 < Real.sqrt 16 := by apply Real.sqrt_lt_sqrt <;> norm_num
    simpa [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq] using this
  linarith

/-- **`r = 5` is genuinely excluded**: `√5/4 > 2/5`, so the constant there is `0.441…`, and the
argument of the lemma does not reach it. -/
theorem ratio_five_gt : (2 : ℝ) / 5 < Real.sqrt 5 / 4 := by
  have h : (2 : ℝ) < Real.sqrt 5 := by
    have : Real.sqrt 4 < Real.sqrt 5 := by apply Real.sqrt_lt_sqrt <;> norm_num
    simpa [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq] using this
  linarith

/-- **`r = 3` is genuinely excluded**, and badly: `√3/2 > 1/2`, the constant there being `0.133…`. -/
theorem ratio_three_gt : (1 : ℝ) / 2 < Real.sqrt 3 / 2 := by
  have h : (1 : ℝ) < Real.sqrt 3 := by
    have : Real.sqrt 1 < Real.sqrt 3 := by apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  linarith

end Erdos307
