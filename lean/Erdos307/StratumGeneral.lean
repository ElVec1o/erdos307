import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Every stratum of `prop:oneprime` is one-sided

`StratumM30` shows that solutions of the `M = 30` stratum satisfy `σ(b) < 30/31`, strictly. That
constant is not special to `30`. In the normal form of `prop:oneprime` a solution of the `M`-stratum
is `a = Mp`, `b = N = M + M'p`, so

  `σ(a) = N/(Mp) = σ(M) + 1/p`,   `σ(b) = Mp/N = 1/σ(a)`,

and therefore `σ(b) < 1/σ(M) = M/M'` for **every** squarefree `M`, with `M = 30` giving `30/31`.

This is a corollary of the identity `(σ(M) + 1/p)·σ(N) = 1` already recorded in `prop:oneprime`(b),
not a new theorem; it is stated here because it is the constraint that governs search *direction*,
and it is worth having machine-checked in the form the search actually uses. What it says is that in
no stratum whatsoever can a solution be approached from above: the entire half-space `σ(b) ≥ M/M'`
is empty. The `M = 30` near-miss record that was obtained from above (v1.6.1) was therefore on a
solution-free side, and so is every such record in every other stratum.

The statements are over `ℚ` with `M`, `M'` and `p` as positive rationals: no arithmetic of the
derivative is needed, only that `M > 0`, and specializing recovers `StratumM30.stratum_sigma_lt`.

Paper: Proposition `prop:oneprime`(b), Proposition `prop:nearmiss`.
-/

namespace Erdos307.StratumGeneral

/-- `σ(b) = Mp/(M + M'p) < M/M'` in every stratum. The whole content is `0 < M²`. -/
theorem stratum_sigma_lt_general (M M' p : ℚ) (hM : 0 < M) (hM' : 0 < M') (hp : 0 < p) :
    M * p / (M + M' * p) < M / M' := by
  have hden : (0 : ℚ) < M + M' * p := by positivity
  rw [div_lt_div_iff₀ hden hM']
  nlinarith [mul_pos hM hM]

/-- The reciprocal identity of `prop:oneprime`(b): `(σ(M) + 1/p)·σ(N) = 1`. -/
theorem stratum_sigma_mul (M M' p : ℚ) (hM : 0 < M) (hM' : 0 < M') (hp : 0 < p) :
    (M' / M + 1 / p) * (M * p / (M + M' * p)) = 1 := by
  have hden : (0 : ℚ) ≠ M + M' * p := by positivity
  field_simp
  ring

/-- The exact defect: `M/M' - σ(b) = M²/(M'(M + M'p))`, which is positive and `O(1/p)`. -/
theorem stratum_sigma_defect_general (M M' p : ℚ) (hM : 0 < M) (hM' : 0 < M') (hp : 0 < p) :
    M / M' - M * p / (M + M' * p) = M ^ 2 / (M' * (M + M' * p)) := by
  have hden : (0 : ℚ) ≠ M + M' * p := by positivity
  have hM'0 : (0 : ℚ) ≠ M' := hM'.ne
  field_simp
  ring

/-- Specialization to `M = 30`, `M' = 31`: recovers `StratumM30.stratum_sigma_lt`. -/
theorem stratum_sigma_lt_thirty (p : ℚ) (hp : 0 < p) :
    30 * p / (30 + 31 * p) < 30 / 31 :=
  stratum_sigma_lt_general 30 31 p (by norm_num) (by norm_num) hp

end Erdos307.StratumGeneral
