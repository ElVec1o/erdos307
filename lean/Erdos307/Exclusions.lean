import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Two exclusion results for the barrier crux

Improving the barrier past `60` is equivalent to a bound `|σ(a) - 1| > c` with `c` absolute, where
`σ(a) = ∑_{p ∣ a} 1/p = b/a` for a two-cycle `a' = b`, `b' = a` (Proposition `prop:barthreshold`).
Two classes of argument are excluded from producing such a `c`, and both exclusions are elementary.
They are formalised here because they are the standing constraints on any future attempt.

* `lyap_increments_sum`, `lyap_not_both_neg` — `rem:lyapshape`. For a potential
  `F(n) = log n + G(σ(n))` with *any* `G`, one step gives increment `log σ(n) + G(σ(n')) - G(σ(n))`.
  Around a two-cycle the `G`-terms telescope and the two increments sum to `log(σ(a)σ(b)) = 0`, so
  they cannot both be negative. A strictly decreasing `F` of this shape would settle the problem, and
  none can be exhibited without already excluding cycles. Nothing about `G` is used beyond its being
  a function, which is the point: the obstruction is to the shape, not to a choice of `G`.
* `ppn_gap`, `ppn_gap_lt` — `rem:twosided`. A primary pseudoperfect `n` satisfies
  `σ(n) + 1/n = 1`, so `|σ(n) - 1| = 1/n`, which is below any prescribed `c` once `n > 1/c`. Such `n`
  solve the coprime relaxation of the problem, so no argument using only the one-sided equation
  `a' = b` can bound `|σ(a) - 1|` below by an absolute constant: it would prove the relaxed statement
  too, and these `n` refute it.

Paper: Remark `rem:lyapshape`, Remark `rem:twosided`, Proposition `prop:barthreshold`.
-/

namespace Erdos307

/-- **The increments telescope.** For any `G`, the two one-step increments of `F = log n + G(σ(n))`
around a two-cycle sum to `log(s·t)`, which is `0` when `s·t = 1`. -/
theorem lyap_increments_sum (G : ℝ → ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : s * t = 1) :
    (Real.log s + G t - G s) + (Real.log t + G s - G t) = 0 := by
  have : Real.log s + Real.log t = 0 := by
    rw [← Real.log_mul (ne_of_gt hs) (ne_of_gt ht), h, Real.log_one]
  linarith

/-- **Hence no potential of that shape can decrease at both points of a cycle.** -/
theorem lyap_not_both_neg (G : ℝ → ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : s * t = 1) :
    ¬ ((Real.log s + G t - G s < 0) ∧ (Real.log t + G s - G t < 0)) := by
  rintro ⟨h1, h2⟩
  have := lyap_increments_sum G hs ht h
  linarith

/-- **The primary pseudoperfect gap.** `σ(n) + 1/n = 1` forces `|σ(n) - 1| = 1/n`. -/
theorem ppn_gap {s n : ℝ} (hn : 0 < n) (h : s + 1 / n = 1) : |s - 1| = 1 / n := by
  have hs : s - 1 = -(1 / n) := by linarith
  rw [hs, abs_neg, abs_of_pos (by positivity)]

/-- **So the gap falls below any prescribed constant.** For `n > 1/c` with `c > 0`, a solution of
`σ(n) + 1/n = 1` has `|σ(n) - 1| < c`. These are solutions of the coprime relaxation, so no
one-sided argument can bound the gap below by an absolute constant. -/
theorem ppn_gap_lt {s n c : ℝ} (hn : 0 < n) (hc : 0 < c) (hlarge : 1 / c < n)
    (h : s + 1 / n = 1) : |s - 1| < c := by
  rw [ppn_gap hn h]
  rw [div_lt_iff₀ hn]
  rw [div_lt_iff₀ hc] at hlarge
  linarith

end Erdos307
