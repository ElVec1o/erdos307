import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The half-mass Lyapunov function

`thm:halflyap`. Put `δ(n) = log n + σ(n)/2`. For squarefree `n` with `n'` squarefree, if
`σ(n · n') < 2` then `δ(n') < δ(n)`, so the arithmetic derivative admits no cycle whose consecutive
pairs all lie in that region. Since a two-cycle has `σ(ab) > 2` by AM-GM, this recovers the barrier
of `thm:barrier` by a route using no extremality argument and no enumeration.

The number theory enters only twice, and both facts are already in this development: `n` and `n'`
are coprime (`Erdos307.rigidity_coprime`, so `σ(n n') = σ(n) + σ(n')`), and `n' = n σ(n)`. Once
those are used the statement is the real-analysis inequality below, which is what this file proves.
Isolating it that way keeps the arithmetic and the analysis separately checkable.

Paper: Theorem `thm:halflyap`, Corollary `cor:lyapbarrier`.
-/

namespace Erdos307

open Real

/-- **The inequality behind `thm:halflyap`.** If `s` is positive and `s + t < 2`, then
`log s < (s - t)/2`. Here `s = σ(n)` and `t = σ(n')`, so the hypothesis is `σ(n n') < 2`. -/
theorem log_lt_half_sub {s t : ℝ} (hs : 0 < s) (h : s + t < 2) :
    Real.log s < (s - t) / 2 := by
  have h1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : s - 1 < (s - t) / 2 := by linarith
  linarith

/-- **`thm:halflyap`.** With `δ = log n + σ(n)/2` and `n' = n · σ(n)`, writing `s = σ(n)` and
`t = σ(n')`, the increment `δ(n') - δ(n)` equals `log s + (t - s)/2`, which is negative exactly when
the inequality above holds. The hypothesis `s + t < 2` is `σ(n n') < 2`. -/
theorem delta_decreasing {s t : ℝ} (hs : 0 < s) (h : s + t < 2) :
    Real.log s + (t - s) / 2 < 0 := by
  have := log_lt_half_sub hs h
  linarith

/-- The two-cycle case of `cor:lyapbarrier`: if `s * t = 1` with both positive, then `s + t ≥ 2`,
so a two-cycle can never satisfy the hypothesis of `delta_decreasing`. This is AM-GM, and it is why
the Lyapunov argument stops exactly at the barrier. -/
theorem two_le_add_of_mul_eq_one {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : s * t = 1) :
    2 ≤ s + t := by
  nlinarith [sq_nonneg (s - t), sq_nonneg (s + t - 2)]

end Erdos307
