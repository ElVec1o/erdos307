import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The live-slot threshold

`prop:liveslot`. In the decoupled family of `rem:decouple`, a Pythagorean pair over a squarefree base
`N₀` gives a representation of `4N₀²` by the binary form

  `Q(s,d) = A s² + B d²`,  `A = N₀(2 - σ)`,  `B = N₀(2 + σ)`,  `σ = σ(N₀)`,

and the recovered slot is `r = (s² - N₀)/B`. The slot `r = 1` is the ghost; a *live* slot needs
`r ≥ 2`. This file proves that a live slot forces `σ ≥ 3/2`.

The argument is two inequalities meeting at a quadratic. From `r ≥ 2`,
`s² ≥ N₀ + 2B = N₀(5 + 2σ)`; from positive definiteness, `A s² ≤ 4N₀²`. Both hold only if
`(2 - σ)(5 + 2σ) ≤ 4`, that is `2σ² + σ - 6 ≥ 0`, and

  `2σ² + σ - 6 = (2σ - 3)(σ + 2)`,

so with `σ + 2 > 0` the threshold `σ ≥ 3/2` is forced. The constant is exact, not fitted.

The arithmetic half, that `σ ≥ 3/2` forces `ω(N₀) ≥ 10` and `N₀ ≥ Π₁₀ = 6469693230`, rests on the
mass estimate `σ(Π₉) < 3/2 ≤ σ(Π₁₀)`, whose two numerals are checked here; the passage from a mass
bound to a prime count is the same step as `Erdos307.card_ge_59_of_recipSum_ge_two` and is cited
rather than repeated.

Nothing here decides \#307. It fixes the range in which the decoupled family can have a live slot,
and in particular shows the census recorded in `prop:form`, which ran to `N₀ ≤ 5·10⁴`, lay below the
threshold by a factor `1.3·10⁵` and could not have met one.

Paper: Proposition `prop:liveslot`.
-/

namespace Erdos307

/-- **`prop:liveslot`, the analytic core.** If the positive-definite form `A s² + B d²` with
`A = N₀(2-σ)` and `B = N₀(2+σ)` represents `4N₀²`, and the slot is live in the sense
`s² ≥ N₀ + 2B`, then `σ ≥ 3/2`. -/
theorem live_slot_threshold {N0 σ s d : ℝ}
    (hN : 0 < N0) (hσ0 : 0 < σ) (hσ2 : σ < 2)
    (hform : N0 * (2 - σ) * s ^ 2 + N0 * (2 + σ) * d ^ 2 = 4 * N0 ^ 2)
    (hlive : N0 + 2 * (N0 * (2 + σ)) ≤ s ^ 2) :
    3 / 2 ≤ σ := by
  -- the `d` term is nonnegative, so the `s` term alone is at most the target
  have hd : 0 ≤ N0 * (2 + σ) * d ^ 2 := by positivity
  have hAs : N0 * (2 - σ) * s ^ 2 ≤ 4 * N0 ^ 2 := by linarith
  -- and the live-slot bound pushes `s²` up
  have hA : 0 < N0 * (2 - σ) := by nlinarith
  have hkey : N0 * (2 - σ) * (N0 * (5 + 2 * σ)) ≤ 4 * N0 ^ 2 := by
    have : N0 * (2 - σ) * (N0 * (5 + 2 * σ)) ≤ N0 * (2 - σ) * s ^ 2 := by
      have h5 : N0 * (5 + 2 * σ) ≤ s ^ 2 := by linarith
      exact mul_le_mul_of_nonneg_left h5 (le_of_lt hA)
    linarith
  -- divide by N0², which is where the base drops out
  have hring : N0 * (2 - σ) * (N0 * (5 + 2 * σ)) = N0 ^ 2 * ((2 - σ) * (5 + 2 * σ)) := by ring
  rw [hring] at hkey
  have hN2 : (0:ℝ) < N0 ^ 2 := by positivity
  have hstep : N0 ^ 2 * ((2 - σ) * (5 + 2 * σ)) ≤ N0 ^ 2 * 4 := by linarith
  have hdiv : (2 - σ) * (5 + 2 * σ) ≤ 4 := le_of_mul_le_mul_left hstep hN2
  -- factor: 4 - (2-σ)(5+2σ) = (2σ - 3)(σ + 2), and σ + 2 > 0
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_pos (show (0:ℝ) < 3 / 2 - σ by linarith) (show (0:ℝ) < σ + 2 by linarith)]

/-- `σ(Π₉) < 3/2`: nine primes do not reach the threshold. -/
theorem recipSum9_lt_three_halves :
    (1/2 + 1/3 + 1/5 + 1/7 + 1/11 + 1/13 + 1/17 + 1/19 + 1/23 : ℚ) < 3/2 := by norm_num

/-- `3/2 ≤ σ(Π₁₀)`: ten do. Together with the previous lemma and the fact that the `k` smallest
primes maximise the reciprocal sum among `k`-element prime sets, a live slot forces `ω(N₀) ≥ 10`
and `N₀ ≥ Π₁₀ = 6469693230`. -/
theorem three_halves_le_recipSum10 :
    (3/2 : ℚ) ≤ 1/2 + 1/3 + 1/5 + 1/7 + 1/11 + 1/13 + 1/17 + 1/19 + 1/23 + 1/29 := by norm_num

/-- The two numerals bracket the threshold, which is what makes `Π₁₀` the entry point. -/
theorem threshold_bracket :
    (1/2 + 1/3 + 1/5 + 1/7 + 1/11 + 1/13 + 1/17 + 1/19 + 1/23 : ℚ) < 3/2 ∧
    (3/2 : ℚ) ≤ 1/2 + 1/3 + 1/5 + 1/7 + 1/11 + 1/13 + 1/17 + 1/19 + 1/23 + 1/29 :=
  ⟨recipSum9_lt_three_halves, three_halves_le_recipSum10⟩

end Erdos307
