import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The cycle condition does not improve the barrier

`prop:nogain`. A two-cycle satisfies more than the mass inequality: it forces `b = a'` exactly,
that is `b = a·σ(a)`. One may ask whether that extra structure pushes the barrier of `thm:barrier`
up. It does not, and the negative result is the substantive one: it is evidence that `10^112.9` is
the true cost of the mass condition rather than an artefact of the AM-GM route.

The reduction is two lines of algebra and is proved here in full.

* `N = a·b = a·(a σ(a)) = a² σ(a)`, which is `cycle_product`.
* Lower bounds on `a` and on `σ(a)` therefore give a lower bound on `N`, monotonically. That is
  `cycle_bound`, and `le_max_of_both` is the step that lets the two independent constraints
  `a ≥ ∏S` and `a ≥ Π_min(S)/σ(S)` be used together.

What is **not** in Lean is the minimisation over `S`. Fixing the small primes `S` of `a`, the two
constraints give `a ≥ max(∏S, Π_min(S)/σ(S))`, and minimising `max(...)²·σ(S)` over all `S` is a
finite search, carried out in `code/minimise_structured.rs` and `code/full_minimisation.rs`. Its
output is `log₁₀ N ≥ 113.2`, attained at `S = {odd p ≤ 151} \ {3, 97}` with `σ(S) = 1.0495` and
`|Q| ≥ 26`. That number is a computation, not a theorem in this file, and is labelled as such.

Against `thm:barrier`'s `log₁₀ N ≥ 112.9`, the gain is `0.3` of an order of magnitude:
`gain_lt_one_order`. The cycle condition, the strongest structural constraint available beyond the
masses, buys less than a single decimal digit.

The optimum is worth one remark, recorded in `rem:sectorsquared`. It hands `2` to `Q` and keeps the
odd primes to `151` in `S` while dropping two of them, a configuration no initial segment and no
small subset can express; minimising over such restricted families reports `10^222.9`, `10^195.9`,
`10^188.9`, `10^181.7`, each looking like a large improvement of the barrier and none of them being
one. A bound minimised over a family that cannot express the optimum reports the family's best, not
the problem's.

Paper: Proposition `prop:nogain`, Remark `rem:sectorsquared`.
-/

namespace Erdos307

/-- **The cycle identity.** With `b = a·σ(a)` forced by `b = a'`, the product of the two members is
`N = a²·σ(a)`. -/
theorem cycle_product (a s : ℝ) : a * (a * s) = a ^ 2 * s := by ring

/-- Two independent lower bounds on `a` combine into one: this is the `max` in the statement of
`prop:nogain`. -/
theorem le_max_of_both {a x y : ℝ} (hx : x ≤ a) (hy : y ≤ a) : max x y ≤ a := max_le hx hy

/-- **The bound the minimisation feeds.** If `a ≥ A > 0` and `σ(a) ≥ s > 0`, then
`N = a²σ(a) ≥ A²s`. This is the step that converts the two constraints on `a` and the mass bound
into a bound on `N`, and it is the whole of the deductive content of `prop:nogain`; the value of
the resulting minimum is a separate computation. -/
theorem cycle_bound {a A sa s : ℝ} (hA : 0 < A) (hs : 0 < s)
    (ha : A ≤ a) (hsa : s ≤ sa) : A ^ 2 * s ≤ a ^ 2 * sa := by
  have h1 : A ^ 2 ≤ a ^ 2 := by nlinarith
  nlinarith

/-- The same statement in the form used, with `a` bounded below by a maximum of two quantities. -/
theorem cycle_bound_max {a x y sa s : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hxa : x ≤ a) (hya : y ≤ a) (hsa : s ≤ sa) :
    max x y ^ 2 * s ≤ a ^ 2 * sa := by
  refine cycle_bound ?_ hs (le_max_of_both hxa hya) hsa
  exact lt_of_lt_of_le hx (le_max_left x y)

/-- **The gain, quantified.** The cycle condition moves the barrier from `10^112.9` to `10^113.2`,
which is less than one order of magnitude. The two exponents are inputs: `112.9` from
`thm:barrier`, `113.2` from the finite minimisation in `code/minimise_structured.rs`. -/
theorem gain_lt_one_order : (10 : ℝ) ^ ((113.2 : ℝ) - 112.9) < 10 ^ (1 : ℝ) :=
  Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

/-- The barrier is not moved out of reach: `10^113.2` and `10^112.9` differ by a factor below `10`,
so the cycle condition leaves the order of magnitude of the obstruction intact. -/
theorem nogain (N : ℝ) (h : (10 : ℝ) ^ (113.2 : ℝ) ≤ N) : (10 : ℝ) ^ (112.9 : ℝ) ≤ N :=
  le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)) h

end Erdos307
