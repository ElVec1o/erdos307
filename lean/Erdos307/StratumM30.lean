import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The `M = 30` stratum of `prop:oneprime`, and why one side of it is empty

The near-miss construction of `code/nearmiss_below.gp` always produces `a' = 2·3·5·P` with `P` prime.
That family is not ad hoc: it is exactly the stratum `M = 30` of `prop:oneprime`. With `M' = 31` the
equation `MN - M'N' = M²` reads `30N - 31N' = 900`, and the proposition's `N = M + M'p`, `N' = Mp`
become `a = 31P + 30` and `a' = 30P`.

Three consequences, all elementary, and the third is the one that matters:

* `deriv_thirty_mul_prime` : `a'' = 31P + 30`. This is Leibniz at `30`, using `30' = 31` and
  `P' = 1`, so `r = a''/a = (31P + 30)/a`.
* `stratum_linear` : a two-cycle in this stratum is exactly `30a - 31a' = 900`, and conversely.
* `stratum_sigma_lt` : every solution of the stratum has `σ(a) = 30P/(31P + 30) < 30/31`,
  **strictly**, with the defect `900/(31a)`.

The third rules out a whole search direction. Approaches to `r = 1` from *above*, meaning
`σ(a) > 30/31`, cannot converge on a solution of this stratum, however close they get. Two records
obtained that way, `|r-1| = 6.2787e-9` and `3.7617e-9`, are therefore records for the spectrum of `r`
and nothing more. The from-below record `1.654663e-13` lies on the side that solutions must occupy.

What none of this shows is progress toward a solution. `|r-1|` is a ratio; the stratum needs the
integer identity `30a - 31a' = 900`. For the from-below witness that integer has `112` digits, against
`114` for its predecessor: three orders of magnitude in the ratio bought two digits in the integer.

Paper: Proposition `prop:oneprime`, Proposition `prop:nearmiss`, Theorem `thm:lyapfalse`.
-/

namespace Erdos307

/-- **Leibniz at `30`.** With `30' = 31` and `P' = 1` for a prime `P` not dividing `30`, the
derivative of `30P` is `31P + 30`. Applied to `a' = 30P` this gives `a'' = 31P + 30`, hence
`r = a''/a = (31P + 30)/a`. -/
theorem deriv_thirty_mul_prime (P d30 dP : ℤ) (h30 : d30 = 31) (hP : dP = 1) :
    d30 * P + 30 * dP = 31 * P + 30 := by
  subst h30; subst hP; ring

/-- **The stratum's cycle condition is linear.** In the `M = 30` stratum, `a = 31P + 30` and
`a' = 30P`, so a two-cycle is exactly `30a - 31a' = 900`. -/
theorem stratum_linear (a ap P : ℤ) (ha : a = 31 * P + 30) (hap : ap = 30 * P) :
    30 * a - 31 * ap = 900 := by
  subst ha; subst hap; ring

/-- The converse: `30a - 31a' = 900` together with `a' = 30P` forces `a = 31P + 30`. So the linear
equation characterises the stratum rather than merely following from it. -/
theorem stratum_linear_conv (a ap P : ℤ) (hap : ap = 30 * P) (h : 30 * a - 31 * ap = 900) :
    a = 31 * P + 30 := by
  subst hap; linarith

/-- **One side of the stratum is empty.** Every solution has `σ(a) = 30P/(31P + 30)`, and for
positive `P` that is strictly below `30/31`.

So a near-miss with `σ(a) > 30/31` is on a side no solution of this stratum occupies, no matter how
small `|r - 1|` becomes. -/
theorem stratum_sigma_lt (P : ℚ) (hP : 0 < P) :
    30 * P / (31 * P + 30) < 30 / 31 := by
  have hden : (0 : ℚ) < 31 * P + 30 := by linarith
  rw [div_lt_div_iff₀ hden (by norm_num : (0:ℚ) < 31)]
  linarith

/-- The defect is exactly `900/(31a)`: `σ(a) = 30/31 - 900/(31a)` with `a = 31P + 30`. This is what
the from-below ladder aims at, and it shows the target deficit shrinks like `1/a`. -/
theorem stratum_sigma_defect (P : ℚ) (hP : 0 < P) :
    30 * P / (31 * P + 30) = 30 / 31 - 900 / (31 * (31 * P + 30)) := by
  have hden : (31 * P + 30) ≠ 0 := by positivity
  field_simp
  ring

/-- **The two halves together**, stated as a conjunction so they cannot drift apart: the cycle
condition is the linear equation, and every solution of it sits strictly below `30/31`. -/
theorem stratum_M30 (P : ℚ) (hP : 0 < P) :
    (30 * (31 * P + 30) - 31 * (30 * P) = 900)
    ∧ (30 * P / (31 * P + 30) < 30 / 31) :=
  ⟨by ring, stratum_sigma_lt P hP⟩

end Erdos307
