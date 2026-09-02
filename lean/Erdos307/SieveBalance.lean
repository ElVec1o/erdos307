import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Why the exponent in `cor:a9rate` is `1/4`

`cor:a9rate` bounds the count of squarefree `m ≤ N` with `m' ∓ 2m` a square by
`N (log log N)^{1/2+δ} (log N)^{-1/4}`. The analytic inputs are `lem:swdirect` and Halász, and they
remain the blocker recorded in `COVERAGE.md`. The *exponent*, however, comes from neither: it comes
from choosing the sieve parameter `P` to balance two of the five terms, and that choice is an
elementary optimisation, formalised here.

After dividing by `Π²`, the diagonal term is of order `log P / P ≍ (log log N)/P` and the character
term of order `P (log N)^{-1/2}`. The first decreases in `P`, the second increases, so the best `P`
is where they meet. Writing `a = (log N)^{1/4}` and `b = (log log N)^{1/2}` — so that
`(log N)^{1/2} = a²` and `log log N = b²` — the two terms are `b²/P` and `P/a²`, and everything
below is elementary algebra in `a, b, P`. At `P = a·b`, which is
`(log N)^{1/4} (log log N)^{1/2}`, both equal `b/a = (log log N)^{1/2} (log N)^{-1/4}`: the bound of
the theorem.

* `sieve_terms_equal_iff` — the two terms agree exactly when `P² = a²b²`, i.e. `P = ab`.
* `sieve_balance` — at `P = ab` both terms equal `b/a`, the stated rate.
* `sieve_optimal` — and no `P` does better: for every `P > 0` the larger of the two terms is at
  least `b/a`. So the exponent `1/4` is not an artefact of the proof but the true optimum of this
  sieve, and `cor:a9rate` cannot be improved by retuning `P` alone.

The `δ` of the theorem absorbs the difference between `log P` and `log log N`, which is a
`log log log N` and is not modelled here.

Paper: Theorem `cor:a9rate` (the *five terms* paragraph), Proposition `prop:condrate`.
-/

namespace Erdos307

/-- The diagonal term `b²/P` and the character term `P/a²` agree exactly at `P² = (ab)²`. -/
theorem sieve_terms_equal_iff {a b P : ℝ} (ha : 0 < a) (hP : 0 < P) :
    b ^ 2 / P = P / a ^ 2 ↔ P ^ 2 = (a * b) ^ 2 := by
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  constructor
  · intro h
    have := (div_eq_div_iff (ne_of_gt hP) (ne_of_gt ha2)).mp h
    nlinarith [this]
  · intro h
    rw [div_eq_div_iff (ne_of_gt hP) (ne_of_gt ha2)]
    nlinarith [h]

/-- **The balance point.** At `P = ab`, both terms equal `b/a`: with `a = (log N)^{1/4}` and
`b = (log log N)^{1/2}` this is `(log log N)^{1/2} (log N)^{-1/4}`, the rate of `cor:a9rate`. -/
theorem sieve_balance {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b ^ 2 / (a * b) = b / a ∧ (a * b) / a ^ 2 = b / a := by
  constructor
  · field_simp
  · field_simp

/-- **The balance is optimal.** For every `P > 0` the larger of the two terms is at least `b/a`, so
no other sieve parameter improves the exponent. The proof is AM–GM: the product of the two terms is
`b²/a²`, independent of `P`, so the maximum is at least their geometric mean `b/a`. -/
theorem sieve_optimal {a b P : ℝ} (ha : 0 < a) (hb : 0 < b) (hP : 0 < P) :
    b / a ≤ max (b ^ 2 / P) (P / a ^ 2) := by
  by_contra hcon
  push_neg at hcon
  have h1 : b ^ 2 / P < b / a := lt_of_le_of_lt (le_max_left _ _) hcon
  have h2 : P / a ^ 2 < b / a := lt_of_le_of_lt (le_max_right _ _) hcon
  rw [div_lt_div_iff₀ hP ha] at h1
  rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < a ^ 2) ha] at h2
  nlinarith [h1, h2, ha, hb, hP]

end Erdos307
