import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The coprime variant inherits the closed level

`cor:coprime60`. Weaken \#307 so that the elements of `P` and `Q` are merely pairwise coprime
integers `≥ 2` rather than primes (the open form, `1 ∉ P ∪ Q`). Any solution still has
`|P ∪ Q| ≥ 60`.

The reduction is bookkeeping on least prime factors, not a computation. Rigidity holds verbatim for
pairwise-coprime families, since the cofactor-sum argument uses only coprimality, so again
`T(U) = s + t > 2`. The least prime factors `ℓ(e)` are distinct, and `∑ 1/e ≤ ∑ 1/ℓ(e)`. If some
element `e` is not prime then `e ≥ ℓ(e)²`, and the loss `1/ℓ - 1/e` is bounded below by
`(ℓ-1)/ℓ²`, which exceeds the slack available at `|U| = 59`. So every element is prime and
`prop:close59` applies unchanged.

This file proves the two inequalities that carry the argument:

* `coprime_loss`: `e ≥ ℓ²` gives `1/ℓ - 1/e ≥ (ℓ-1)/ℓ²`. One line, since `1/e ≤ 1/ℓ²`.
* `loss_antitone`: `(x-1)/x²` is decreasing for `x ≥ 2`, so a bound at the largest admissible `ℓ`
  bounds all smaller ones. This is what turns a per-element estimate into the single number
  `276/277² = 0.00359…` the corollary compares against the slack.

What is not here is the slack computation itself, which is the level-59 census.

Paper: Corollary `cor:coprime60`, Proposition `prop:close59`.
-/

namespace Erdos307

/-- **The loss from a composite element.** If `e ≥ ℓ²` then replacing `1/ℓ` by `1/e` costs at least
`(ℓ-1)/ℓ²`. -/
theorem coprime_loss {l e : ℚ} (hl : 2 ≤ l) (he : l ^ 2 ≤ e) :
    (l - 1) / l ^ 2 ≤ 1 / l - 1 / e := by
  have hl0 : (0 : ℚ) < l := by linarith
  have hlne : l ≠ 0 := hl0.ne'
  have hl2 : (0 : ℚ) < l ^ 2 := by positivity
  have h1 : 1 / e ≤ 1 / l ^ 2 := one_div_le_one_div_of_le hl2 he
  have h2 : (l - 1) / l ^ 2 = 1 / l - 1 / l ^ 2 := by field_simp
  rw [h2]; linarith

/-- **The bound is worst at the largest least-prime-factor.** `(x-1)/x²` is antitone on `[2, ∞)`, so
checking it at the top of the admissible range bounds every element at once. -/
theorem loss_antitone {x y : ℚ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    (y - 1) / y ^ 2 ≤ (x - 1) / x ^ 2 := by
  have hx0 : (0 : ℚ) < x := by linarith
  have hy0 : (0 : ℚ) < y := by linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hyne : y ≠ 0 := hy0.ne'
  rw [← sub_nonneg]
  have key : (x - 1) / x ^ 2 - (y - 1) / y ^ 2
      = ((y - x) * (x * y - x - y)) / (x ^ 2 * y ^ 2) := by field_simp; ring
  rw [key]
  refine div_nonneg ?_ (by positivity)
  have h1 : (0 : ℚ) ≤ y - x := by linarith
  have h2 : (0 : ℚ) ≤ x * y - x - y := by nlinarith
  exact mul_nonneg h1 h2

/-- The numeric consequence the corollary uses: at `ℓ ≤ 277` the loss is at least `276/277²`. -/
theorem loss_at_277 {l : ℚ} (hl : 2 ≤ l) (hu : l ≤ 277) :
    (276 : ℚ) / 277 ^ 2 ≤ (l - 1) / l ^ 2 := by
  have h := loss_antitone hl hu
  norm_num at h ⊢
  linarith

end Erdos307
