import Erdos307.CompleteSums
import Mathlib.Tactic

/-!
# Regime (2) of `prop:pairlocal` without Weil

The pair-sector argument needs, for odd `ℓ ∤ 2D`, one pair of units `α, β` making both targets
`A αβ + D(α+β)` and `B αβ + D(α+β)` nonzero squares. The paper reached this by rewriting the pair of
conditions as a single quartic and citing Hasse-Weil for its point count. That is more than the
statement needs: only *existence* is wanted, and counting the pairs `(α, β)` directly gives a double
character sum whose inner sums are the two complete evaluations of `CompleteSums.lean`.

Writing `χ` for the quadratic character and summing over `α, β ≠ 0`,

  `4 · #{both nonzero squares} ≥ (ℓ-1)² + S_f + S_g + S_fg - 8(ℓ-1)`,

with `S_f = ∑ χ(f)`, `S_g = ∑ χ(g)`, `S_fg = ∑ χ(fg)`. For fixed `α` each target is *linear* in `β`,
so `S_f` and `S_g` collapse by `sum_quadraticChar_affine`; and `f·g` is a *product of two linear
forms* in `β`, so the inner sum of `S_fg` is `sum_quadraticChar_quadratic`, whose side condition
`ad ≠ bc` is here exactly `4D²α² ≠ 0`. All three sums are therefore `O(ℓ)`, and the count is positive
from `ℓ ≥ 17` onwards -- far below the `ℓ ≥ 107` the proposition uses.

This file proves the two steps that carried the citation: the inner-sum evaluation, and the
arithmetic that turns the `O(ℓ)` bounds into a positive count.

Paper: Proposition `prop:pairlocal`, regime (2).
-/

namespace Erdos307

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The inner sum of `S_fg`.** For fixed `α ≠ 0`, the product of the two targets is a product of
two linear forms in `β`, and the side condition of `sum_quadraticChar_quadratic` is `4D²α² ≠ 0`,
which holds since the characteristic is odd. So the inner sum is `-χ((Aα+D)(Bα+D))`, of modulus at
most `1`, where Weil was previously invoked. -/
theorem pairlocal_inner_sum (hF : ringChar F ≠ 2) {A B D α : F}
    (hD : D ≠ 0) (hα : α ≠ 0) (hAB : A - B = 4 * D)
    (ha : A * α + D ≠ 0) (hc : B * α + D ≠ 0) :
    ∑ β : F, quadraticChar F (((A * α + D) * β + D * α) * ((B * α + D) * β + D * α))
      = -quadraticChar F ((A * α + D) * (B * α + D)) := by
  refine sum_quadraticChar_quadratic hF ha hc ?_
  intro h
  -- `ad - bc = D α (A - B) α = 4 D² α²`, so the hypothesis forces `4 D² α² = 0`
  have h4 : (4 : F) * D ^ 2 * α ^ 2 = 0 := by
    have hsub : (A * α + D) * (D * α) - (D * α) * (B * α + D) = D * α * ((A - B) * α) := by ring
    rw [hAB] at hsub
    have : (A * α + D) * (D * α) - (D * α) * (B * α + D) = 0 := by rw [h]; ring
    rw [this] at hsub
    linear_combination -hsub
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4ne : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  exact (mul_ne_zero (mul_ne_zero h4ne (pow_ne_zero 2 hD)) (pow_ne_zero 2 hα)) h4

/-- **The count is positive from `ℓ ≥ 17`.** Given the `O(ℓ)` bounds on the three character sums,
the inclusion-exclusion count of pairs making both targets nonzero squares is positive. The
proposition applies this at `ℓ ≥ 107`. -/
theorem pairlocal_count_pos {l : ℤ} {Sf Sg Sfg : ℤ} (hl : 17 ≤ l)
    (hf : |Sf| ≤ 2 * l) (hg : |Sg| ≤ 2 * l) (hfg : |Sfg| ≤ 3 * l) :
    0 < (l - 1) ^ 2 + Sf + Sg + Sfg - 8 * (l - 1) := by
  have h1 : -(2 * l) ≤ Sf := neg_le_of_abs_le hf
  have h2 : -(2 * l) ≤ Sg := neg_le_of_abs_le hg
  have h3 : -(3 * l) ≤ Sfg := neg_le_of_abs_le hfg
  nlinarith [hl, h1, h2, h3]

end Erdos307
