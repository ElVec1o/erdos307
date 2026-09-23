import Mathlib.Tactic

/-!
# The single-tail criterion is exact: the algebraic core

For a single-tail family `S ∪ {q}` with `a = q α`, `b = β`, `α β = D`, the identity
`α² + α' β' = D` together with `β' = q α` gives back `β = α + q α'`, which is `a' = b` for a prime `q`
(`(q α)' = α + q α'`). And when `2 ∉ T`, `α` and `q` are odd and `α' ≡ |T| (mod 2)`, so `β` is even only
for `|T|` odd.

Paper: Corollary `cor:splitexact`.
-/

namespace Erdos307

/-- The converse direction: the identity and `β' = q α` recover the second cycle equation. -/
theorem split_cycle_of_identity (α β dα dβ D q : ℤ) (hα : α ≠ 0) (hD : α * β = D)
    (hid : α ^ 2 + dα * dβ = D) (hq : dβ = q * α) : β = α + q * dα := by
  have h : α * (β - α - q * dα) = 0 := by linear_combination hD - hid + dα * hq
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hα
  · linarith

/-- The parity step: with `α`, `q` odd and `α' ≡ t (mod 2)`, an even `β = α + q α'` forces `t` odd. -/
theorem split_card_odd (α q dα β t : ℤ) (hα : α % 2 = 1) (hq : q % 2 = 1) (hdα : dα % 2 = t % 2)
    (hβ : β = α + q * dα) (heven : β % 2 = 0) : t % 2 = 1 := by
  have hm : (q * dα) % 2 = dα % 2 := by rw [Int.mul_emod, hq]; simp
  omega

end Erdos307
