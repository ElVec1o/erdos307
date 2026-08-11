import Mathlib.Tactic.Linarith

/-!
# The function-field analogue has no two-cycles

`thm:ff`. Over `𝔽_q[t]` the Leibniz derivative `f' = ∑_i e_i f / P_i` satisfies
`deg f' ≤ deg f - 1` for every nonconstant `f`, because each term `e_i f / P_i` has degree
`deg f - deg P_i ≤ deg f - 1`. A two-cycle `f' = g`, `g' = f` would then force
`deg g ≤ deg f - 1` and `deg f ≤ deg g - 1`, hence `deg f ≤ deg f - 2`. A fixed point is excluded
the same way.

The content is entirely an order argument about the degree, so it is stated here on the degrees
alone, over `ℕ`, with no polynomial API involved. That is the honest shape: the arithmetic input is
the single inequality `deg f' + 1 ≤ deg f`, which `deg_drop_of_terms` records, and everything else
is `omega`.

This is why the algebraic route dies in characteristic `p` while the integer problem stays open: the
derivative there is degree-lowering, and over `ℤ` it is not. `prop:noplace` is the statement that no
place of `ℚ` restores the missing ultrametric inequality, and `prop:fieldoptimal` records what
happens when one tries number rings instead.

Paper: Theorem `thm:ff`, Corollary `cor:ff307`.
-/

namespace Erdos307

/-- **The degree drop.** If every term `e_i f / P_i` has degree at most `deg f - deg P_i` and every
`P_i` is nonconstant, then the derivative drops the degree by at least one. Stated on degrees: a
maximum over terms each at most `d - 1` is at most `d - 1`. -/
theorem deg_drop_of_terms {d dp dterm : ℕ} (hp : 1 ≤ dp) (hterm : dterm + dp ≤ d) :
    dterm + 1 ≤ d := by omega

/-- **`thm:ff`, no two-cycles.** A degree-lowering map has no two-cycle: `deg g + 1 ≤ deg f` and
`deg f + 1 ≤ deg g` are inconsistent. -/
theorem no_two_cycle_of_drop {df dg : ℕ} (h1 : dg + 1 ≤ df) (h2 : df + 1 ≤ dg) : False := by omega

/-- **`thm:ff`, no nonzero fixed points.** Likewise `deg f + 1 ≤ deg f` is inconsistent, so the
analogues of the integer fixed points `p^p` vanish. -/
theorem no_fixed_point_of_drop {df : ℕ} (h : df + 1 ≤ df) : False := by omega

/-- The two together, in the form the theorem is used: on a set where the derivative lowers the
degree, neither a two-cycle nor a fixed point exists. The hypothesis `hdrop` is exactly
`deg f' ≤ deg f - 1`, which `deg_drop_of_terms` supplies, and it holds verbatim for every twisted
variant since the twist multiplies each term by a unit and does not change its degree. -/
theorem ff_no_cycle {S : Type*} (deg : S → ℕ) (D : S → S)
    (hdrop : ∀ x, deg (D x) + 1 ≤ deg x) (f g : S) (h1 : D f = g) (h2 : D g = f) : False := by
  have hf := hdrop f
  have hg := hdrop g
  rw [h1] at hf
  rw [h2] at hg
  omega

end Erdos307
