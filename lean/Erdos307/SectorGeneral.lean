import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The forced-prime identity in an arbitrary sector

`prop:sector42` is stated at `d = 42`, where the sector equation is `42e - 41e' = 1764`, and
`Sector42.lean` formalises its algebra with those constants. The at-60 sweep and
`prop:ppnsectors` run the same argument in every sector, where the equation is `de - d'e' = d^2`.
The algebra is identical and is formalised here once, for arbitrary `d` and `d'`, so that the
enumerations over `16,234` sectors rest on a machine-checked identity rather than on the `d = 42`
instance plus an assertion that it generalises.

* `terminal_prime_general` — with `e = R·ℓ` and `e' = R'·ℓ + R` (the derivative of a product with
  `ℓ ∤ R`), the sector equation `de - d'e' = d²` is equivalent to `ℓ·(dR - d'R') = d'R + d²`. The
  last prime of `e` is therefore determined by the others: it is a quotient of two integers built
  from `S`, or there is no solution. This is what makes each sector a finite search.
* `terminal_prime_general'` — the converse, so the enumerator's test is exact and not merely
  necessary.
* `terminal_denom_pos_general` — a positive `ℓ` forces `dR - d'R' > 0` when `d'R + d² > 0`, the sign
  test performed before dividing.

Specialising `d = 42`, `d' = 41` recovers the statements of `Sector42.lean`.

Paper: Proposition `prop:sector42`, Proposition `prop:ppnsectors`, Remark `rem:sectordprime`.
-/

namespace Erdos307

/-- **The forced-prime identity, any sector.** -/
theorem terminal_prime_general (d dp R Rp l : ℤ)
    (h : d * (R * l) - dp * (Rp * l + R) = d ^ 2) :
    l * (d * R - dp * Rp) = dp * R + d ^ 2 := by linarith [h, mul_comm R l]

/-- **The converse**, so the integrality test is exact. -/
theorem terminal_prime_general' (d dp R Rp l : ℤ)
    (h : l * (d * R - dp * Rp) = dp * R + d ^ 2) :
    d * (R * l) - dp * (Rp * l + R) = d ^ 2 := by linarith [h, mul_comm R l]

/-- **The sign condition.** If `ℓ > 0` and `d'R + d² > 0` then the denominator is positive, which is
the test the enumerator applies before dividing. -/
theorem terminal_denom_pos_general (d dp R Rp l : ℤ) (hl : 0 < l) (hnum : 0 < dp * R + d ^ 2)
    (h : l * (d * R - dp * Rp) = dp * R + d ^ 2) : 0 < d * R - dp * Rp := by
  rcases lt_trichotomy (d * R - dp * Rp) 0 with hneg | hzero | hpos
  · exfalso; nlinarith
  · exfalso; rw [hzero, mul_zero] at h; linarith
  · exact hpos

/-- Specialisation to the sector `d = 42`, recovering the constants of `Sector42.lean`. -/
theorem terminal_prime_fortytwo (R Rp l : ℤ)
    (h : 42 * (R * l) - 41 * (Rp * l + R) = 1764) :
    l * (42 * R - 41 * Rp) = 41 * R + 1764 := by
  have := terminal_prime_general 42 41 R Rp l (by linarith [h])
  linarith [this]

end Erdos307
