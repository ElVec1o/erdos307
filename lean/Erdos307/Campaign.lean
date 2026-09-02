import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The campaign lemma: one binary certificate per tail family

`rem:campaign` runs a Jacobi certificate over the 49,961 admissible bases at level 60. For each
base `S` it forms `A_S = N_S + 2 D_S` and `B_S = N_S - 2 D_S`, and kills the family when
`(D_S | A_S) = -1`. The paper observes that `(D_S | A_S) = (D_S | B_S)` *always*, so one symbol
decides a family rather than two. This file proves that observation.

The reason is periodicity rather than reciprocity: `A_S - B_S = 4 D_S`, and `J(a | ·)` has period
`4a` in its denominator (`jacobiSym.mod_right`). The paper's own derivation goes through
`A_S ≡ B_S (mod 8)`, agreement mod every odd `p ∣ D_S`, and an even reciprocity exponent; the
periodicity route below is the same fact packaged once.

## Scope

The *primality* of the 34 immune `A_S, B_S` is deliberately not formalised here, and cannot
currently be. mathlib's only route to a large prime is `lucas_primality`, which requires a
complete factorisation of `n - 1`, and `code/immune_certify.py` establishes that this is out of
reach for these 114-digit numbers: 0 of 34 reach even the Brillhart-Lehmer-Selfridge threshold
`n^(1/3)`. Those primality facts rest on the external ECPP certificates in
`data/certs/immune_ecpp.txt`, which any third party can verify but which no Lean tactic can consume.

Paper: Remark `rem:campaign` (the campaign lemma; the ECPP certificates are external).
-/

namespace Erdos307

/-- Shifting the denominator of a Jacobi symbol by `4 * d` leaves it unchanged. -/
theorem jacobiSym_add_four_mul (d : ℕ) {b : ℕ} (hb : Odd b) :
    jacobiSym (d : ℤ) (b + 4 * d) = jacobiSym (d : ℤ) b := by
  have ha : Odd (b + 4 * d) := by
    obtain ⟨k, hk⟩ := hb
    exact ⟨k + 2 * d, by omega⟩
  rw [jacobiSym.mod_right (d : ℤ) ha, jacobiSym.mod_right (d : ℤ) hb,
    Int.natAbs_natCast d, Nat.add_mod_right]

/-- **The campaign lemma.** With `A = N + 2D` and `B = N - 2D`, the two Jacobi symbols
`(D | A)` and `(D | B)` agree, so a single binary test decides each tail family. -/
theorem jacobiSym_A_eq_B (d n : ℕ) (h : 2 * d ≤ n) (hodd : Odd (n - 2 * d)) :
    jacobiSym (d : ℤ) (n + 2 * d) = jacobiSym (d : ℤ) (n - 2 * d) := by
  have e : n + 2 * d = (n - 2 * d) + 4 * d := by omega
  rw [e]
  exact jacobiSym_add_four_mul d hodd

end Erdos307
