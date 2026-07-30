import Erdos307.Rigidity

/-!
# The mass function is injective on squarefree supports

`thm:pairavg` rests on one arithmetic fact: for squarefree `d`, `d'`, equality of the masses
`σ(d) = σ(d')` forces `d = d'`. It is what keeps `F(d,d') = D(d) d' - D(d') d` away from zero off
the diagonal, and so what confines the divisor-heavy case of that theorem to the diagonal.

The proof is the rigidity of Theorem `rigidity_coprime`: `csum S / dprod S` is already in lowest
terms, so the denominator is recoverable from the fraction. This file records the deduction.

Paper: Lemma `lem:sigmainj`.
-/

namespace Erdos307

open Finset

/-- Two fractions in lowest terms with equal value have equal denominators. Stated over `ℕ` with the
cross-multiplied hypothesis, which is what the mass equality supplies; no positivity is needed. -/
theorem den_eq_of_coprime_cross {a b c d : ℕ}
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d) (h : a * d = c * b) : b = d := by
  have hbd : b ∣ d := by
    have : b ∣ a * d := ⟨c, by rw [h]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hab) this)
  have hdb : d ∣ b := by
    have : d ∣ c * b := ⟨a, by rw [← h]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hcd) this)
  exact Nat.dvd_antisymm hbd hdb

/-- **Injectivity of the mass on squarefree supports.** If two finite sets of primes have equal
reciprocal sums, presented through the cross-multiplied identity
`csum S * dprod T = csum T * dprod S`, then their products agree. -/
theorem dprod_eq_of_mass_eq (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (h : csum S * dprod T = csum T * dprod S) :
    dprod S = dprod T :=
  den_eq_of_coprime_cross (rigidity_coprime S hS) (rigidity_coprime T hT) h

/-- The numerators agree too, so the whole fraction is determined. -/
theorem csum_eq_of_mass_eq (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (hTpos : 0 < dprod T)
    (h : csum S * dprod T = csum T * dprod S) :
    csum S = csum T := by
  have hd : dprod S = dprod T := dprod_eq_of_mass_eq S T hS hT h
  rw [hd] at h
  exact Nat.eq_of_mul_eq_mul_right hTpos h

end Erdos307
