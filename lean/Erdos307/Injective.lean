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

/-! ## Transfer to integers

The paper states `lem:sigmainj` for squarefree integers rather than for prime sets. For squarefree
`n` the two agree: `n.primeFactors` consists of primes and its product is `n`.
-/

open scoped Nat

/-- The arithmetic derivative of a squarefree integer, as `csum` of its prime factors. -/
noncomputable def ad (n : ℕ) : ℕ := csum n.primeFactors

/-- For squarefree `n`, the product of `n.primeFactors` is `n` itself. -/
theorem dprod_primeFactors {n : ℕ} (hn : Squarefree n) : dprod n.primeFactors = n :=
  Nat.prod_primeFactors_of_squarefree hn

/-- **Injectivity on squarefree integers.** If `ad d * d' = ad d' * d` for squarefree `d, d'`,
then `d = d'`. This is the hypothesis `hdiag` consumed by `Erdos307.pairavg_bound`, and it is what
keeps `F(d,d') = ad d * d' - ad d' * d` off zero away from the diagonal. -/
theorem eq_of_cross {d d' : ℕ} (hd : Squarefree d) (hd' : Squarefree d')
    (h : ad d * d' = ad d' * d) : d = d' := by
  have hpd : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hpd' : ∀ p ∈ d'.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have e : dprod d.primeFactors = d := dprod_primeFactors hd
  have e' : dprod d'.primeFactors = d' := dprod_primeFactors hd'
  have h' : csum d.primeFactors * dprod d'.primeFactors
      = csum d'.primeFactors * dprod d.primeFactors := by
    rw [e, e']; exact h
  have := dprod_eq_of_mass_eq d.primeFactors d'.primeFactors hpd hpd' h'
  rwa [e, e'] at this

end Erdos307
