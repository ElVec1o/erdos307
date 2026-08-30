import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The coprime relaxation of #307

Barbeau's question is asked on `erdosproblems.com/307` in a weakened form: drop primality and ask
only that the members of each set be pairwise coprime. Examples are known, but every one of them
contains `1`, and no example is known with `1 ∉ P ∪ Q`. This file proves the fact that explains the
pattern: a family of pairwise coprime integers `≥ 2` can never have reciprocal sum `1`.

The argument is a single divisibility. If `A` is such a family with reciprocal sum `1` and `a ∈ A`,
put `R = ∏ (A.erase a)`. Every other member divides `R`, so clearing `R` through the identity leaves
`R / a` equal to an integer, whence `a ∣ R`. But `a` is coprime to `R`, so `a = 1`.

Paper: Proposition `prop:coprimeone`.
-/

namespace Erdos307.Coprime

open Finset

/-- A pairwise coprime family of integers `≥ 2` cannot have reciprocal sum `1`. Consequently every
solution of the coprime relaxation of #307 in which one side has reciprocal sum `1` must use the
member `1`, which is what every known example does. -/
theorem sum_inv_ne_one {A : Finset ℕ} (h2 : ∀ a ∈ A, 2 ≤ a)
    (hcop : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) :
    ∑ a ∈ A, (1 : ℚ) / (a : ℚ) ≠ 1 := by
  intro hsum
  -- `A` is nonempty, since the empty sum is `0`.
  have hA : A.Nonempty := by
    rcases A.eq_empty_or_nonempty with rfl | h
    · simp at hsum
    · exact h
  obtain ⟨a, ha⟩ := hA
  set R : ℕ := ∏ b ∈ A.erase a, b with hR
  have ha2 : 2 ≤ a := h2 a ha
  have ha0 : (0 : ℚ) < (a : ℚ) := by
    have : (0 : ℕ) < a := by omega
    exact_mod_cast this
  -- every other member divides `R`
  have hdvd : ∀ b ∈ A.erase a, b ∣ R := fun b hb => Finset.dvd_prod_of_mem _ hb
  -- `a` is coprime to `R`
  have hcopR : Nat.Coprime a R := by
    rw [hR]
    exact Nat.Coprime.prod_right fun b hb =>
      hcop a ha b (Finset.mem_of_mem_erase hb) (Ne.symm (Finset.ne_of_mem_erase hb))
  have hR0 : 0 < R := by
    rw [hR]
    exact Finset.prod_pos fun b hb => by have := h2 b (Finset.mem_of_mem_erase hb); omega
  -- the integer `S = ∑_{b ≠ a} R / b`
  set S : ℕ := ∑ b ∈ A.erase a, R / b with hS
  have hcastS : (S : ℚ) = ∑ b ∈ A.erase a, (R : ℚ) / (b : ℚ) := by
    rw [hS]
    push_cast
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb2 : 2 ≤ b := h2 b (Finset.mem_of_mem_erase hb)
    have hbne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact Nat.cast_div (hdvd b hb) hbne
  -- clear `R` through the hypothesis
  have hkey : (R : ℚ) / (a : ℚ) = (R : ℚ) - (S : ℚ) := by
    have hsplit : ∑ b ∈ A, (R : ℚ) / (b : ℚ)
        = (R : ℚ) / (a : ℚ) + ∑ b ∈ A.erase a, (R : ℚ) / (b : ℚ) :=
      (Finset.add_sum_erase _ _ ha).symm
    have hmul : ∑ b ∈ A, (R : ℚ) / (b : ℚ) = (R : ℚ) := by
      have : ∑ b ∈ A, (R : ℚ) / (b : ℚ) = (R : ℚ) * ∑ b ∈ A, (1 : ℚ) / (b : ℚ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, hsum, mul_one]
    rw [hcastS]
    linarith [hsplit, hmul]
  -- hence `a ∣ R`
  have hdvdaR : a ∣ R := by
    have hRS : R = a * (R - S) := by
      have h1 : (R : ℚ) = (a : ℚ) * ((R : ℚ) - (S : ℚ)) := by
        field_simp at hkey
        linarith [hkey]
      have hSR : (S : ℚ) ≤ (R : ℚ) := by nlinarith [h1, ha0, hkey]
      have hSRn : S ≤ R := by exact_mod_cast hSR
      have : ((R : ℕ) : ℚ) = ((a * (R - S) : ℕ) : ℚ) := by
        push_cast [Nat.cast_sub hSRn]
        linarith [h1]
      exact_mod_cast this
    exact ⟨R - S, hRS⟩
  -- but `a` is coprime to `R`, so `a = 1`
  have : a = 1 := Nat.dvd_one.mp (hcopR ▸ Nat.dvd_gcd dvd_rfl hdvdaR)
  omega


/-- The engine behind the rigidity of the coprime relaxation. For a pairwise coprime family `A` of
positive integers with product `α`, the numerator `M = ∑ α / a` is coprime to every member of `A`.
The reason is that every term but one is divisible by `a`, and the remaining term `α / a` is the
product of the other members, hence coprime to `a`. -/
theorem coprime_numerator {A : Finset ℕ} (h1 : ∀ a ∈ A, 0 < a)
    (hcop : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) {a : ℕ} (ha : a ∈ A) :
    Nat.Coprime (∑ b ∈ A, (∏ c ∈ A, c) / b) a := by
  set α : ℕ := ∏ c ∈ A, c with hα
  have hprod : α / a = ∏ c ∈ A.erase a, c := by
    rw [hα, ← Finset.prod_erase_mul _ _ ha, Nat.mul_div_cancel _ (h1 a ha)]
  have hcopa : Nat.Coprime (α / a) a := by
    rw [hprod]
    exact Nat.Coprime.prod_left fun c hc =>
      hcop c (Finset.mem_of_mem_erase hc) a ha (Finset.ne_of_mem_erase hc)
  -- every other term is divisible by `a`
  have hterm : ∀ b ∈ A.erase a, a ∣ α / b := by
    intro b hb
    have hbA : b ∈ A := Finset.mem_of_mem_erase hb
    have : α / b = ∏ c ∈ A.erase b, c := by
      rw [hα, ← Finset.prod_erase_mul _ _ hbA, Nat.mul_div_cancel _ (h1 b hbA)]
    rw [this]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hb).symm, ha⟩)
  have hsplit : ∑ b ∈ A, α / b = α / a + ∑ b ∈ A.erase a, α / b :=
    (Finset.add_sum_erase _ _ ha).symm
  have hdvd : a ∣ ∑ b ∈ A.erase a, α / b := Finset.dvd_sum hterm
  obtain ⟨j, hj⟩ := hdvd
  rw [hsplit, hj, mul_comm]
  exact (Nat.coprime_add_mul_right_left (α / a) a j).mpr hcopa

end Erdos307.Coprime
