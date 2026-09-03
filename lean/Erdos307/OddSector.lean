import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The parity of the derivative of an odd squarefree number

`prop:oddsector`. For odd squarefree `d` every cofactor `d/p` is a product of odd primes, hence odd,
so `d' = ∑_{p ∣ d} d/p` is a sum of `ω(d)` odd integers and has the parity of `ω(d)`. The consequence
used in the sector analysis is that `ω(d)` even forces `2 ∣ d'`, hence `2 ∣ dd'`, hence `2` is
excluded from `supp(e)` (Remark `rem:sectordprime`) and the mass `d/d'` must be carried by odd primes
alone, which lifts the mass floor `K(d)` by an order of magnitude.

* `sum_odd_parity` — a sum of `k` odd integers is congruent to `k` modulo `2`. This is the whole
  content; nothing about primes or divisors enters.
* `deriv_parity_of_odd` — the application: if every cofactor is odd, the cofactor sum has the parity
  of the number of cofactors.
* `two_dvd_deriv_of_even_omega` — the case that matters: an even number of odd cofactors gives an
  even cofactor sum, so `2` divides the derivative.

Paper: Proposition `prop:oddsector`, Remark `rem:sectordprime`.
-/

namespace Erdos307

open Finset

/-- **A sum of `k` odd integers is congruent to `k` modulo `2`.** -/
theorem sum_odd_parity {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ)
    (h : ∀ i ∈ s, Odd (f i)) : (∑ i ∈ s, f i) % 2 = (s.card : ℤ) % 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have hfa : Odd (f a) := h a (Finset.mem_insert_self a s)
      have ihs : (∑ i ∈ s, f i) % 2 = (s.card : ℤ) % 2 :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      obtain ⟨m, hm⟩ := hfa
      push_cast
      omega

/-- **The cofactor sum inherits the parity of the number of cofactors**, when every cofactor is odd.
For odd squarefree `d` the cofactors `d/p` are products of odd primes, so this applies with
`s` the prime divisors and `f p = d/p`, giving `d' ≡ ω(d) (mod 2)`. -/
theorem deriv_parity_of_odd {α : Type*} [DecidableEq α] (s : Finset α) (cof : α → ℤ)
    (h : ∀ p ∈ s, Odd (cof p)) : (∑ p ∈ s, cof p) % 2 = (s.card : ℤ) % 2 :=
  sum_odd_parity s cof h

/-- **The case that matters.** An even number of odd cofactors gives `2 ∣ d'`, so `2 ∣ dd'` and the
prime `2` is unavailable to `supp(e)`. -/
theorem two_dvd_deriv_of_even_omega {α : Type*} [DecidableEq α] (s : Finset α) (cof : α → ℤ)
    (h : ∀ p ∈ s, Odd (cof p)) (heven : Even s.card) : (2 : ℤ) ∣ ∑ p ∈ s, cof p := by
  have hp := sum_odd_parity s cof h
  obtain ⟨k, hk⟩ := heven
  have : (s.card : ℤ) % 2 = 0 := by rw [hk]; push_cast; omega
  omega

end Erdos307
