import Erdos307.Rigidity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The mod-8 law of the derivative, and the parity dichotomy

`prop:mod8` and `thm:parity`.

For odd squarefree `m`, writing `S(m) = ∑_{p ∣ m} p`,

  `m · m' ≡ S(m)  (mod 8)`.

The proof is one observation: `q² ≡ 1 (mod 8)` for odd `q`. Writing `m = p·c_p` with `c_p = m/p`,
each term of `m·m' = ∑_p m·c_p` is `p·c_p²`, and `c_p` is odd, so the term is `≡ p`. Summing gives
the law. This file proves it in that form, over the `Finset` model of squarefree supports.

Two consequences are recorded.

* **Modulo `2`** the law degenerates to the parity law `m' ≡ ω(m)`, since every cofactor `m/p` is
  odd. That is `parity_law`, and it is the arithmetic heart of `thm:parity`: in the mixed-parity
  case `a = 2k`, the odd member `b` has `b' = a` even, so `ω(b)` is even
  (`omega_even_of_even_derivative`). The other branch of the dichotomy, that `a` and `b` cannot both
  be even, is `gcd(a, a') = 1`, which is Rigidity.

* **For an all-odd two-cycle** `a' = b`, `b' = a`, the law applied to each member gives
  `S(a) ≡ S(b) ≡ ab (mod 8)`: the two prime sums are congruent to each other and to the product.
  That is `prime_sums_congruent`, and it refines `thm:parity`(ii).

None of these congruences is an obstruction, consistently with `prop:localcomplete`. They thin every
hunt over the odd sector by a fixed factor, which is what they are used for.

The parity law is stated over `ℕ` with `%`, which keeps it free of any `ZMod` API; the mod-`8` law
uses `ZMod 8`, where the only external fact needed is `(8 : ZMod 8) = 0`, checked by `decide`.

Paper: Proposition `prop:mod8`, Theorem `thm:parity`.
-/

namespace Erdos307

open Finset

/-! ### Odd squares modulo 8 -/

/-- **The whole content of the mod-8 law**: an odd number squares to `1` modulo `8`. The proof is
`(2k+1)² = 4k(k+1) + 1` together with `k(k+1)` even. -/
theorem odd_sq_mod8 {n : ℕ} (h : Odd n) : ((n : ℕ) : ZMod 8) ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
  have hcast : ((2 * k + 1 : ℕ) : ZMod 8) ^ 2 = 4 * ((k * (k + 1) : ℕ) : ZMod 8) + 1 := by
    push_cast; ring
  rw [hcast, hm]
  push_cast
  have h8 : (8 : ZMod 8) = 0 := by decide
  linear_combination (m : ZMod 8) * h8

/-- Every cofactor `m/p` of a product of odd primes is odd. -/
theorem cofactor_odd {S : Finset ℕ} (hodd : ∀ p ∈ S, Odd p) {p : ℕ} (hp : p ∈ S) (hp0 : 0 < p) :
    Odd (dprod S / p) := by
  rw [dprod_div S hp hp0]
  exact Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one
    (fun q hq => hodd q (Finset.mem_of_mem_erase hq))

/-! ### The mod-8 law -/

/-- **`prop:mod8`.** For a squarefree odd `m` with prime support `S`,

  `m · m' ≡ ∑_{p ∈ S} p  (mod 8)`.

Each summand of `m · m' = ∑_p m · (m/p)` equals `p · (m/p)²`, and `(m/p)² ≡ 1` because the cofactor
is odd. -/
theorem mod8_law {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hodd : ∀ p ∈ S, Odd p) :
    ((dprod S : ℕ) : ZMod 8) * ((csum S : ℕ) : ZMod 8) = ∑ p ∈ S, ((p : ℕ) : ZMod 8) := by
  simp only [csum, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (hS p hp).pos
  have hfac : dprod S = p * (dprod S / p) :=
    (Nat.mul_div_cancel' (Finset.dvd_prod_of_mem _ hp)).symm
  have hsq := odd_sq_mod8 (cofactor_odd hodd hp hp0)
  have hcast : ((dprod S : ℕ) : ZMod 8) = (p : ZMod 8) * ((dprod S / p : ℕ) : ZMod 8) := by
    conv_lhs => rw [hfac]
    push_cast
    ring
  rw [hcast]
  linear_combination (p : ZMod 8) * hsq

/-- **`prop:mod8`(b).** For an all-odd two-cycle `a' = b`, `b' = a`, the mod-8 law applied to each
member gives `S(a) ≡ ab` and `S(b) ≡ ab`, so the two prime sums are congruent to each other and to
the product. This refines `thm:parity`(ii). -/
theorem prime_sums_congruent {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPodd : ∀ p ∈ P, Odd p) (hQodd : ∀ q ∈ Q, Odd q)
    (h1 : csum P = dprod Q) (h2 : csum Q = dprod P) :
    (∑ p ∈ P, ((p : ℕ) : ZMod 8)) = ∑ q ∈ Q, ((q : ℕ) : ZMod 8) := by
  have hA := mod8_law hP hPodd
  have hB := mod8_law hQ hQodd
  rw [h1] at hA
  rw [h2] at hB
  rw [← hA, ← hB]
  ring

/-! ### The parity law and `thm:parity` -/

/-- **The mod-2 shadow of the law.** Every cofactor `m/p` is odd, so `m' ≡ ω(m) (mod 2)`. Stated
over `ℕ` with `%`, so it needs no `ZMod` API at all. -/
theorem parity_law {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hodd : ∀ p ∈ S, Odd p) :
    csum S % 2 = S.card % 2 := by
  have hone : ∀ p ∈ S, (dprod S / p) % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (cofactor_odd hodd hp (hS p hp).pos)
  calc csum S % 2 = (∑ p ∈ S, (dprod S / p) % 2) % 2 := by rw [csum, Finset.sum_nat_mod]
    _ = (∑ _p ∈ S, 1) % 2 := by rw [Finset.sum_congr rfl hone]
    _ = S.card % 2 := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- **`thm:parity`(i).** In the mixed-parity case `a = 2k`, the odd member `b` has `b' = a` even, so
`ω(b)` is even. This is the parity law read backwards. -/
theorem omega_even_of_even_derivative {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, Odd q) (heven : Even (csum Q)) : Even Q.card := by
  rw [Nat.even_iff] at heven ⊢
  rw [← parity_law hQ hodd]
  exact heven

/-- **`thm:parity`, the other branch.** The two members of a cycle cannot both be even, since
`gcd(a, a') = 1`. In the support model this is the statement that a prime of `P` cannot divide
`csum P`, which is Rigidity. -/
theorem not_both_even {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (h2 : 2 ∈ P) :
    ¬ (2 ∣ csum P) := by
  intro hdvd
  have hg : Nat.gcd (csum P) (dprod P) = 1 := rigidity_coprime P hP
  have hpd : (2 : ℕ) ∣ dprod P := Finset.dvd_prod_of_mem _ h2
  have h1 : (2 : ℕ) ∣ 1 := by rw [← hg]; exact Nat.dvd_gcd hdvd hpd
  omega

end Erdos307
