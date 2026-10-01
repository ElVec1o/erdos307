import Erdos307.Pythagorean
import Erdos307.Injective

/-!
# The pair form and the split discriminant

`prop:pairform` and `prop:splitdisc`: the one-equation relaxation `a² + b² = (ab)'` of the two-cycle
problem, and the two-square form of the same equation.

For disjoint prime sets `P`, `Q` put `a = ∏ P`, `b = ∏ Q`, so `a' = csum P`, `b' = csum Q` and, by
Leibniz, `(ab)' = csum (P ∪ Q)`.

* `pair_form_iff` (`prop:pairform`): `a² + b² = (ab)'` holds iff there is an integer `k` with
  `a' = b + a k` and `b' = a - b k`; a two-cycle is the case `k = 0`. The proof is the identity
  `a² + b² - (ab)' = a (a - b') - b (a' - b)` and the coprimality of `a` and `b`.
* `pair_iff_two_squares` (`prop:splitdisc`): `a² + b² = (ab)'` holds iff `N' + 2N = (a+b)²` and
  `N' - 2N = (a-b)²`, where `N = ab`.
* `pair_of_two_squares` (`prop:splitdisc`, converse): if `N' + 2N = s²` and `N' - 2N = d²` for a
  support `U` of primes, then `N` is the product of a pair, namely `a, b = (s ± d)/2`. This is the
  statement that the single-integer test `N'² - 4N² = □` loses nothing.
* `card_ge_59_of_minus_square`: the minus layer `N' - 2N = (a - b)² ≥ 0` forces `σ(N) ≥ 2`, hence
  `59` primes; the paper's "`0` of `103,596` squarefree `N < 2·10⁵`" is this statement.

What is *not* here: the counts `103,596` and `114` of the paper are computations; the first follows
from `card_ge_59_of_minus_square`, the second is not formalised. The characteristic-`2` remark is a
statement about the function-field analogue and is formalised there (`prop:ff-pyth`).

Paper: Proposition `prop:pairform`, Proposition `prop:splitdisc`.
-/

namespace Erdos307

open Finset

/-- The product of a set of primes is squarefree. -/
lemma squarefree_dprod {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) : Squarefree (dprod U) := by
  unfold dprod
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun p hp => (hU p hp).squarefree)
  intro p hp q hq hpq
  exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hU p hp) (hU q hq)).2 hpq)

/-- Disjoint sets of primes have coprime products. -/
lemma coprime_dprod_of_disjoint {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdisj : Disjoint P Q) : Nat.Coprime (dprod P) (dprod Q) := by
  unfold dprod
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
  refine (Nat.coprime_primes (hP p hp) (hQ q hq)).2 ?_
  rintro rfl
  exact Finset.disjoint_left.1 hdisj hp hq

lemma dprod_union_disjoint {P Q : Finset ℕ} (hdisj : Disjoint P Q) :
    dprod (P ∪ Q) = dprod P * dprod Q := by
  unfold dprod; exact Finset.prod_union hdisj

/-- **`prop:pairform`.** For coprime squarefree `a = ∏ P`, `b = ∏ Q`, the single equation
`a² + b² = (ab)'` holds iff there is an integer `k` with `a' = b + a k` and `b' = a - b k`. A
two-cycle is exactly the case `k = 0`. -/
theorem pair_form_iff {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdisj : Disjoint P Q) :
    (dprod P : ℤ) ^ 2 + (dprod Q : ℤ) ^ 2 = (csum (P ∪ Q) : ℤ) ↔
      ∃ k : ℤ, (csum P : ℤ) = dprod Q + dprod P * k ∧ (csum Q : ℤ) = dprod P - dprod Q * k := by
  have hU : (csum (P ∪ Q) : ℤ) = dprod Q * csum P + dprod P * csum Q := by
    exact_mod_cast csum_union_eq hdisj
  have hcop : IsCoprime (dprod P : ℤ) (dprod Q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (coprime_dprod_of_disjoint hP hQ hdisj)
  have ha : (0 : ℤ) < dprod P := by exact_mod_cast dprod_pos hP
  rw [hU]
  constructor
  · intro h
    have key : (dprod P : ℤ) * (dprod P - csum Q) = dprod Q * (csum P - dprod Q) := by
      linear_combination h
    have hdvd : (dprod P : ℤ) ∣ dprod Q * (csum P - dprod Q) := ⟨_, key.symm⟩
    obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
    refine ⟨k, by linarith, ?_⟩
    have h2 : (dprod P : ℤ) * (dprod P - csum Q) = (dprod P : ℤ) * (dprod Q * k) := by
      rw [key, hk]; ring
    have := mul_left_cancel₀ ha.ne' h2
    linarith
  · rintro ⟨k, h1, h2⟩
    rw [h1, h2]; ring

/-- **`prop:splitdisc`, the two layers.** For disjoint supports, `a² + b² = (ab)'` iff both
`N' + 2N = (a + b)²` and `N' - 2N = (a - b)²`, where `N = ab`. -/
theorem pair_iff_two_squares {P Q : Finset ℕ} (hdisj : Disjoint P Q) :
    (dprod P : ℤ) ^ 2 + (dprod Q : ℤ) ^ 2 = (csum (P ∪ Q) : ℤ) ↔
      ((csum (P ∪ Q) : ℤ) + 2 * dprod (P ∪ Q) = (dprod P + dprod Q) ^ 2 ∧
        (csum (P ∪ Q) : ℤ) - 2 * dprod (P ∪ Q) = (dprod P - dprod Q) ^ 2) := by
  have hp : (dprod (P ∪ Q) : ℤ) = dprod P * dprod Q := by
    exact_mod_cast dprod_union_disjoint hdisj
  rw [hp]
  constructor
  · intro h; constructor <;> linear_combination -h
  · rintro ⟨h1, -⟩; linear_combination -h1

/-- **`prop:splitdisc`, the converse.** If `N' + 2N = s²` and `N' - 2N = d²` for the support `U` of
`N`, then `N` is the product of a pair `(a, b) = ((s + d)/2, (s - d)/2)`: the two-layer test loses
nothing, so `N'² - 4N² = □` is a faithful single-integer reformulation. -/
theorem pair_of_two_squares {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) {s d : ℤ} (hs : 0 ≤ s)
    (hd : 0 ≤ d) (h1 : (csum U : ℤ) + 2 * dprod U = s ^ 2)
    (h2 : (csum U : ℤ) - 2 * dprod U = d ^ 2) :
    ∃ P Q : Finset ℕ, Disjoint P Q ∧ P ∪ Q = U ∧
      (dprod P : ℤ) ^ 2 + (dprod Q : ℤ) ^ 2 = csum U := by
  have hNpos : (0 : ℤ) < dprod U := by exact_mod_cast dprod_pos hU
  have hsd : (s - d) * (s + d) = 4 * dprod U := by linear_combination h2 - h1
  -- `s + d` is even: otherwise `(s - d)(s + d)` would be odd
  obtain ⟨a, ha⟩ : Even (s + d) := by
    by_contra hne
    rw [Int.not_even_iff_odd] at hne
    have hodd2 : Odd (s - d) := by
      have : s - d = (s + d) - 2 * d := by ring
      rw [this]; exact hne.sub_even (even_two_mul d)
    have hmul : Odd ((s - d) * (s + d)) := hodd2.mul hne
    rw [hsd] at hmul
    exact (Int.not_even_iff_odd.2 hmul) ⟨2 * dprod U, by ring⟩
  -- `a = (s + d)/2` and `b = a - d = (s - d)/2`
  have hb : s - d = 2 * (a - d) := by linarith
  have hab : a * (a - d) = dprod U := by
    have h4 : (a + a) * (2 * (a - d)) = 4 * dprod U := by
      rw [← ha, ← hb]; linear_combination hsd
    have h5 : (4 : ℤ) * (a * (a - d)) = 4 * dprod U := by linear_combination h4
    exact Int.eq_of_mul_eq_mul_left (by norm_num) h5
  have ha0 : 0 ≤ a := by linarith
  have ha1 : 0 < a := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hab; omega
  have hb1 : 0 < a - d := by
    by_contra hneg
    have hneg' := not_lt.1 hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha0 hneg']
  lift a to ℕ using ha0
  lift (a - d) to ℕ using hb1.le with b hbdef
  have hab' : a * b = dprod U := by exact_mod_cast hab
  have hsqU := squarefree_dprod hU
  rw [← hab'] at hsqU
  obtain ⟨hcop, hsqa, hsqb⟩ := Nat.squarefree_mul_iff.1 hsqU
  have ha0' : a ≠ 0 := by exact_mod_cast ha1.ne'
  have hb0' : b ≠ 0 := by exact_mod_cast hb1.ne'
  refine ⟨a.primeFactors, b.primeFactors, Nat.Coprime.disjoint_primeFactors hcop, ?_, ?_⟩
  · rw [← Nat.primeFactors_mul ha0' hb0', hab']
    unfold dprod; exact Nat.primeFactors_prod hU
  · rw [dprod_primeFactors hsqa, dprod_primeFactors hsqb]
    have hbd : (b : ℤ) = a - d := hbdef
    have hs' : s = a + b := by rw [hbd]; linarith
    have hNabs : (dprod U : ℤ) = a * b := by exact_mod_cast hab'.symm
    rw [hs'] at h1
    rw [hNabs] at h1
    linear_combination (-1 : ℤ) * h1

/-- **The minus layer carries the barrier.** If `N' - 2N` is a square then `σ(N) ≥ 2`, so the
support has at least `59` primes; in particular no squarefree `N < 10^112` with `N' - 2N = □`
exists, which contains the paper's empirical "`0` of `103,596`". -/
theorem card_ge_59_of_minus_square {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) {d : ℤ}
    (h : (csum U : ℤ) - 2 * dprod U = d ^ 2) : 59 ≤ U.card := by
  refine card_ge_59_of_pythagorean hU ?_
  have hD : (0 : ℚ) < dprod U := by exact_mod_cast dprod_pos hU
  rw [le_div_iff₀ hD]
  have : (csum U : ℤ) - 2 * dprod U ≥ 0 := by rw [h]; positivity
  have hq : (csum U : ℚ) - 2 * dprod U ≥ 0 := by exact_mod_cast this
  linarith

end Erdos307
