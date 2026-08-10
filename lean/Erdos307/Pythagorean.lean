import Erdos307.Sixty
import Erdos307.RhoBarrier
import Erdos307.Capstone
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Pythagorean layer: the single-integer test, and why it is empty

`prop:pyth`, `cor:emptytest`, `prop:split`, `prop:kcycles`.

A two-cycle `a' = b`, `b' = a` makes `N = ab` squarefree with `N' = a² + b²`, so
`N'² - 4N² = (a² - b²)²` is a perfect square. That is a *one-integer* necessary test, strictly
weaker than the cycle condition, and the point of `cor:emptytest` is that the barrier survives the
weakening: the test is provably empty below `10^112`, so the empirical "0 of 103,596" is a theorem.

Everything here rests on Leibniz, which the project already has as `csum_union_eq`: for disjoint
prime supports, `(PQ)' = Q·P' + P·Q'`. The rest is algebra.

* `pyth_sum_of_squares`: `N' = a² + b²` for a two-cycle. One rewrite of Leibniz.
* `pyth_discriminant`: hence `N'² - 4N² = (a² - b²)²`, a perfect square. A ring identity over `ℤ`.
* `split_identity`: `prop:split`, the two-sided form
  `N' + 2N - (a+b)² = N' - 2N - (a-b)² = (ab)' - a² - b²`. Also a ring identity, and it is what
  isolates the obstructing factor: the minus side is a square only when `σ(N) ≥ 2`, while the plus
  side is satisfiable at small scale. In characteristic `2` the obstructing factor vanishes, which
  is exactly why the function-field analogue is permissive.
* `mass_ge_two_of_pythagorean` and `card_ge_59_of_pythagorean`: `cor:emptytest`. Dividing
  `a² + b² = (ab)'` by `ab` gives `σ(N) = a/b + b/a ≥ 2` by AM-GM, so the support carries at least
  `59` primes and `N ≥ Π₅₉ > 7.9 × 10^112`. The barrier therefore extends from two-cycles to the
  strictly weaker one-equation problem.
* `sum_ge_card_of_prod_eq_one`: `prop:kcycles`'s AM-GM step, for every `k` at once. The masses of a
  `k`-cycle multiply to `1`, so their sum is at least `k`. The proof is `log x ≤ x - 1` summed,
  which is the same inequality that forces `λ = 1/2` in `thm:halflyap`; no `k`-term AM-GM is needed.

What is *not* here: the converse half of `prop:pyth` (that a squarefree `N` passing the test
determines the factorisation) is Bado's, cited; and the values `m₂ = 59`, `m₃ = 361,139` are
computations, the first of which is `card_ge_59_of_recipSum_ge_two` and the second of which is not
formalised.

Paper: Proposition `prop:pyth`, Corollary `cor:emptytest`, Proposition `prop:split`,
Proposition `prop:kcycles`, Proposition `prop:kdev`.
-/

namespace Erdos307

open Finset

/-! ### The Pythagorean identity -/

/-- **`prop:pyth`.** For a two-cycle `a' = b`, `b' = a` with disjoint supports, `N = ab` satisfies
`N' = a² + b²`. This is Leibniz together with the cycle equations, nothing more. -/
theorem pyth_sum_of_squares {P Q : Finset ℕ} (hdisj : Disjoint P Q)
    (h1 : csum P = dprod Q) (h2 : csum Q = dprod P) :
    csum (P ∪ Q) = dprod P ^ 2 + dprod Q ^ 2 := by
  rw [csum_union_eq hdisj, h1, h2]; ring

/-- **The single-integer test.** Hence `N'² - 4N² = (a² - b²)²` is a perfect square: a necessary
condition on `N` alone, with the pair `(a,b)` eliminated. -/
theorem pyth_discriminant (a b : ℤ) :
    (a ^ 2 + b ^ 2) ^ 2 - 4 * (a * b) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 := by ring

/-! ### The split discriminant -/

/-- **`prop:split`.** The two layers differ by the same amount from the two squares:
`N' + 2N - (a+b)² = N' - 2N - (a-b)² = N' - a² - b²`. So `N` is the product of a Pythagorean pair
iff `N' - 2N` and `N' + 2N` are *both* perfect squares, and their product is Bado's discriminant
`N'² - 4N²`.

The minus factor carries the obstruction: `N' - 2N = (a-b)² ≥ 0` forces `σ(N) ≥ 2`, hence the
barrier. In characteristic `2` the obstructing factor vanishes, since `a - b = a + b` there, and the
criterion degenerates to `(a+b)² = N'`. The permissiveness of the function-field statement and the
barrier here are the absence and presence of one and the same algebraic factor. -/
theorem split_identity (Nd Nn a b : ℤ) (hN : Nn = a * b) :
    Nd + 2 * Nn - (a + b) ^ 2 = Nd - a ^ 2 - b ^ 2 ∧
    Nd - 2 * Nn - (a - b) ^ 2 = Nd - a ^ 2 - b ^ 2 := by
  constructor <;> rw [hN] <;> ring

/-- The product of the two layers is the discriminant. -/
theorem split_product (Nd Nn : ℤ) : (Nd - 2 * Nn) * (Nd + 2 * Nn) = Nd ^ 2 - 4 * Nn ^ 2 := by ring

/-! ### `cor:emptytest`: the test is empty below the barrier -/

/-- **The mass bound.** Dividing `a² + b² = (ab)'` by `ab` gives `σ(N) = a/b + b/a ≥ 2`, by AM-GM.
The Pythagorean condition alone, without the cycle condition, already forces mass `2`. -/
theorem mass_ge_two_of_pythagorean {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    2 ≤ (a ^ 2 + b ^ 2) / (a * b) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a - b)]

/-- **`cor:emptytest`.** A Pythagorean pair carries at least `59` primes in its support, so
`N = ab ≥ Π₅₉ > 7.9 × 10^112` and no squarefree `N < 10^112` with `ω(N) ≥ 2` passes the
single-integer test. The empirical "`0` of `103,596`" is a theorem, and the barrier extends from
two-cycles to the strictly weaker one-equation problem. -/
theorem card_ge_59_of_pythagorean {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime)
    (h : (2 : ℚ) ≤ (csum U : ℚ) / (dprod U : ℚ)) : 59 ≤ U.card := by
  refine card_ge_59_of_recipSum_ge_two hU ?_
  rwa [recipSum_eq U hU]

/-! ### `prop:kcycles`: longer cycles are harder -/

/-- **The AM-GM step of `prop:kcycles`, for every `k` at once.** If positive reals multiply to `1`,
their sum is at least their number. Applied to the masses `s(aᵢ) = a_{i+1}/aᵢ` of a `k`-cycle, whose
product telescopes to `1`, this gives `∑ s(aᵢ) ≥ k`, so the support contains at least `m_k` primes
where `m_k` is least with `∑_{i ≤ m_k} 1/pᵢ ≥ k`.

The proof is `log x ≤ x - 1` summed over the family, the same inequality that forces `λ = 1/2` in
`thm:halflyap`. No `k`-term AM-GM is needed, and the statement holds for an arbitrary finite index
set. -/
theorem sum_ge_card_of_prod_eq_one {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 < x i) (hprod : ∏ i ∈ s, x i = 1) :
    (s.card : ℝ) ≤ ∑ i ∈ s, x i := by
  have h1 : ∀ i ∈ s, Real.log (x i) ≤ x i - 1 := fun i hi =>
    Real.log_le_sub_one_of_pos (hx i hi)
  have h2 : ∑ i ∈ s, Real.log (x i) ≤ ∑ i ∈ s, (x i - 1) := Finset.sum_le_sum h1
  have h3 : ∑ i ∈ s, Real.log (x i) = 0 := by
    rw [← Real.log_prod (fun i hi => (hx i hi).ne'), hprod, Real.log_one]
  rw [h3, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  linarith

/-- The `k = 2` case, which is the one the paper uses: two masses multiplying to `1` have sum at
least `2`, whence `59` primes. This is `lem:amgm` again, from the general statement. -/
theorem two_le_sum_of_mul_eq_one {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : s * t = 1) :
    2 ≤ s + t := by nlinarith [sq_nonneg (s - t), sq_nonneg (s + t - 2)]

end Erdos307
