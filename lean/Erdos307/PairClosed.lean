import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

/-!
# The pair sector of level 60: the algebraic core

A support `U = R ∪ {m}` with `D = ∏ R`, `D' = ∑_{p ∈ R} D/p` has `N = D m` and, by Leibniz, `N' = D' m + D`.
A two-cycle on `U` splits `N = a b` with `N' = a² + b²` (`pyth_sum_of_squares`). Hence
`(D' + 2D) m + D = (a+b)²` and `(D' - 2D) m + D = (a-b)²`, independently of the split.

In the pair sector `T(R) < 2`, i.e. `D' < 2D`, so the second square bounds the tail:
`m (2D - D') ≤ D`, that is `m ≤ 1/(2 - T(R))`. Reducing the first square modulo a prime `p ∣ D`, where
`D' ≡ D/p`, shows `(D/p) m` is a square mod `p`; for `p ∤ (D/p) m` this is `(m|p) = ((D/p)|p)`.
The computation of `code/pairsector_close.rs` applies exactly these two facts to every base.

Paper: Proposition `prop:pairclosed`.
-/

namespace Erdos307

/-- The two squares of a support `R ∪ {m}`, independent of the split `N = a b`. -/
theorem pair_squares (D Dd m a b : ℤ) (hN : a * b = D * m) (hNd : a ^ 2 + b ^ 2 = Dd * m + D) :
    (Dd + 2 * D) * m + D = (a + b) ^ 2 ∧ (Dd - 2 * D) * m + D = (a - b) ^ 2 := by
  constructor
  · linear_combination (-1 : ℤ) * hNd + (-2 : ℤ) * hN
  · linear_combination (-1 : ℤ) * hNd + (2 : ℤ) * hN

/-- **The tail bound.** When `D' < 2D` (mass of `R` below `2`), the minus square forces
`m (2D - D') ≤ D`: the tail is bounded by `1/(2 - T(R))`. -/
theorem pair_tail_bound (D Dd m a b : ℤ) (hN : a * b = D * m) (hNd : a ^ 2 + b ^ 2 = Dd * m + D) :
    m * (2 * D - Dd) ≤ D := by
  have h := (pair_squares D Dd m a b hN hNd).2
  nlinarith [sq_nonneg (a - b)]

/-- **The character condition.** For a prime `p` with `D = p e` and `D' ≡ e (mod p)`, the plus square
makes `e m` a square modulo `p`. -/
theorem pair_char_square (p : ℕ) (D Dd m e a b : ℤ) (hN : a * b = D * m)
    (hNd : a ^ 2 + b ^ 2 = Dd * m + D) (hD : D = p * e) (hDd : (Dd : ZMod p) = e) :
    IsSquare ((e * m : ℤ) : ZMod p) := by
  have h := (pair_squares D Dd m a b hN hNd).1
  refine ⟨((a + b : ℤ) : ZMod p), ?_⟩
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) h
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hD, hDd] at hc
  have hp : (((p : ℤ) : ZMod p)) = 0 := by simp
  push_cast
  linear_combination hc + (-(2 * (e : ZMod p) * m) - e) * hp

/-- Hence `(m | p) = ((D/p) | p)` whenever `p ∤ (D/p) m`. -/
theorem pair_legendre (p : ℕ) [Fact p.Prime] (D Dd m e a b : ℤ) (hN : a * b = D * m)
    (hNd : a ^ 2 + b ^ 2 = Dd * m + D) (hD : D = p * e) (hDd : (Dd : ZMod p) = e)
    (he : (e : ZMod p) ≠ 0) (hm : (m : ZMod p) ≠ 0) :
    legendreSym p m = legendreSym p e := by
  have hsq := pair_char_square p D Dd m e a b hN hNd hD hDd
  have hem : ((e * m : ℤ) : ZMod p) ≠ 0 := by push_cast; exact mul_ne_zero he hm
  have h1 : legendreSym p e * legendreSym p m = 1 := by
    rw [← legendreSym.mul]; exact (legendreSym.eq_one_iff p hem).2 hsq
  have h2 : legendreSym p e ^ 2 = 1 := legendreSym.sq_one p he
  linear_combination (-(legendreSym p m)) * h2 + legendreSym p e * h1

end Erdos307
