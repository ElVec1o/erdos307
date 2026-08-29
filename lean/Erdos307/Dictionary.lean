import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The mass-to-size dictionary: the algebraic cores

`rem:dictionary` observes that every barrier in the note is one implication,

  `∑_{p ∈ U} 1/p ≥ c  ⟹  |U| ≥ n(c)`,

read at different `c`, and that the arithmetic specific to each row is only the derivation of its
`c`. This file machine-checks the algebra of the rows, with the number-theoretic inputs supplied as
hypotheses exactly as in `NoPoly.lean`, so what is imported stays visible. The inputs used are:

* `∑_{p ∈ S} 1/p ≤ T_{|S|}` (extremality of the smallest primes, `Extremal.lean`);
* `σ(a)σ(b) = 1` with `σ(a) + σ(b) ≤ T_{|U|}` (rigidity, disjoint supports);
* for `prop:kuniform`, that each prime occupies an independent set of the cycle `C_k`, so its
  multiplicity is at most `⌊k/2⌋`, and that the masses telescope to product `1`.

What is proved here is the part that does not depend on which row is being read.

* `cost_of_ratio` : `2√r ≤ S ⟹ r ≤ (S/2)²`. This is `cor:cost` and, with `S = T_{|U|}`,
  `prop:frontier`.
* `mass_window` : if `xy = 1`, `x, y > 0` and `x + y ≤ T`, then `1/t ≤ x ≤ t` for `t ≥ 1` the root
  of `t² - Tt + 1 = 0`. This is `prop:window`, and `prop:split` is its corollary.
* `uniform_from_multiplicity` : if the masses sum to at least `k` and each prime contributes with
  multiplicity at most `m`, then the support mass is at least `k/m`. With `m = ⌊k/2⌋` this is
  `prop:kuniform`; with `m = ⌈L/2⌉` and `k = L·G^{1/L}` it is `prop:growth`.
* `band_bound` : if a support carries mass above `2`, and all but one of its primes carry at most
  `T`, then the exceptional prime `q` satisfies `1/q > 2 - T`. This is `prop:band`, whose
  consequence is that the level is finite exactly when `T < 2`.

Paper: Remark `rem:dictionary`, Propositions `prop:frontier`, `prop:window`, `prop:split`,
`prop:kuniform`, `prop:growth`, `prop:band`, Corollary `cor:cost`.
-/

namespace Erdos307.Dictionary

/-- **The cost of a ratio.** `2√r ≤ S` forces `r ≤ (S/2)²`. Read with `S = T_{|U|}` and `r` the
near-miss ratio this is `cor:cost`; solving for `r` instead gives `prop:frontier`. -/
theorem cost_of_ratio {r S : ℝ} (hr : 0 ≤ r) (h : 2 * Real.sqrt r ≤ S) : r ≤ (S / 2) ^ 2 := by
  have hs : Real.sqrt r ≤ S / 2 := by linarith
  have hnn : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have := mul_self_le_mul_self hnn hs
  rwa [Real.mul_self_sqrt hr, ← pow_two] at this

/-- **The mass window.** With `xy = 1`, `x, y > 0`, `x + y ≤ T`, and `t ≥ 1` the root above `1` of
`t² - Tt + 1 = 0`, both masses lie in `[1/t, t]`. This is `prop:window`; requiring `T_k ≥ 1/t` for
the smaller support is `prop:split`. -/
theorem mass_window {x y t T : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x * y = 1)
    (hsum : x + y ≤ T) (ht : 1 ≤ t) (hroot : t ^ 2 - T * t + 1 = 0) :
    1 / t ≤ x ∧ x ≤ t := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  -- multiplying `x + y ≤ T` by `x > 0` and using `xy = 1`
  have hq : x ^ 2 - T * x + 1 ≤ 0 := by nlinarith [hsum, hxy, hx]
  -- `t·(x² - Tx + 1) = (tx - 1)(x - t)` once `t² + 1 = Tt`
  have hfac : (t * x - 1) * (x - t) ≤ 0 := by nlinarith [hq, hroot, ht0]
  constructor
  · rw [div_le_iff₀ ht0]
    by_contra hc
    push Not at hc
    have hxt : x < t := by nlinarith [hc, ht, ht0]
    nlinarith [hfac, hc, hxt]
  · by_contra hc
    push Not at hc
    have h1 : 0 < x - t := by linarith
    have hb : t * t < t * x := mul_lt_mul_of_pos_left hc ht0
    have hc2 : (1 : ℝ) * 1 ≤ t * t := mul_le_mul ht ht zero_le_one (by linarith)
    rw [one_mul] at hc2
    have h2 : 0 < t * x - 1 := by linarith
    nlinarith [hfac, h1, h2]

/-- **Multiplicity to mass.** If the masses sum to at least `k` and every prime is counted with
multiplicity at most `m`, the support mass is at least `k/m`. With `m = ⌊k/2⌋` (a prime occupies an
independent set of `C_k`) this is `prop:kuniform`; with `m = ⌈L/2⌉` it is `prop:growth`. -/
theorem uniform_from_multiplicity {k m S total : ℝ} (hm : 0 < m)
    (hlow : k ≤ total) (hhigh : total ≤ m * S) : k / m ≤ S := by
  rw [div_le_iff₀ hm]
  calc k ≤ total := hlow
    _ ≤ m * S := hhigh
    _ = S * m := by ring

/-- **The band.** If the support carries mass above `2` and all but one prime carry at most `T`,
the exceptional prime has `1/q > 2 - T`. Finiteness of the level is exactly `T < 2`. -/
theorem band_bound {T q total : ℝ} (_hq : 0 < q) (htot : 2 < total)
    (hsplit : total ≤ T + 1 / q) : 2 - T < 1 / q := by linarith

end Erdos307.Dictionary
