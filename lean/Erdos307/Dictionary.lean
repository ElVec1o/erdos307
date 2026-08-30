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

/-- **The band at a general constant.** `prop:band` was stated at `c = 2`; the argument uses only
that all but one prime carry at most `T`. This is `prop:levelstructure`'s ceiling. -/
theorem band_bound_general {c T q total : ℝ} (htot : c ≤ total) (hsplit : total ≤ T + 1 / q) :
    c - T ≤ 1 / q := by linarith

/-- **The forced core.** If `p` is absent from the support, extremality caps the support's mass at
`Tnext - 1/p`, so carrying mass at least `c` forces `1/p ≤ Tnext - c`. Contrapositively, every
prime with `1/p > Tnext - c` lies in the support. This is `prop:window`'s second half at a general
constant, hence `prop:levelstructure`'s core. -/
theorem forced_prime {c Tnext p total : ℝ} (hmax : total ≤ Tnext - 1 / p) (hmass : c ≤ total) :
    1 / p ≤ Tnext - c := by linarith

/-- **The threshold pushes the level.** `x + 1/x` is strictly increasing above `1`, so a mass
`σ(a) > t` forces the union mass past `t + 1/t`. With `t = t_n` solving `t + 1/t = T_n`, this is
`prop:barthreshold`: exceeding `t_n` forces `|U| ≥ n+1` by extremality. -/
theorem threshold_pushes {sa sb t : ℝ} (ht1 : 1 < t) (hgt : t < sa) (hprod : sa * sb = 1) :
    t + 1 / t < sa + sb := by
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
  have hsa : (0 : ℝ) < sa := lt_trans ht0 hgt
  have hb : sb = 1 / sa := by field_simp; linear_combination hprod
  subst hb
  have hsat : (1 : ℝ) < sa * t := by nlinarith [hgt, ht1, ht0]
  have key : (sa + 1 / sa) - (t + 1 / t) = (sa - t) * (sa * t - 1) / (sa * t) := by
    field_simp; ring
  have hpos : 0 < (sa - t) * (sa * t - 1) / (sa * t) :=
    div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hsa ht0)
  linarith [key, hpos]

/-- **How many rungs.** Positivity of the two masses of a Pythagorean pair gives `-t < k ≤ 0` for
the integer rung index, and the level pins `t ≤ T`. So `k` is bounded below by `1 - ⌈T⌉`, hence
takes at most `⌈T⌉` values. With `T = t_n` this is `prop:rungcount`: two rungs while `t_n < 2`,
that is while `T_n < 5/2`, that is for every level up to `1412`. -/
theorem rung_floor {t T : ℝ} {k : ℤ} (hk : -t < (k : ℝ)) (hT : t ≤ T) : 1 - ⌈T⌉ ≤ k := by
  have h : -k < ⌈T⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
  omega

/-- **A ladder rung never overshoots.** Choosing `p ≥ 1/d` leaves the deficit nonnegative and
strictly smaller. This is the invariant that makes the ladder of `prop:effapprox` well defined: the
approach to the target is monotone and from one side. -/
theorem ladder_step {d p : ℝ} (hd : 0 < d) (hp : 1 / d ≤ p) : 0 ≤ d - 1 / p ∧ d - 1 / p < d := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have h1 : 1 / p ≤ d := by
    rw [div_le_iff₀ hp0]
    rw [div_le_iff₀ hd] at hp
    linarith
  exact ⟨by linarith, by linarith [one_div_pos.mpr hp0]⟩

/-- **A ladder rung converges quadratically.** If the prime chosen is within `g` of `1/d`, the new
deficit is at most `g d²`. With `g` the local prime gap this is the squaring that makes the largest
prime of `prop:effapprox` scale like `ε^(-1/2)` rather than the greedy `ε^(-e²)`. -/
theorem ladder_quadratic {d p g : ℝ} (hd : 0 < d) (hp : 1 / d ≤ p) (hpg : p ≤ 1 / d + g)
    (_hg : 0 ≤ g) : d - 1 / p ≤ g * d ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hpd : 1 ≤ p * d := by rw [div_le_iff₀ hd] at hp; linarith
  have hub : p * d ≤ 1 + g * d := by
    have := mul_le_mul_of_nonneg_right hpg hd.le
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hd)] at this
    linarith
  have hinv : 1 / p ≤ d := by rw [div_le_iff₀ hp0]; linarith
  have key : d - 1 / p = (p * d - 1) / p := by field_simp
  rw [key, div_le_iff₀ hp0]
  nlinarith [hub, hinv, hp0, hd]

end Erdos307.Dictionary
