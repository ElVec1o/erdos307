import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Ring.Basic

/-!
# The Pythagorean tail prime is bounded: `rem:lehmer` is not Lehmer-class

For a base `S` with `D = ∏S`, `N = D' = ∑_{p∈S} D/p`, `A = N + 2D`, `B = N - 2D > 0`, a Pythagorean
pair in the tail family `S ∪ {q}` is a solution of the Pell system `B x² - A y² = -4D²` with
`q = (x² - D)/A = (y² - D)/B` a positive prime. The paper reads the surviving question as the
primality of a term `q_n` of the *exponential* Pell orbit, a Lehmer/Mersenne question, and
`rem:whatisleft` names that orbit as the only live branch of #307.

**It is not exponential.** The orbit is genuinely infinite and both square conditions do hold along
all of it, but no term past a fixed bound can be prime. The reason is that `A - B = 4D` *exactly*:

`x² - y² = (A - B) q = 4Dq`, so `(x - y)(x + y) = 4Dq`.

A prime `q ∤ 2D` divides exactly one factor, so `x + y = qm` and `x - y = c` with `mc = 4D`; the
other case returns the same `x`. That pins `2xm = qm² + 4D`, and squaring against `x² = Aq + D`
collapses everything to a quadratic in `q`:

`q²m² - 4Nq + c² - 4D = 0`   (`tail_quadratic`)

whose discriminant condition is `(qm² - 2N)² = 4(AB + Dm²)` (`tail_discriminant`), so
`q = 2(N ± k)/m²` with `k² = AB + Dm²` and `m ∣ 4D`. Dropping `q²m² ≥ q²` and `c² ≥ 0` gives the
bound outright:

`q ≤ N`    (`tail_bound_sharp`; `tail_bound` gives the weaker `q ≤ 4N` from `m ≥ 1` alone).

So the Pythagorean tail primes of a base form a **finite, explicitly parametrised** set: a search
over the divisors of `4D`, not a primality question along an exponential sequence. Two consequences,
both in the paper:

* `rem:lehmer`'s Lehmer/Mersenne framing is withdrawn. The exponential orbit contributes nothing
  past its bounded initial segment. Checked in `code/tailbound.gp` on the orbit of the base
  `D = 1, N = 7` (bound `4N = 28`): `q₁ = 7` is prime, and `q₂ = 741895`, `q₃ = 76921173511`, and
  every later term factors, while both square conditions continue to hold along the whole orbit.
* The count changes sign. The number of admissible `m` is heuristically
  `∑_{m ∣ 4D} (AB + Dm²)^{-1/2} ≈ D^{-1/2} ∑_{m ∣ 4D} 1/m`, which on the first immune base is
  `2.4 × 10⁻⁵⁶` and `< 10⁻³⁸` summed over all 34 immune families. So the finite search is expected
  to be empty, which reverses the "weakly favours yes" reading of `rem:killcount` on exactly the
  families that reading was about.

The parametrisation was checked sound *and complete* against exhaustive search on 1200 bases with
zero mismatches (`code/tailbound.gp`); no prime tail escapes it.

Everything below is integer algebra, with no arithmetic-derivative content: the hypotheses record
what a Pythagorean pair supplies, and the conclusions are what follows from `A - B = 4D` alone.

Paper: Proposition `prop:tailbound`, Remark `rem:notlehmer`, Remark `rem:lehmer`, Remark
`rem:whatisleft`, Remark `rem:killcount`, Remark `rem:tier60`.
-/

namespace Erdos307

/-- **The factorisation.** `A - B = 4D` exactly, so the two square conditions subtract to
`x² - y² = 4Dq`. Writing that as `(x+y)(x-y)` and cancelling `q` gives `mc = 4D`: the cofactors of
the split a prime `q` forces are a factorisation of `4D`, which is what makes the search finite.

This is the one place the identity `A - B = 4D` is used, and it is the whole reason the orbit is not
Lehmer-class. -/
theorem tail_factor {D N q m c x y : ℤ} (hq : q ≠ 0)
    (hx : x ^ 2 = (N + 2 * D) * q + D)
    (hy : y ^ 2 = (N - 2 * D) * q + D)
    (hsum : x + y = q * m) (hdiff : x - y = c) :
    m * c = 4 * D := by
  have h : q * (m * c) = q * (4 * D) := by
    have hxy : (x + y) * (x - y) = 4 * D * q := by
      have : x ^ 2 - y ^ 2 = 4 * D * q := by rw [hx, hy]; ring
      linarith [sq_nonneg x, this, (by ring : (x + y) * (x - y) = x ^ 2 - y ^ 2)]
    rw [hsum, hdiff] at hxy; linarith [hxy]
  exact mul_left_cancel₀ hq h

/-- **The collapse.** A Pythagorean pair with `x + y = qm` and `x - y = c` satisfies a quadratic in
`q` with coefficients built from `N`, `m`, `c`, `D` alone.

The hypotheses are exactly the two square conditions `x² = Aq + D`, `y² = Bq + D` written with
`A = N + 2D` and `B = N - 2D`, together with the split of `4Dq = (x-y)(x+y)` that a prime `q`
forces. Everything else is `tail_factor` and one squaring. -/
theorem tail_quadratic {D N q m c x y : ℤ} (hm : m ≠ 0) (hq : q ≠ 0)
    (hx : x ^ 2 = (N + 2 * D) * q + D)
    (hy : y ^ 2 = (N - 2 * D) * q + D)
    (hsum : x + y = q * m) (hdiff : x - y = c) :
    q ^ 2 * m ^ 2 - 4 * N * q + c ^ 2 - 4 * D = 0 := by
  have hmc : m * c = 4 * D := tail_factor hq hx hy hsum hdiff
  -- `2xm = qm² + cm = qm² + 4D`
  have h2x : 2 * x * m = q * m ^ 2 + 4 * D := by
    have hx2 : 2 * x = q * m + c := by linarith
    calc 2 * x * m = (q * m + c) * m := by rw [hx2]
      _ = q * m ^ 2 + m * c := by ring
      _ = q * m ^ 2 + 4 * D := by rw [hmc]
  -- square it, substitute the plus-square, and use `16D² = (mc)²`
  have key : m ^ 2 * (q ^ 2 * m ^ 2 - 4 * N * q + c ^ 2 - 4 * D) = 0 := by
    have hsq : (2 * x * m) ^ 2 = (q * m ^ 2 + 4 * D) ^ 2 := by rw [h2x]
    have h16 : (4 * D) ^ 2 = m ^ 2 * c ^ 2 := by rw [← hmc]; ring
    nlinarith [hsq, hx, h16, sq_nonneg m]
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  exact (mul_eq_zero.mp key).resolve_left hm2

/-- **The discriminant.** The quadratic of `tail_quadratic` is soluble exactly when `AB + Dm²` is a
square, where `AB = N² - 4D²`. This is the parametrisation `q = 2(N ± k)/m²` with `k² = AB + Dm²`,
and it is what makes the tail set a finite search over the divisors `m ∣ 4D`. -/
theorem tail_discriminant {D N q m c : ℤ}
    (heq : q ^ 2 * m ^ 2 - 4 * N * q + c ^ 2 - 4 * D = 0) (hmc : m * c = 4 * D) :
    (q * m ^ 2 - 2 * N) ^ 2 = 4 * ((N ^ 2 - 4 * D ^ 2) + D * m ^ 2) := by
  have h16 : (4 * D) ^ 2 = m ^ 2 * c ^ 2 := by rw [← hmc]; ring
  nlinarith [heq, h16]

/-- **The bound.** Any prime tail is at most `4N`. Only `m ≥ 1`, `c² ≥ 0` and `D < N` are used, so
the exponential Pell orbit cannot supply a prime past this point however far it runs.

`D < N` is automatic in the intended setting: `N = D·σ(S)` and an admissible base has `σ(S) > 2`.
Positivity of `D` is *not* needed, so the bound also covers the degenerate bases. -/
theorem tail_bound {D N q m c : ℤ} (hq : 0 < q) (hm : 1 ≤ m) (hDN : D < N)
    (heq : q ^ 2 * m ^ 2 - 4 * N * q + c ^ 2 - 4 * D = 0) :
    q ≤ 4 * N := by
  by_contra hgt
  push Not at hgt
  have hm1 : 1 ≤ m ^ 2 := by nlinarith
  have h1 : q ^ 2 ≤ q ^ 2 * m ^ 2 := by nlinarith [sq_nonneg q]
  -- `4Nq = q²m² + c² - 4D ≥ q² - 4D`, so `q² ≤ 4Nq + 4D < 4Nq + q`, forcing `q < 4N + 1`
  nlinarith [sq_nonneg c, h1, heq, hgt, hDN]

/-- **The multiplier `m` is even.** In the factorisation `x+y = qm`, `x-y = c` of
`(x+y)(x-y) = 4Dq`, the two factors have equal parity, and if both were odd their product would be
odd while `4Dq` is even. So both are even, and since `q` is odd this forces `2 ∣ m`. The recorded
proof of `tail_bound` uses only `m ≥ 1`; this is what upgrades it to `m ≥ 2`. -/
theorem tail_m_even {D q m c x : ℤ} (hq : q % 2 = 1)
    (hmc : m * c = 4 * D) (hx : q * m + c = 2 * x) : m % 2 = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ : ∃ i, q = 2 * i + 1 := ⟨q / 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
  have hqm : q * m = 2 * (2 * i * j + i + j) + 1 := by subst hi hj; ring
  have hc : c = 2 * (x - (2 * i * j + i + j)) - 1 := by omega
  obtain ⟨A, hA⟩ : ∃ A : ℤ, 2 * A - 1 = 4 * D :=
    ⟨2 * j * (x - (2 * i * j + i + j)) - j + (x - (2 * i * j + i + j)),
     by rw [← hmc, hj, hc]; ring⟩
  omega

/-- **The sharpened bound.** With `m ≥ 2`, which `tail_m_even` supplies, the same identity gives
`q ≤ N` in place of the recorded `q ≤ 4N` -- a factor of four. The proof is the recorded one with
`m² ≥ 4` in place of `m² ≥ 1`: `4Nq = q²m² + c² - 4D ≥ 4q² - 4D`, so `Nq ≥ q² - D`, and `q ≥ N+1`
would give `q² - Nq - D ≥ q - D > 0` since `D < N < q`. -/
theorem tail_bound_sharp {D N q m c : ℤ} (hq : 0 < q) (hm : 2 ≤ m) (hDN : D < N)
    (heq : q ^ 2 * m ^ 2 - 4 * N * q + c ^ 2 - 4 * D = 0) :
    q ≤ N := by
  by_contra hgt
  push Not at hgt
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  have h1 : 4 * q ^ 2 ≤ q ^ 2 * m ^ 2 := by nlinarith [sq_nonneg q]
  nlinarith [sq_nonneg c, h1, heq, hgt, hDN]

/-- **What the three steps say together.** From the two square conditions and the factorisation a
prime `q` forces, the tail is bounded by `4N` and its value is pinned by the discriminant identity.
Stated as one theorem so the bound and the parametrisation cannot drift apart: the second component
is what makes the search finite, and the first is what makes it terminate. -/
theorem tail_finite {D N q m c x y : ℤ} (hm : 1 ≤ m) (hq : 0 < q) (hDN : D < N)
    (hx : x ^ 2 = (N + 2 * D) * q + D)
    (hy : y ^ 2 = (N - 2 * D) * q + D)
    (hsum : x + y = q * m) (hdiff : x - y = c) :
    q ≤ 4 * N ∧ (q * m ^ 2 - 2 * N) ^ 2 = 4 * ((N ^ 2 - 4 * D ^ 2) + D * m ^ 2) := by
  have hm0 : m ≠ 0 := by omega
  have hq0 : q ≠ 0 := hq.ne'
  have hmc : m * c = 4 * D := tail_factor hq0 hx hy hsum hdiff
  have heq := tail_quadratic hm0 hq0 hx hy hsum hdiff
  exact ⟨tail_bound hq hm hDN heq, tail_discriminant heq hmc⟩

/-! ### Why the finite search cannot be sieved cheaply -/

/-- **No local obstruction at any prime dividing `D`.** The search of `prop:tailbound` asks whether
`AB + Dm²` is a perfect square, with `AB = N² - 4D²`. For any `ℓ ∣ D` the value differs from `N²` by
`D(m² - 4D)`, which `ℓ` divides:

`(AB + Dm²) - N² = D(m² - 4D)`.

So `AB + Dm² ≡ N² (mod ℓ)` for **every** `m`: a square residue, always. Since rigidity gives
`gcd(D, N) = 1`, `ℓ` does not divide `2N`, and `hensel_lift_identity` below lifts the root to every
power of `ℓ`.

This is the analogue of `prop:localcomplete` for this formulation, and it has a sharp practical
consequence: a modular sieve of the tail search must use primes coprime to `2D`. Because `D` contains
every prime up to `167`, the classical `64/63/65/11` pre-filter for perfect squares rejects nothing
at all here. Measured on the first immune base: `75%` pass rate mod `64`, `100%` mod `63`, against
`18.75%` and `25.4%` for a uniform value. `code/tailsearch.rs` therefore filters on primes not
dividing `2D`. -/
theorem tail_value_sub_sq (D N m : ℤ) :
    ((N ^ 2 - 4 * D ^ 2) + D * m ^ 2) - N ^ 2 = D * (m ^ 2 - 4 * D) := by ring

/-- The divisibility form: every prime dividing `D` sees `AB + Dm²` as the square `N²`. -/
theorem tail_value_mod_dvd {ℓ D : ℤ} (N m : ℤ) (h : ℓ ∣ D) :
    ℓ ∣ ((N ^ 2 - 4 * D ^ 2) + D * m ^ 2) - N ^ 2 := by
  rw [tail_value_sub_sq]; exact h.mul_right _

/-- **The lifting step.** If `x² ≡ c` modulo `ℓ^(i+1)` with defect `c - x² = s·ℓ^(i+1)`, and `t`
solves `s - 2xt ≡ 0 (mod ℓ)` (possible whenever `2x` is invertible mod `ℓ`, which holds here since
`ℓ` is odd and `ℓ ∤ N`), then `x + t·ℓ^(i+1)` is a root one power further:

`c - (x + t·ℓ^(i+1))² = ℓ^(i+2) · (u - t²·ℓ^i)`.

Pure ring identity. `hensel_all_powers` runs the induction it powers. -/
theorem hensel_lift_identity (c x s t u ℓ : ℤ) (i : ℕ)
    (hdef : c - x ^ 2 = s * ℓ ^ (i + 1)) (hsol : s - 2 * x * t = u * ℓ) :
    c - (x + t * ℓ ^ (i + 1)) ^ 2 = ℓ ^ (i + 2) * (u - t ^ 2 * ℓ ^ i) := by
  have hs : s = u * ℓ + 2 * x * t := by linarith
  calc c - (x + t * ℓ ^ (i + 1)) ^ 2
      = (c - x ^ 2) - 2 * x * t * ℓ ^ (i + 1) - t ^ 2 * ℓ ^ (i + 1) * ℓ ^ (i + 1) := by ring
    _ = s * ℓ ^ (i + 1) - 2 * x * t * ℓ ^ (i + 1)
          - t ^ 2 * ℓ ^ (i + 1) * ℓ ^ (i + 1) := by rw [hdef]
    _ = (u * ℓ) * ℓ ^ (i + 1) - t ^ 2 * ℓ ^ (i + 1) * ℓ ^ (i + 1) := by rw [hs]; ring
    _ = ℓ ^ (i + 2) * (u - t ^ 2 * ℓ ^ i) := by ring

/-- **Hensel, all powers.** If `c` is a square modulo `ℓ` at a root `x₀` whose double is invertible
mod `ℓ` (witnessed by `w` with `ℓ ∣ 2x₀w - 1`), then `c` is a square modulo `ℓ^k` for **every** `k`,
at a root congruent to `x₀`.

Elementary and self-contained: the induction carries the congruence `ℓ ∣ x - x₀` so that `2x` stays
invertible at every stage, and each step is `hensel_lift_identity` with `t = s·w`. -/
theorem hensel_all_powers {c x₀ ℓ w : ℤ}
    (hbase : ℓ ∣ c - x₀ ^ 2) (hw : ℓ ∣ 2 * x₀ * w - 1) (k : ℕ) :
    ∃ x, ℓ ^ (k + 1) ∣ c - x ^ 2 ∧ ℓ ∣ x - x₀ := by
  induction k with
  | zero => exact ⟨x₀, by simpa using hbase, by simp⟩
  | succ k ih =>
    obtain ⟨x, hx, hx0⟩ := ih
    obtain ⟨s, hs⟩ := hx
    -- `2x` is invertible mod `ℓ` because `x ≡ x₀`
    obtain ⟨a, ha⟩ := hw
    obtain ⟨v, hv⟩ := hx0
    have hu : 2 * x * w - 1 = ℓ * (a + 2 * w * v) := by linear_combination ha + 2 * w * hv
    set u := a + 2 * w * v with hudef
    refine ⟨x + s * w * ℓ ^ (k + 1), ⟨-(s * u) - (s * w) ^ 2 * ℓ ^ k, ?_⟩, ?_⟩
    · linear_combination hs - ℓ ^ (k + 1) * s * hu
    · exact ⟨v + s * w * ℓ ^ k, by linear_combination hv⟩

/-- **No local obstruction at any prime dividing `D`, at every power.** Combining
`tail_value_mod_dvd` with `hensel_all_powers`: for `ℓ ∣ D` with `2N` invertible mod `ℓ` (which
rigidity supplies, since `gcd(D, N) = 1` and `ℓ` is odd), the search value `AB + Dm²` is a square
modulo `ℓ^k` for every `k` and every `m`.

So the tail search of `prop:tailbound` cannot be sieved at any prime dividing `D`, at any power. -/
theorem tail_no_local_obstruction {ℓ D N w : ℤ} (m : ℤ) (hD : ℓ ∣ D)
    (hw : ℓ ∣ 2 * N * w - 1) (k : ℕ) :
    ∃ x, ℓ ^ (k + 1) ∣ ((N ^ 2 - 4 * D ^ 2) + D * m ^ 2) - x ^ 2 ∧ ℓ ∣ x - N :=
  hensel_all_powers (tail_value_mod_dvd N m hD) hw k

end Erdos307
