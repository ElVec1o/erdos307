import Erdos307.TailBound
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Bezout
import Mathlib.Tactic.LinearCombination

/-!
# The pair sector admits no congruence kill: the certificate programme ends at arity one

`prop:pairlocal`. The reciprocity certificate captures every `q`-independent congruence obstruction
of a *single-tail* family, and kills `46,483` of the `49,961` families at level `60`. It is
intrinsically arity-one, and on the pair sector it provably fails: with `α, β` the two adjoined
primes, a pair-sector member needs the two simultaneous squares

  `x² = A αβ + D(α+β)`,  `y² = B αβ + D(α+β)`,   where `A = N + 2D`, `B = N - 2D`,

and this system is locally soluble at *every* prime power. So no finite system of congruence
conditions empties any pair-sector family, and the arity barrier is a theorem rather than an
observation.

The proof runs in three regimes, and this file formalises the algebraic backbone that all three
share, together with the two regimes whose content is algebraic rather than analytic.

* **No `ℓ` pins either target to a constant.** That would need `ℓ ∣ A` and `ℓ ∣ D` at once, whence
  `ℓ ∣ N` since `N = A - 2D`, contradicting `gcd(N, D) = 1`, which is Rigidity. So the tail-kill
  mechanism is unavailable before the regimes are even entered. This is `no_pinning` and
  `no_pinning_isUnit`.

* **Regime (1), `ℓ` odd with `ℓ ∣ D`** (which covers every odd `ℓ ≤ 103`). Take `β = 1`, `x = 1`
  and `α` the unit with `(A + D)α + D = 1`. The first equation then holds by construction, and
  modulo `ℓ` the second target collapses to `N · N⁻¹ = 1`, a unit congruent to a square, so `y`
  exists. This is `regime_one_first` and `regime_one_second`.

* **Regime (2), `ℓ` odd with `ℓ ∤ 2D`.** The two conditions are secretly *one*. Setting
  `4Dm = x² - y²` and `Du = x² - Am`, the relation `A - B = 4D` gives the identity `Bm + Du = y²`
  outright, so the second equation is a consequence of the first. That collapse is
  `collapse_identity`, and it is the heart of the regime: what remains is counting `(x,y)` with
  `u² - 4m` square, which Weil's bound supplies and which is *not* formalised here.

* **Regime (3), `ℓ = 2`.** Both targets are odd and agree modulo `8`, because their difference is
  `(A - B)αβ = 4Dαβ` and `D` is even. That is `targets_agree_mod_eight`. The finite table over
  `(A mod 8, D mod 8)` showing some achievable pair makes the common target `≡ 1 (mod 8)` is a
  computation, in `code/pairlocal.py`.

One input is cited and not reproved: Weil's bound for the point count in regime (2). The second
former citation, lifting a nonsingular point from `ℓ` to `ℓ^j`, is now `square_lifts_to_prime_powers`
below, proved from `hensel_all_powers`; it is no longer assumed.

The consequence is the one that matters for the programme. Unlike the single-tail family, the pair
sector admits no congruence obstruction at all: it is a genuine two-parameter surface per base,
\#307 in miniature. Reciprocity cannot touch it, and only a direct both-squares search or a descent
argument can.

Paper: Proposition `prop:pairlocal`, Remark `rem:campaign`.
-/

namespace Erdos307

/-! ### No prime pins a target to a constant -/

/-- If `ℓ` divides both `A = N + 2D` and `D`, it divides `N`. -/
theorem no_pinning {ℓ A D N : ℤ} (hA : A = N + 2 * D) (hl : ℓ ∣ A) (hlD : ℓ ∣ D) : ℓ ∣ N := by
  have hN : N = A - 2 * D := by linear_combination -hA
  rw [hN]
  exact dvd_sub hl (hlD.mul_left 2)

/-- **The tail-kill mechanism is unavailable on the pair sector.** A prime pinning a target to a
constant would divide `N` and `D` together, and Rigidity says those are coprime; so it is a unit.
This is what forces the analysis into the three regimes rather than letting a single `ℓ` finish
the job. -/
theorem no_pinning_isUnit {ℓ A D N : ℤ} (hA : A = N + 2 * D) (hl : ℓ ∣ A) (hlD : ℓ ∣ D)
    (hcop : IsCoprime N D) : IsUnit ℓ :=
  hcop.isUnit_of_dvd' (no_pinning hA hl hlD) hlD

/-! ### The relation between the two forms -/

/-- `A - B = 4D`, the relation that drives both the collapse of regime (2) and the mod-`8`
agreement of regime (3). -/
theorem A_sub_B {A B D N : ℤ} (hA : A = N + 2 * D) (hB : B = N - 2 * D) : A - B = 4 * D := by
  rw [hA, hB]; ring

/-! ### Regime (2): the two conditions are one -/

/-- **The collapse identity.** With `4Dm = x² - y²` and `Du = x² - Am`, the relation `A - B = 4D`
gives `Bm + Du = y²` as a polynomial identity. So in regime (2) the second square condition is a
consequence of the first, and the system has one degree of freedom rather than two.

No division is needed: the identity holds over any commutative ring. -/
theorem collapse_identity {A B D m u x y : ℤ}
    (hAB : A - B = 4 * D) (hm : 4 * D * m = x ^ 2 - y ^ 2) (hu : D * u = x ^ 2 - A * m) :
    B * m + D * u = y ^ 2 := by linear_combination hu - m * hAB - hm

/-! ### Regime (1): the explicit unit -/

/-- **Regime (1), the first equation holds by construction.** With `β = 1`, `x = 1`, and `α` chosen
so that `(A + D)α + D = 1`, the first target is a square outright. -/
theorem regime_one_first {A D α : ℤ} (hα : (A + D) * α + D = 1) :
    A * (α * 1) + D * (α + 1) = 1 ^ 2 := by linear_combination hα

/-- **Regime (1), the second target is a unit congruent to a square.** Modulo `ℓ` dividing `D` one
has `A ≡ B ≡ N`, so with `Nα = 1` the second target collapses to `N · N⁻¹ = 1`. A unit square
modulo `ℓ` lifts to `ℓ^j`, giving `y`. -/
theorem regime_one_second {ℓ : ℕ} {B D N α : ZMod ℓ}
    (hB : B = N - 2 * D) (hD : D = 0) (hα : N * α = 1) :
    B * (α * 1) + D * (α + 1) = 1 ^ 2 := by
  subst hB; subst hD; linear_combination hα

/-- **The lifting input, no longer cited.** Regime (1) needs "a unit square modulo `ℓ` lifts to
`ℓ^j`", which was one of the two facts this file imported without proof. It is now discharged:
`hensel_all_powers` supplies exactly this lift, and the invertibility it requires is automatic here
because `ℓ` is an odd prime not dividing `c`.

If `ℓ` is an odd prime, `ℓ ∤ c`, and `c` is a square modulo `ℓ`, then `c` is a square modulo every
power of `ℓ`. The unit hypothesis is what makes `2x₀` invertible: `ℓ ∤ c` forces `ℓ ∤ x₀`, and `ℓ`
odd forces `ℓ ∤ 2`.

This leaves Weil's point count in regime (2) as the *only* remaining cited input of `prop:pairlocal`,
so the atom's blocker list drops from two items to one. -/
theorem square_lifts_to_prime_powers {ℓ c x₀ : ℤ} (hℓ : Prime ℓ) (hodd : ¬ (ℓ ∣ 2))
    (hc : ¬ ℓ ∣ c) (hbase : ℓ ∣ c - x₀ ^ 2) (j : ℕ) :
    ∃ x, ℓ ^ (j + 1) ∣ c - x ^ 2 := by
  -- `ℓ ∤ x₀`, else `ℓ ∣ x₀^2` and `ℓ ∣ c - x₀^2` give `ℓ ∣ c`
  have hx₀ : ¬ ℓ ∣ x₀ := by
    intro h
    have h2 : ℓ ∣ x₀ ^ 2 := h.pow (by norm_num)
    exact hc (by simpa using dvd_add hbase h2)
  have h2x : ¬ ℓ ∣ 2 * x₀ := fun h => (hℓ.2.2 2 x₀ h).elim hodd hx₀
  -- so `2x₀` is invertible mod `ℓ`
  have hcop : IsCoprime ℓ (2 * x₀) := (Prime.coprime_iff_not_dvd hℓ).mpr h2x
  obtain ⟨u, v, huv⟩ := hcop
  have hw : ℓ ∣ 2 * x₀ * v - 1 := ⟨-u, by linarith [huv]⟩
  obtain ⟨x, hx, _⟩ := hensel_all_powers hbase hw j
  exact ⟨x, hx⟩

/-- The same for the first target, so that regime (1) produces both squares at once. -/
theorem regime_one_first_mod {ℓ : ℕ} {A D N α : ZMod ℓ}
    (hA : A = N + 2 * D) (hD : D = 0) (hα : N * α = 1) :
    A * (α * 1) + D * (α + 1) = 1 ^ 2 := by
  subst hA; subst hD; linear_combination hα

/-! ### Regime (3): the two targets agree modulo 8 -/

/-- `4·(2D₁) = 0` in `ZMod 8`: the difference of the two targets vanishes because `D` is even. -/
theorem four_two_eq_zero (D1 : ZMod 8) : (4 : ZMod 8) * (2 * D1) = 0 := by
  have h : (4 : ZMod 8) * 2 = 0 := by decide
  linear_combination D1 * h

/-- **Regime (3).** Writing `D = 2D₁`, the two targets are *equal* modulo `8`, since their
difference is `(A - B)αβ = 4Dαβ = 8D₁αβ`. So one table over `(A mod 8, D mod 8)` settles both
conditions at once, and the `2`-adic layer never separates them. -/
theorem targets_agree_mod_eight {A B D1 α β : ZMod 8} (hAB : A - B = 4 * (2 * D1)) :
    A * (α * β) + (2 * D1) * (α + β) = B * (α * β) + (2 * D1) * (α + β) := by
  have hz : A - B = 0 := by rw [hAB, four_two_eq_zero]
  have : A = B := sub_eq_zero.mp hz
  rw [this]

end Erdos307
