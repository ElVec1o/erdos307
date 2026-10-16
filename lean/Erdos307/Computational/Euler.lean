import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Euler's criterion as a table lookup

`eulerSym ℓ x = x^(ℓ/2) mod ℓ` read as `0, 1, -1`; `legendreSym_eq_eulerSym` identifies it with
`legendreSym ℓ x` for an odd prime `ℓ`. The compiled pair-sector leaf reads precomputed tables of this
function; the lemma is why the table lookup is the Legendre symbol.

Paper: Proposition `prop:pairclosed` (the character test of the computation).
-/

namespace Erdos307

/-- `x^(ℓ/2) mod ℓ`, as `0`, `1`, or `-1`. -/
def eulerSym (ℓ x : ℕ) : ℤ :=
  let r := x ^ (ℓ / 2) % ℓ
  if r = 0 then 0 else if r = 1 then 1 else -1

theorem legendreSym_eq_eulerSym {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (x : ℕ) :
    legendreSym ℓ (x : ℤ) = eulerSym ℓ (x % ℓ) := by
  have hp : ℓ.Prime := Fact.out
  have hℓ2 : 2 ≤ ℓ := hp.two_le
  have hlt : 1 < ℓ := hp.one_lt
  have hhalf : 0 < ℓ / 2 := by
    have : 3 ≤ ℓ := by omega
    omega
  -- the `ZMod ℓ` value of the pure power
  have hcast : (((x % ℓ) ^ (ℓ / 2) % ℓ : ℕ) : ZMod ℓ) = (x : ZMod ℓ) ^ (ℓ / 2) := by
    rw [ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_mod]
  unfold eulerSym
  simp only []
  by_cases hx0 : (x : ZMod ℓ) = 0
  · have h1 : legendreSym ℓ (x : ℤ) = 0 := by
      rw [legendreSym.eq_zero_iff]; simpa using hx0
    have h2 : (x % ℓ) ^ (ℓ / 2) % ℓ = 0 := by
      have : x % ℓ = 0 := by
        exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff x ℓ).1 hx0)
      rw [this, zero_pow hhalf.ne']; simp
    rw [h1, if_pos h2]
  · have hne : ((x : ℤ) : ZMod ℓ) ≠ 0 := by simpa using hx0
    have hpow0 : (x : ZMod ℓ) ^ (ℓ / 2) ≠ 0 := pow_ne_zero _ hx0
    have hr0 : (x % ℓ) ^ (ℓ / 2) % ℓ ≠ 0 := by
      intro h; apply hpow0; rw [← hcast, h]; simp
    have hrlt : (x % ℓ) ^ (ℓ / 2) % ℓ < ℓ := Nat.mod_lt _ (by omega)
    rw [if_neg hr0]
    by_cases hsq : IsSquare (x : ZMod ℓ)
    · have h1 : legendreSym ℓ (x : ℤ) = 1 := by
        rw [legendreSym.eq_one_iff ℓ hne]; simpa using hsq
      have hpow1 : (x : ZMod ℓ) ^ (ℓ / 2) = 1 := (ZMod.euler_criterion ℓ hx0).1 hsq
      have h2 : (x % ℓ) ^ (ℓ / 2) % ℓ = 1 := by
        have hc : (((x % ℓ) ^ (ℓ / 2) % ℓ : ℕ) : ZMod ℓ) = ((1 : ℕ) : ZMod ℓ) := by
          rw [hcast, hpow1]; simp
        have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hc
        rwa [Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hlt] at this
      rw [h1, if_pos h2]
    · have h1 : legendreSym ℓ (x : ℤ) = -1 := by
        rw [legendreSym.eq_neg_one_iff ℓ]; simpa using hsq
      have h2 : (x % ℓ) ^ (ℓ / 2) % ℓ ≠ 1 := by
        intro h
        apply hsq
        refine (ZMod.euler_criterion ℓ hx0).2 ?_
        rw [← hcast, h]; simp
      rw [h1, if_neg h2]

end Erdos307
