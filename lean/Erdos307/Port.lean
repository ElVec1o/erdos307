import Erdos307.Rigidity
import Erdos307.Frame
import Mathlib.Tactic

/-!
# Ports, and why only the value one sustains itself

Erdős \#313 -- are there infinitely many primary pseudoperfect numbers -- is studied in the recent
literature through *ports*: a pair `(R, c)`, filled by a squarefree `B` when
`Δ := c * B - R * ∂ B = 1`, where `∂` is the arithmetic derivative. By `cor:threethirteen` the
`u = 1` case of \#307's coprime relaxation is exactly that problem, and the general `u` case is the
same equation with right-hand side `u²` in place of `1`. So it is natural to ask what the machinery
built for value `1` does at value `u²`.

The recursion is indifferent to the value: appending a prime `q` to `B` sends
`Δ ↦ q * Δ - R * B`. What is *not* indifferent is which values sustain themselves. Taking `R = 1`:

* `Δ` is always coprime to `B`, because a prime of `B` dividing `Δ` would divide `∂ B`, which
  `rigidity_coprime` forbids;
* a step returns to the same value exactly when `Δ * (q - 1) = B`, so `Δ ∣ B`;
* the two together force `Δ = 1`, and then `q = B + 1`.

So **value one is the unique self-sustaining value**. That is the structural reason Sylvester's
recursion `2, 6, 42, 1806, …` produces primary pseudoperfect numbers without effort, and the reason
no analogous family exists for `u ≥ 2`: the descent for the `1`-free case has no fixed point to sit
on, which is what the failed search of `code/two_side_descent.gp` was measuring.

Paper: Corollary `cor:threethirteen`, Proposition `prop:portfixed`.
-/

namespace Erdos307

/-- **Only the value one sustains itself.** If a value `d` coprime to `b` is returned to by the port
step `d ↦ q * d - b`, then `d = 1` and the step is Sylvester's, `q = b + 1`. -/
theorem port_fixed_value {d b q : ℕ} (hcop : Nat.Coprime d b) (hq : 1 ≤ q)
    (hrec : q * d = b + d) : d = 1 ∧ q = b + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
  have hdvd : d ∣ b := ⟨k, by nlinarith [hrec]⟩
  have hd1 : d = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd dvd_rfl hdvd)
  refine ⟨hd1, ?_⟩
  subst hd1
  omega

/-- **Period two.** `prop:portfixed` is sharp at period one only: a two-step orbit
`Δ ↦ q₁Δ - B ↦ Δ` is possible above the value `1`, and requires exactly `Δ ∣ q₁ + q₂`. Such orbits
do occur at `c = 1` --- `B = 33` gives `Δ : 19 ↦ 5 ↦ 19` with `q₁ = 2`, `q₂ = 17` --- but they are
single events, not families: returning a second time needs a fresh pair, since the condition ties
the primes to `B`. -/
theorem port_period_two {d b q₁ q₂ : ℕ} (hd : 0 < d) (hcop : Nat.Coprime d b)
    (hrec : q₁ * q₂ * d = d + b * (q₁ + q₂)) : d ∣ q₁ + q₂ := by
  have h1 : 1 ≤ q₁ * q₂ := by
    by_contra hc
    push_neg at hc
    interval_cases h : (q₁ * q₂) <;> omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h1
  have h : d ∣ b * (q₁ + q₂) := ⟨k, by rw [hk] at hrec; nlinarith [hrec]⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop h

/-- **The balanced splits are exactly the forbidden ones.** `thm:frame` needs
`Δ = D(1 - σ(P₀)σ(Q₀))` positive, so a split of the base must have `σ(P₀)σ(Q₀) < 1`. Since
`σ(P₀) + σ(Q₀)` is fixed at `σ(S)`, the product is a downward parabola in `σ(P₀)`, maximal at the
midpoint; so admissible splits lie strictly *outside* the base's own mass window `[1/t, t]`, and the
mass-balanced splits — where one would look first — are precisely excluded.

This is the exact complement of `Erdos307.mass_window`, which puts the mass of a *solution* inside
the window of the full support. -/
theorem split_outside_window {x y s t : ℚ} (hsum : x + y = s) (hprod : x * y < 1)
    (ht : 0 < t) (hroot : t ^ 2 - s * t + 1 = 0) : x < 1 / t ∨ t < x := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hy : y = s - x := by linarith
  subst hy
  have hq : 0 < x ^ 2 - s * x + 1 := by nlinarith [hprod]
  have h1 : (1 : ℚ) / t = s - t := by
    field_simp
    linear_combination hroot
  have hfac : 0 < (x - t) * (x - 1 / t) := by
    rw [h1]
    nlinarith [hq, hroot]
  rcases lt_trichotomy x (1 / t) with h | h | h
  · exact Or.inl h
  · exfalso; rw [h] at hfac; simp at hfac
  · right
    by_contra hc
    push_neg at hc
    nlinarith [hfac, hc, h]

end Erdos307
