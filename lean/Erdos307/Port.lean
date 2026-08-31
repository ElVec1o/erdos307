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

end Erdos307
