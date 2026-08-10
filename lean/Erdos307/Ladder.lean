import Erdos307.Pythagorean

/-!
# The deviation ladder, and why the rung is a parity rather than a choice

`prop:ladder` and `cor:kdetermined`.

A Pythagorean pair `(a, b)` with `a < b` carries an integer parameter

  `k = σ(a) - b/a = a/b - σ(b)`,

and `k = 0` is exactly the (open) two-cycle case. The ladder of rungs `k = 0, -1, -2, …` is what the
single-integer test of `prop:pyth` actually sees, and the point of this file is that it is finite,
that every rung is as rigid as `k = 0`, and that at the masses which occur the rung is *determined*
by a parity rather than free.

* `k_nonpos`: `k ≤ 0`. From `b' = a - bk > 0` and `b > a ≥ 1`: a positive `k` would make
  `b' ≤ a - b < 0`.
* `rung_cross`: each rung is `(σ(a) - k)(σ(b) + k) = 1`, a shifted copy of the cross-match `st = 1`.
  So every rung is exactly as rigid as `k = 0`; no rung is structurally easier.
* `rung_mass_indep`: `σ(a) + σ(b) = a/b + b/a`, **independent of `k`**. This is the reason
  `cor:emptytest` holds on *every* rung rather than only on the two-cycle one: the whole ladder is
  empty below `10^112`, so the invariant `k(N)` lives on a domain that is empty there.
* `rung_minus_one`: on `k = -1` the equations read `a' = b - a`, `b' = a + b`, and
  `a'² + b'² = 2(a² + b²)`: the derivative acts on `z = a + bi` as the orientation-reversing
  `√2`-similarity `z ↦ (-1+i)z̄`.
* `rung_parity_mixed` and `rung_parity_odd`: `prop:ladder`(2). If exactly one member is even then
  `k ≡ ω(odd member) (mod 2)`; if both are odd then `k ≡ ω(a) + 1 (mod 2)`. These are the parity law
  `m' ≡ ω(m)` of `Mod8.parity_law` pushed through the rung equations.
* `k_determined`: `cor:kdetermined`. At masses below `5/2` only `k ∈ {0, -1}` survives, and then the
  parity *decides* which. So at those masses the single-integer test together with one parity check
  is **equivalent** to \#307, not merely necessary: a squarefree `N` passing the test whose splitting
  has the right `ω`-parity *is* a two-cycle. In particular the finite verifications at level 59 and
  60 are decisive in both directions, since that whole regime has masses in `(2, 2.00235]`.

What is not formalised: that mass below `5/2` forces `k ∈ {0,-1}`, which needs the bound
`|k| < min(b/a, σ(b))` together with the numeric range of `σ` at those scales; it enters
`k_determined` as the hypothesis `hk`. Bado's uniqueness of the splitting, which makes `k(N)` a
well-defined invariant of `N`, is cited.

Paper: Proposition `prop:ladder`, Corollary `cor:kdetermined`.
-/

namespace Erdos307

/-! ### The ladder is bounded above by zero -/

/-- **`prop:ladder`(1).** `k ≤ 0`. A positive `k` would force `b' = a - bk ≤ a - b < 0`. -/
theorem k_nonpos {a b bd k : ℤ} (ha : 0 < a) (hab : a < b) (hbd : 0 < bd)
    (h : bd = a - b * k) : k ≤ 0 := by
  by_contra hk
  push_neg at hk
  have h1 : b ≤ b * k := le_mul_of_one_le_right (by linarith) hk
  linarith

/-! ### Every rung is as rigid as `k = 0` -/

/-- **`prop:ladder`(3), the cross-match.** With `ra = a/b` and `rb = b/a`, each rung is
`(σ(a) - k)(σ(b) + k) = 1`, a shifted copy of `st = 1`. -/
theorem rung_cross {sa sb ra rb k : ℚ}
    (h1 : k = sa - rb) (h2 : k = ra - sb) (h : rb * ra = 1) :
    (sa - k) * (sb + k) = 1 := by
  rw [show sa - k = rb by linarith, show sb + k = ra by linarith]
  exact h

/-- **`prop:ladder`(3), the invariance.** `σ(a) + σ(b) = a/b + b/a` does not involve `k`. This is why
`cor:emptytest` holds on every rung: the mass bound that empties the two-cycle case empties the whole
ladder. -/
theorem rung_mass_indep {sa sb ra rb k : ℚ} (h1 : k = sa - rb) (h2 : k = ra - sb) :
    sa + sb = ra + rb := by linarith

/-- **`prop:ladder`(4).** On the rung `k = -1` the equations are `a' = b - a`, `b' = a + b`, and the
squares double: `a'² + b'² = 2(a² + b²)`. -/
theorem rung_minus_one (a b : ℤ) : (b - a) ^ 2 + (a + b) ^ 2 = 2 * (a ^ 2 + b ^ 2) := by ring

/-! ### The rung is a parity -/

/-- **`prop:ladder`(2), mixed parity.** If `a` is even and `b` odd, then from `b' = a - bk` the
parity of `b'`, which is `ω(b)`, equals that of `k`. -/
theorem rung_parity_mixed {a b bd k : ℤ} (ha : Even a) (hb : Odd b) (hbd : bd = a - b * k) :
    bd % 2 = k % 2 := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  subst hn; subst hm; subst hbd
  have h : n + n - (2 * m + 1) * k = 2 * (n - m * k) - k := by ring
  rw [h]
  generalize (n - m * k) = t
  omega

/-- **`prop:ladder`(2), both odd.** If `a` and `b` are both odd, then from `a' = b + ak` the parity
of `a'`, which is `ω(a)`, is that of `k + 1`. Hence also `ω(a) ≡ ω(b)`. -/
theorem rung_parity_odd {a b ad k : ℤ} (ha : Odd a) (hb : Odd b) (had : ad = b + a * k) :
    ad % 2 = (k + 1) % 2 := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  subst hn; subst hm; subst had
  have h : 2 * m + 1 + (2 * n + 1) * k = 2 * (m + n * k) + k + 1 := by ring
  rw [h]
  generalize (m + n * k) = t
  omega

/-- **`cor:kdetermined`.** Once the mass confines the ladder to `k ∈ {0, -1}`, the parity decides
which: `k = 0` exactly when the relevant `ω` is even. So at those masses the single-integer test
plus one parity check is equivalent to \#307, and a surviving candidate at level 59 or 60 would have
been a solution rather than a candidate. -/
theorem k_determined {k : ℤ} {w : ℕ} (hk : k = 0 ∨ k = -1) (hpar : k % 2 = (w : ℤ) % 2) :
    k = 0 ↔ Even w := by
  rw [Nat.even_iff]
  omega

end Erdos307
