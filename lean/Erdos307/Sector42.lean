import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The non-enumerative half of `prop:sector42`

`prop:sector42` states that no two-cycle has `a = 42q` with `q` prime and `ω(b) = 64`, so that
`|P ∪ Q| ≥ 70` in that sector. Its proof has two parts. The finite part — the exact enumeration of
`3.69 × 10¹⁰` prime sets — has no Lean-checkable form at this size and is recorded as a blocker in
`COVERAGE.md`. The *algebraic* part is formalised here, and it is the part that makes the
enumeration finite in the first place:

* `terminal_prime` — the forced-prime identity. If the support of `e` is `S ∪ {ℓ}` with `R = ∏ S`
  and `R'` the derivative sum of `S`, then the sector equation `42e - 41e' = 1764` forces
  `ℓ · (42R - 41R') = 41R + 1764`. So `ℓ` is *determined* by the other primes: it is a quotient of
  two integers built from `S`, or there is no solution at all. This is what turns a search over
  `64`-element supports into a search over `63`-element ones with an integrality test.
* `terminal_denom_pos` — that identity forces `42R - 41R' > 0`, the sign condition the enumerator
  tests before dividing.
* `case_split` — the mass bound behind "at most two primes exceed `1229`": if `k` primes carry mass
  at least `T` and `m` of them are at least `B`, then the other `k - m` carry at least `T - m/B`.
  Instantiated at `T = 42/41`, `B = 1231`, `m = 3` against `S₆₁ < 42/41` this is the exclusion of
  `m ≥ 3`, the numerical half of which is the exact rational computation in
  `code/sector42_k64.gp` rather than a Lean statement.
* `parity_step` — from `ω(e) ≠ 64`, `ω(e) ≥ 64` and `ω(e)` even, conclude `ω(e) ≥ 66`; and the
  count `|P ∪ Q| = 4 + ω(e)`.

Nothing here is `sorry`-free by accident: the file states the algebra only, and the two arithmetic
facts it does not prove (`ω(e) ≥ 64`, and the enumeration returning nothing) are hypotheses of
`sector42_conclusion`, so what the finite computation must supply is visible in the statement.

Paper: Proposition `prop:sector42`, Remark `rem:sectordprime`.
-/

namespace Erdos307

/-- **The forced-prime identity.** With `e = R * ℓ` and `e' = R' * ℓ + R` (the derivative of a
product with `ℓ ∤ R`), the sector equation `42e - 41e' = 1764` is equivalent to
`ℓ * (42R - 41R') = 41R + 1764`. Stated over `ℤ` so no positivity is assumed. -/
theorem terminal_prime (R R' l : ℤ) (h : 42 * (R * l) - 41 * (R' * l + R) = 1764) :
    l * (42 * R - 41 * R') = 41 * R + 1764 := by linarith [h, mul_comm R l]

/-- The converse: the identity gives back the sector equation. Together with `terminal_prime` this
says the enumerator's test is not merely necessary but exact. -/
theorem terminal_prime' (R R' l : ℤ) (h : l * (42 * R - 41 * R') = 41 * R + 1764) :
    42 * (R * l) - 41 * (R' * l + R) = 1764 := by linarith [h, mul_comm R l]

/-- **The sign condition.** A positive `ℓ` forces the denominator `42R - 41R'` to be positive, since
`41R + 1764 > 0` whenever `R > 0`. This is the test the enumerator applies before dividing. -/
theorem terminal_denom_pos (R R' l : ℤ) (hR : 0 < R) (hl : 0 < l)
    (h : l * (42 * R - 41 * R') = 41 * R + 1764) : 0 < 42 * R - 41 * R' := by
  rcases lt_trichotomy (42 * R - 41 * R') 0 with hneg | hzero | hpos
  · exfalso; nlinarith
  · exfalso; rw [hzero, mul_zero] at h; linarith
  · exact hpos

/-- **The case split.** If `k` primes carry total mass at least `T`, and `m` of them are each at
least `B > 0` (so each contributes at most `1/B`), the remaining `k - m` carry mass at least
`T - m/B`. The exclusion of `m ≥ 3` at `d = 42` is this with `T = 42/41`, `B = 1231`, together with
the exact inequality `S₆₁ + 3/1231 < 42/41` verified in `code/sector42_k64.gp`. -/
theorem case_split {T small large : ℚ} {m B : ℚ}
    (hmass : T ≤ small + large) (hlarge : large ≤ m / B) : T - m / B ≤ small := by
  linarith

/-- **The parity step.** `ω(e)` even, `ω(e) ≥ 64` and `ω(e) ≠ 64` give `ω(e) ≥ 66`. -/
theorem parity_step {w : ℕ} (heven : Even w) (hge : 64 ≤ w) (hne : w ≠ 64) : 66 ≤ w := by
  rcases heven with ⟨t, ht⟩
  subst ht
  omega

/-- **The conclusion of `prop:sector42`**, with the two facts the finite computations supply left as
explicit hypotheses: `hbado` is Bado's `ω(e) ≥ 64` (his residue certificate, independently re-run),
and `henum` is the exact enumeration of `code/sector42_k64.rs` returning no solution. `hcount` is
`|P ∪ Q| = 4 + ω(e)`, which holds because `q ∉ {2,3,7}` and `q ∤ e`. -/
theorem sector42_conclusion {w U : ℕ} (heven : Even w) (hbado : 64 ≤ w) (henum : w ≠ 64)
    (hcount : U = 4 + w) : 70 ≤ U := by
  have := parity_step heven hbado henum
  omega

end Erdos307
