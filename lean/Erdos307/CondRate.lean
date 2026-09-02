import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The detector steps of `prop:condrate`

`prop:condrate` bounds the count of squarefree `m ≤ N` with `m' - 2m` a positive square. Its
analytic half (Halász, Siegel–Walfisz, Siegel, the zero-free region, through `lem:charcancelunif`
and `lem:deficit`) is not in Mathlib and remains the blocker recorded in `COVERAGE.md`. But the
proof opens with two elementary steps that owe nothing to the analysis, and those are formalised
here, so that the star over this atom covers only the analysis.

* `deriv_ne_two_mul` — `a_m = m' - 2m` never vanishes on squarefree `m > 1`. The paper's reason is
  that `a_m = 0` forces `σ(m) = 2` exactly; the mechanism is simply that `m' = 2m` would make `m`
  divide `m'`, against `gcd(m', m) = 1` (`thm:structure`). Stated with that coprimality as the
  hypothesis it actually uses.
* `legendre_eq_one_of_sq` — if `a` is a nonzero square and `p ∤ a`, then `(a ∣ p) = 1`. This is why
  a square `a_m` can have no `-1` among its Legendre symbols, which is the whole detector.
* `detector_sum_lower` — hence, over any finite set of primes, `∑_p (a ∣ p) ≥ |P| - #{p ∈ P : p ∣ a}`,
  the inequality the second moment is built on. The proof is that every term is `1` off the divisor
  set and `≥ 0` on it.

The sieve that consumes these, and the character sums that bound the cross terms, are the analytic
part and are not here.

Paper: Proposition `prop:condrate`, Theorem `thm:a9`.
-/

namespace Erdos307

open Finset

/-- **The detector never vanishes.** If `gcd(m', m) = 1` and `m > 1`, then `m' ≠ 2m`: otherwise `m`
would divide `m'`, forcing `gcd(m', m) = m > 1`. This is the step that lets `a_m = m' - 2m` be fed
to a Legendre symbol at all. -/
theorem deriv_ne_two_mul {d m : ℤ} (hm : 1 < m) (hcop : IsCoprime d m) : d ≠ 2 * m := by
  rintro rfl
  have hdvd : m ∣ 2 * m := ⟨2, by ring⟩
  have : IsUnit m := hcop.isUnit_of_dvd' hdvd dvd_rfl
  rcases Int.isUnit_iff.mp this with h | h <;> omega

/-- **A nonzero square has Legendre symbol `1`** at every prime not dividing it. -/
theorem legendre_eq_one_of_sq (p : ℕ) [Fact (Nat.Prime p)] (a c : ℤ)
    (hsq : a = c ^ 2) (hnd : ((a : ℤ) : ZMod p) ≠ 0) : legendreSym p a = 1 := by
  rw [legendreSym.eq_one_iff p hnd]
  exact ⟨(c : ZMod p), by rw [hsq]; push_cast; ring⟩

/-- **The detector bound.** Over a finite set `P` of primes, if every term of `∑_{p ∈ P} (a ∣ p)`
is `1` except on the subset where `p ∣ a`, where it is at least `0`, then the sum is at least
`|P|` minus the size of that subset. Stated abstractly in the two facts it uses, so that no
property of `a` beyond them enters. -/
theorem detector_sum_lower {α : Type*} [DecidableEq α] (P : Finset α) (f : α → ℤ) (bad : Finset α)
    (hbad : bad ⊆ P) (hgood : ∀ p ∈ P, p ∉ bad → f p = 1) (hnonneg : ∀ p ∈ bad, 0 ≤ f p) :
    (P.card : ℤ) - bad.card ≤ ∑ p ∈ P, f p := by
  classical
  have hsplit : ∑ p ∈ P, f p = ∑ p ∈ P \ bad, f p + ∑ p ∈ bad, f p := by
    rw [← Finset.sum_sdiff hbad]
  have h1 : ∑ p ∈ P \ bad, f p = ((P \ bad).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun p hp => hgood p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2)]
    simp
  have h2 : (0 : ℤ) ≤ ∑ p ∈ bad, f p := Finset.sum_nonneg hnonneg
  have hle : bad.card ≤ P.card := Finset.card_le_card hbad
  have h3 : (((P \ bad).card : ℕ) : ℤ) = (P.card : ℤ) - (bad.card : ℤ) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hbad]
    omega
  rw [hsplit, h1, h3]
  linarith

end Erdos307
