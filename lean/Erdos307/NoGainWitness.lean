import Erdos307.Witness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The cycle condition gains under one order: a witness, not a search

`prop:nogain` bounds `N` below by `min_S max(∏S, Π_min(S)/σ(S))² σ(S)` and reports the minimum as
`10^113.2`, against the barrier `10^112.9`. The conclusion drawn is that the cycle condition buys
*nothing*, and that conclusion needs an **upper** bound on the minimum, which one witness supplies.
The exhaustive minimisation certifies the sharper claim that `113.2` is exactly the minimum; it is
not needed for the conclusion, and it was the only reason the atom was carried as a refusal.

`Π_min(S)` is itself a minimum, so bounding the expression at `S` above also needs only a witness
`T` for it: any `T` disjoint from `S` with `σ(T) ≥ 1/σ(S)` has `Π_min(S) ≤ ∏T`.

Here `S` is the optimum the search reports, the odd primes to `151` less `{3, 97}`, and `T` is the
greedy completion, `26` primes ending at `277`. Note `∏S · σ(S)` is an integer, since `σ(S)` has
denominator exactly `∏S`, so the whole bound is an integer comparison.

Paper: Proposition `prop:nogain`.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace Erdos307.NoGainWitness

open Erdos307.Witness (rsum)

/-- The optimal small-prime set: odd primes up to `151`, less `3` and `97`. -/
def Sw : List ℕ :=
  [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151]

/-- The greedy completion outside `Sw`, carrying the mass `Sw` leaves. -/
def Tw : List ℕ :=
  [2, 3, 97, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
   241, 251, 257, 263, 269, 271, 277]

theorem Sw_prime : ∀ p ∈ Sw, Nat.Prime p := by intro p hp; fin_cases hp <;> norm_num
theorem Tw_prime : ∀ q ∈ Tw, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num
theorem Sw_nodup : Sw.Nodup := by decide
theorem Tw_nodup : Tw.Nodup := by decide
theorem Sw_disjoint : ∀ p ∈ Sw, p ∉ Tw := by decide


theorem rsum_Sw : rsum Sw = 406306493414283345574880649975890612878822297373922047301 / 387146967339916112248952295926103095104270040141506089505 := by
  simp only [rsum, Sw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

theorem rsum_Tw : rsum Tw = 215887484240793774809303808355630987688924217557132262077 / 226567627037678495185405533334699321740734941163362125078 := by
  simp only [rsum, Tw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

theorem prod_Sw : (Sw.prod : ℚ) = 387146967339916112248952295926103095104270040141506089505 := by
  simp only [Sw, List.prod_cons, List.prod_nil]; norm_num

theorem prod_Tw : (Tw.prod : ℚ) = 226567627037678495185405533334699321740734941163362125078 := by
  simp only [Tw, List.prod_cons, List.prod_nil]; norm_num

/-- **The witness.** There is an admissible pair `(S, T)` at which the cycle bound is under
`10^{113.5}`, so the gain over the barrier `10^{112.9}` is under one order --- indeed under
`0.6` of one. The bound is squared so that the exponent is an integer: `227/2 = 113.5`. -/
theorem nogain_witness :
    ∃ S T : List ℕ, S.Nodup ∧ T.Nodup ∧
      (∀ p ∈ S, Nat.Prime p) ∧ (∀ q ∈ T, Nat.Prime q) ∧ (∀ p ∈ S, p ∉ T) ∧
      1 / rsum S ≤ rsum T ∧
      ((T.prod : ℚ)) ≤ (S.prod : ℚ) * rsum S ∧
      (((S.prod : ℚ)) ^ 2 * rsum S) ^ 2 < 10 ^ 227 := by
  refine ⟨Sw, Tw, Sw_nodup, Tw_nodup, Sw_prime, Tw_prime, Sw_disjoint, ?_, ?_, ?_⟩
  · rw [rsum_Sw, rsum_Tw]; norm_num
  · rw [rsum_Sw, prod_Sw, prod_Tw]; norm_num
  · rw [rsum_Sw, prod_Sw]; norm_num

end Erdos307.NoGainWitness
