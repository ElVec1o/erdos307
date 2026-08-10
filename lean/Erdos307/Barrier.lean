import Mathlib
import Erdos307.Rigidity

/-!
# Erdős #307 — Barrier (Lean targets T3, T4)

Let `(P,Q)` be a solution, `s = ∑_{p∈P} 1/p`, `t = ∑_{q∈Q} 1/q`, so `s·t = 1`.
Write `U = P ∪ Q` (a disjoint union by rigidity), `R = ∏_{p∈U} p = D_P·D_Q`, and
`T = ∑_{p∈U} 1/p = s + t`.

**T3.** `s + t > 2` (strict AM–GM, `reciprocal_sum_gt_two`), and since the reciprocal sum of the
59 smallest primes is the *first* prime-reciprocal sum to exceed `2`, any solution has
`|P ∪ Q| ≥ 59`.  The two rational facts grounding the number 59 are `recipSum58_lt_two` /
`recipSum59_gt_two` (`norm_num` on the exact 113-digit integers).

**T4.** Combining `R = s·D_P²` (rigidity), `s ≤ T`, and the extremal ratio bound
`R/T ≥ Π₅₉/T₅₉ = 4.38·10¹¹²`, one gets `D_P² ≥ 4·10¹¹²`, i.e. `D_P ≥ 2·10⁵⁶`
(`barrier`, via `barrier_algebraic` + `barrier_numeric`).

## Note on the abstract `barrier`
Everything here is `sorry`-free.  `barrier` isolates the algebraic/explicit-rational core of T3/T4,
taking the smallest-primes extremality as the explicit hypothesis `hRatio : (4*10^112) * T ≤ R` so
the dependency is visible.  That extremality is *now proven* (`Erdos307.Extremal`,
`prod_first_primes_le`/`recipSum_le_first_primes`) and the hypothesis is discharged in
`Erdos307.Closed` (`erdos307_barrier_closed`), which states the barrier over genuine prime sets with
no extremality hypothesis.

Paper: Lemma `lem:amgm` (T3), Theorem `thm:barrier` (T4), Lemma `lem:59`.
-/

namespace Erdos307

open Finset

/-- **T3 (strict AM–GM).** If `s·t = 1` with `s > 0` and `s ≠ 1`, then `s + t > 2`. -/
theorem reciprocal_sum_gt_two {s t : ℚ} (hs : 0 < s) (hst : s * t = 1) (hne : s ≠ 1) :
    2 < s + t := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < (s - 1) ^ 2 := by positivity
  nlinarith [hsq, hst, hs, mul_pos hs hs]

/-! ## Exact constants for the first 58 / 59 primes

`P59 = ∏ (first 59 primes)`, `N59 = ∑_{p∈first59} P59/p` (the cofactor sum), so the reciprocal
sum of the first 59 primes is exactly `N59 / P59`; similarly for 58. -/

/-- Product of the first 58 primes. -/
def P58 : ℕ := 316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070

/-- Cofactor sum of the first 58 primes (numerator of `∑_{first 58} 1/p`). -/
def N58 : ℕ := 632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409

/-- Product of the first 59 primes. -/
def P59 : ℕ := 87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390

/-- Cofactor sum of the first 59 primes (numerator of `∑_{first 59} 1/p`). -/
def N59 : ℕ := 175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363

/-- The reciprocal sum of the first **58** primes is `< 2` (so 58 primes never reach `2`):
`N58 / P58 = 1.99874… < 2`. -/
theorem recipSum58_lt_two : N58 < 2 * P58 := by
  unfold N58 P58; norm_num

/-- The reciprocal sum of the first **59** primes is `> 2`:
`N59 / P59 = 2.00235… > 2`.  Hence 59 is the least number of primes whose reciprocals can reach 2,
and `|P ∪ Q| ≥ 59`. -/
theorem recipSum59_gt_two : 2 * P59 < N59 := by
  unfold N59 P59; norm_num

/-- **Numeric heart of the Barrier.** `Π₅₉² ≥ (4·10¹¹²)·N₅₉`, i.e. `Π₅₉ / T₅₉ = Π₅₉²/N₅₉ ≥
4·10¹¹²`.  (Exact value `4.3806·10¹¹²`; we keep the round bound `4·10¹¹²` ⇒ `D_P ≥ 2·10⁵⁶`.) -/
theorem barrier_numeric : 4 * 10 ^ 112 * N59 ≤ P59 ^ 2 := by
  unfold N59 P59; norm_num

/-- **Algebraic core of T4.** If `D_P²·s = R`, `0 < T`, `s ≤ T`, and `B·T ≤ R`, then `B ≤ D_P²`.
(Reads as: `D_P² = R/s ≥ R/T ≥ B`, with all divisions cleared.) -/
theorem barrier_algebraic {DP s T R B : ℚ}
    (hsT : s ≤ T) (hT : 0 < T) (hR : DP ^ 2 * s = R) (hBT : B * T ≤ R) :
    B ≤ DP ^ 2 := by
  nlinarith [hsT, hT, hR, hBT, sq_nonneg DP,
    mul_le_mul_of_nonneg_left hsT (sq_nonneg DP)]

/-- **T4 (Barrier).** With `R = ∏_{p∈P∪Q} p = s·D_P²` (rigidity), `s ≤ T = ∑_{p∈P∪Q} 1/p`
(immediate, since `T = s + t` and `t > 0`), and the extremal ratio bound
`(4·10¹¹²)·T ≤ R` (smallest-primes extremality + `|P∪Q| ≥ 59` + `barrier_numeric`):
the minimal side satisfies `D_P² ≥ 4·10¹¹²`, hence `D_P ≥ 2·10⁵⁶`. -/
theorem barrier {DP s T R : ℚ}
    (hT : 0 < T) (hsT : s ≤ T)
    (hRatio : (4 * 10 ^ 112 : ℚ) * T ≤ R)
    (hR : R = s * DP ^ 2) :
    (4 * 10 ^ 112 : ℚ) ≤ DP ^ 2 :=
  barrier_algebraic hsT hT (by rw [hR]; ring) hRatio

end Erdos307
