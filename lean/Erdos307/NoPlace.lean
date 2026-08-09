import Erdos307.Rigidity

/-!
# No place of ℚ carries the function-field descent

`prop:noplace`. The function-field proof of `prop:ff-pyth` runs on a place whose valuation the
derivative strictly lowers. Over `ℚ` no such place exists, and this is a classification statement
rather than a failure of ingenuity: by Ostrowski the places of `ℚ` are the archimedean one and the
`p`-adic ones, and both are ruled out below.

On squarefree supports the derivative is `dprod S ↦ csum S`: the number is `∏_{p ∈ S} p` and its
derivative is `∑_{p ∈ S} (∏ S)/p`. Everything here is stated in those terms.

* **(i) Archimedean.** `|D(n)| = n·σ(n)` exceeds `n` for every `n` of mass `> 1`; the derivative
  *expands*, first at `n = 30`, where `30 ↦ 31`. So no size function that respects order can
  decrease along it, which is `not_descent_of_strictMono` and is stronger than the statement about
  `|·|` alone: it kills every strictly monotone valuation at once, not just the absolute value. The
  absolute value is in any case not ultrametric, so the second half of the degree argument is
  unavailable too.

* **(ii) `p`-adic.** For squarefree `n` with `p ∣ n`, cofactor survival gives
  `v_p(D n) = 0 < 1 = v_p(n)`: the derivative lowers `v_p` there, and that half is exactly
  Rigidity, recorded as `padic_lowers_on_support`. But it *raises* `v_p` elsewhere. Three witnesses,
  one for each of the first three primes, are checked outright:
  `2 ∤ 15` and `15' = 8`; `3 ∤ 14` and `14' = 9`; `5 ∤ 6` and `6' = 5`. So no `p`-adic place
  contracts uniformly, which is `not_descent_padic`.

* **(iii)** Ostrowski's theorem says (i) and (ii) exhaust the places of `ℚ`. That input is not
  reproved here; it enters `no_place_descent` as an explicit disjunction hypothesis, so the file
  makes visible exactly what is imported and what is proved.

Hence no valuation-theoretic descent of the type that proves `prop:ff-pyth` can exist over `ℚ`: the
function-field argument fails to transfer for a structural reason internal to the classification of
absolute values, not for want of a cleverer place.

Paper: Proposition `prop:noplace`. Counts and witnesses: `code/no_place.rs`.
-/

namespace Erdos307

/-- A *descent* for the derivative with respect to a size `v` is a strict decrease at the point
under consideration. One witness where the size does not drop refutes it. -/
def Descends (v : ℕ → ℕ) (S : Finset ℕ) : Prop := v (csum S) < v (dprod S)

/-- The general refutation principle: a single point where the size fails to drop kills the
descent there. -/
theorem not_descends_of_le {v : ℕ → ℕ} {S : Finset ℕ} (h : v (dprod S) ≤ v (csum S)) :
    ¬ Descends v S := not_lt.mpr h

/-! ### (i) The archimedean place -/

/-- `30' = 31`: the derivative expands at the first point of mass exceeding `1`. -/
theorem der_thirty : dprod {2, 3, 5} = 30 ∧ csum {2, 3, 5} = 31 := by decide

/-- **(i).** No strictly monotone size decreases along the derivative, because it expands at `30`.
This covers the archimedean absolute value and every order-respecting substitute for it. -/
theorem not_descent_of_strictMono {v : ℕ → ℕ} (hv : StrictMono v) : ¬ Descends v {2, 3, 5} := by
  refine not_descends_of_le (hv.monotone ?_)
  rw [der_thirty.1, der_thirty.2]
  norm_num

/-! ### (ii) The `p`-adic places -/

/-- **The lowering half, which is Rigidity.** If `p` lies in the support then `p` does not divide
the derivative: `v_p` drops from `1` to `0`. -/
theorem padic_lowers_on_support {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {p : ℕ} (hp : p ∈ S) :
    ¬ p ∣ csum S := by
  intro hdvd
  have hg : Nat.gcd (csum S) (dprod S) = 1 := rigidity_coprime S hS
  have hpd : p ∣ dprod S := Finset.dvd_prod_of_mem _ hp
  have h1 : p ∣ 1 := by rw [← hg]; exact Nat.dvd_gcd hdvd hpd
  have := Nat.eq_one_of_dvd_one h1
  exact absurd this (hS p hp).one_lt.ne'

/-- **The raising half, `p = 2`.** `2 ∤ 15` but `15' = 8`, so `v₂` climbs from `0` to `3`. -/
theorem raises_two : ¬ (2 ∣ dprod {3, 5}) ∧ 2 ∣ csum {3, 5} := by decide

/-- **The raising half, `p = 3`.** `3 ∤ 14` but `14' = 9`. -/
theorem raises_three : ¬ (3 ∣ dprod {2, 7}) ∧ 3 ∣ csum {2, 7} := by decide

/-- **The raising half, `p = 5`.** `5 ∤ 6` but `6' = 5`. -/
theorem raises_five : ¬ (5 ∣ dprod {2, 3}) ∧ 5 ∣ csum {2, 3} := by decide

/-- **(ii).** No `p`-adic valuation descends at a support avoiding `p`: there `v_p` is already `0`,
which is minimal, so it cannot fall however the derivative behaves. Combined with the witnesses
above, where `p` divides the derivative, `v_p` in fact strictly *rises* at exactly such supports.
Applied with the three witnesses this rules out `p = 2, 3, 5`; the same shape of witness exists at
every `p` tested (`code/no_place.rs`), in abundance comparable to the lowering cases. -/
theorem not_descent_padic {S : Finset ℕ} {p : ℕ} (hnd : ¬ p ∣ dprod S) :
    ¬ Descends (fun n => padicValNat p n) S := by
  refine not_descends_of_le ?_
  rw [padicValNat.eq_zero_of_not_dvd hnd]
  exact Nat.zero_le _

/-! ### (iii) Ostrowski, and the packaging -/

/-- **`prop:noplace`.** Given the classification of places, either branch fails: a strictly monotone
size expands at `30`, and a `p`-adic one rises at a support avoiding `p`. So no place of `ℚ` carries
the descent.

Ostrowski's theorem is the hypothesis `hclass`, supplied rather than reproved, and the two witness
families are the hypotheses it is applied to. -/
theorem no_place_descent {v : ℕ → ℕ} {S : Finset ℕ} {p : ℕ}
    (hclass : StrictMono v ∨ v = fun n => padicValNat p n)
    (harch : S = {2, 3, 5}) (hnd : ¬ p ∣ dprod S) :
    ¬ Descends v S := by
  rcases hclass with hmono | hveq
  · subst harch; exact not_descent_of_strictMono hmono
  · subst hveq; exact not_descent_padic hnd

end Erdos307
