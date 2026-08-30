import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic
import Erdos307.DivisorSum

/-!
# Counting the roots of `2s² + 1` modulo `u`

This closes the last elementary gap in `prop:plusthin` (atom A6). The divisor-sum chain there needs
`|R| ≤ τ(u)` for `R` the roots of `2s² + 1 ≡ 0` modulo `u`. The right-hand half,
`2^ω(u) ≤ τ(u)`, is `Erdos307.two_pow_omega_le_tau`. This file supplies the left-hand half,
`|R| ≤ 2^ω(u)`, which is the multiplicativity of the root count.

Two steps, both elementary once the count is taken in `ZMod`.

* `rootSet_card_mul_le`: the Chinese remainder ring equivalence carries a root modulo `ab` to a pair
  of roots, injectively, so the count is submultiplicative on coprime factors. No transport lemma is
  needed --- a ring equivalence preserves the equation on the nose.
* `rootSet_card_prime_pow_le_two`: modulo an odd prime power there are at most two roots. `ZMod (p^k)`
  is a local ring, so the nonunits are closed under addition; if `x` and `y` are roots then
  `(x-y)(x+y) = 0`, and `x - y`, `x + y` cannot both be nonunits, since their sum `2x` is a unit
  (`2` is a unit as `p` is odd, and `x` is a unit as `2x² = -1`). Hence `y = x` or `y = -x`.

Paper: Proposition `prop:plusthin`.
-/

namespace Erdos307

open Finset

/-- The roots of `2x² + 1 = 0` in `ZMod n`. -/
def rootSet (n : ℕ) [NeZero n] : Finset (ZMod n) :=
  Finset.univ.filter fun x => 2 * x ^ 2 + 1 = 0

theorem mem_rootSet {n : ℕ} [NeZero n] {x : ZMod n} :
    x ∈ rootSet n ↔ 2 * x ^ 2 + 1 = 0 := by
  simp [rootSet]

/-- **Submultiplicativity.** The Chinese remainder equivalence sends a root modulo `ab` to a pair of
roots and is injective, so the root count is at most the product of the root counts. -/
theorem rootSet_card_mul_le {a b : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b) :
    haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    (rootSet (a * b)).card ≤ (rootSet a).card * (rootSet b).card := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  classical
  let e := ZMod.chineseRemainder h
  have hmap : ∀ x ∈ rootSet (a * b), e x ∈ (rootSet a) ×ˢ (rootSet b) := by
    intro x hx
    rw [mem_rootSet] at hx
    have : e (2 * x ^ 2 + 1) = 0 := by rw [hx]; exact map_zero _
    rw [map_add, map_mul, map_pow, map_one, map_ofNat] at this
    have h1 : (e x).1 ∈ rootSet a := by
      rw [mem_rootSet]
      have := congrArg Prod.fst this
      simpa using this
    have h2 : (e x).2 ∈ rootSet b := by
      rw [mem_rootSet]
      have := congrArg Prod.snd this
      simpa using this
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  have := Finset.card_le_card_of_injOn (fun x => e x) hmap
    (fun x _ y _ hxy => e.injective hxy)
  simpa [Finset.card_product] using this

/-- A root modulo an odd prime power is a unit: `2x² = -1` makes `x` invertible. -/
theorem isUnit_of_root {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hk : 0 < k)
    [NeZero (p ^ k)] {x : ZMod (p ^ k)} (hx : 2 * x ^ 2 + 1 = 0) : IsUnit x := by
  have hxy : x * (-(2 * x)) = 1 := by linear_combination -hx
  exact isUnit_iff_exists_inv.mpr ⟨_, hxy⟩


/-- In `ZMod (p^k)` an element is a unit exactly when `p` does not divide its representative. -/
theorem isUnit_iff_not_dvd_val {p k : ℕ} (hp : p.Prime) (hk : 0 < k) [NeZero (p ^ k)]
    (z : ZMod (p ^ k)) : IsUnit z ↔ ¬ p ∣ z.val := by
  have hz : ((z.val : ℕ) : ZMod (p ^ k)) = z := by
    simpa using (ZMod.natCast_val (R := ZMod (p ^ k)) z)
  constructor
  · intro hu hdvd
    have hc : Nat.Coprime z.val (p ^ k) := by
      rw [← ZMod.isUnit_iff_coprime, hz]; exact hu
    have hp1 : p ∣ Nat.gcd z.val (p ^ k) := Nat.dvd_gcd hdvd (dvd_pow_self p hk.ne')
    rw [hc] at hp1
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  · intro hnd
    have hc : Nat.Coprime z.val (p ^ k) :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm.pow_right k
    have := (ZMod.isUnit_iff_coprime z.val (p ^ k)).mpr hc
    rwa [hz] at this

/-- **At most two roots modulo an odd prime power.** If `x` and `y` both satisfy `2z² + 1 = 0` then
`(x-y)(x+y) = 0`, and `p` cannot divide the representatives of both factors, since their sum
represents the unit `2x`. So `p^k` divides one factor outright. -/
theorem root_eq_or_eq_neg {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hk : 0 < k)
    [NeZero (p ^ k)] {x y : ZMod (p ^ k)}
    (hx : 2 * x ^ 2 + 1 = 0) (hy : 2 * y ^ 2 + 1 = 0) : y = x ∨ y = -x := by
  have h2x : IsUnit (2 * x) := by
    have : (2 * x) * (-x) = 1 := by linear_combination -hx
    exact isUnit_iff_exists_inv.mpr ⟨_, this⟩
  have hzero : (x - y) * (x + y) = 0 := by
    have h2 : IsUnit (2 : ZMod (p ^ k)) := by
      have hc : Nat.Coprime 2 (p ^ k) :=
        ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)).pow_right k
      simpa using (ZMod.isUnit_iff_coprime 2 (p ^ k)).mpr hc
    obtain ⟨u, hu⟩ := h2
    have hd : (2 : ZMod (p ^ k)) * ((x - y) * (x + y)) = 0 := by linear_combination hx - hy
    have := congrArg (fun t => (↑u⁻¹ : ZMod (p ^ k)) * t) hd
    simpa [← hu, ← mul_assoc, Units.inv_mul] using this
  -- p divides at most one of the two representatives
  have hnot : ¬ (p ∣ (x - y).val ∧ p ∣ (x + y).val) := by
    rintro ⟨h1, h2⟩
    have hsum : p ∣ ((x - y) + (x + y)).val := by
      rw [ZMod.val_add]
      exact (Nat.dvd_mod_iff (dvd_pow_self p hk.ne')).mpr (Nat.dvd_add h1 h2)
    rw [show (x - y) + (x + y) = 2 * x by ring] at hsum
    exact ((isUnit_iff_not_dvd_val hp hk _).mp h2x) hsum
  rcases Classical.em (p ∣ (x - y).val) with hd | hd
  · -- then p does not divide (x+y).val, so p^k divides it not; instead p^k ∣ (x-y).val
    have hnd : ¬ p ∣ (x + y).val := fun h => hnot ⟨hd, h⟩
    have hcop : Nat.Coprime (p ^ k) (x + y).val :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).pow_left k
    have hdvd : p ^ k ∣ (x - y).val * (x + y).val := by
      have : ((x - y) * (x + y)).val = 0 := by rw [hzero]; simp
      have hmul := ZMod.val_mul (x - y) (x + y)
      rw [this] at hmul
      exact Nat.dvd_iff_mod_eq_zero.mpr hmul.symm
    have : p ^ k ∣ (x - y).val := (Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd)
    have hlt := ZMod.val_lt (x - y)
    have h0 : (x - y).val = 0 := Nat.eq_zero_of_dvd_of_lt this hlt
    left
    have := (ZMod.val_eq_zero (x - y)).mp h0
    linear_combination -this
  · have hcop : Nat.Coprime (p ^ k) (x - y).val :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd).pow_left k
    have hdvd : p ^ k ∣ (x + y).val * (x - y).val := by
      have : ((x - y) * (x + y)).val = 0 := by rw [hzero]; simp
      have hmul := ZMod.val_mul (x - y) (x + y)
      rw [this] at hmul
      rw [mul_comm]
      exact Nat.dvd_iff_mod_eq_zero.mpr hmul.symm
    have hdd : p ^ k ∣ (x + y).val := Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd
    have hlt := ZMod.val_lt (x + y)
    have h0 : (x + y).val = 0 := Nat.eq_zero_of_dvd_of_lt hdd hlt
    right
    have := (ZMod.val_eq_zero (x + y)).mp h0
    linear_combination this


/-- **At most two roots modulo an odd prime power.** -/
theorem rootSet_card_prime_pow_le_two {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hk : 0 < k)
    [NeZero (p ^ k)] : (rootSet (p ^ k)).card ≤ 2 := by
  rcases Finset.eq_empty_or_nonempty (rootSet (p ^ k)) with he | ⟨x, hx⟩
  · simp [he]
  · have hsub : rootSet (p ^ k) ⊆ {x, -x} := by
      intro y hy
      rcases root_eq_or_eq_neg hp hodd hk (mem_rootSet.mp hx) (mem_rootSet.mp hy) with h | h
      · simp [h]
      · simp [h]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _ |>.trans (by simp))

/-- Modulo a power of `2` there are no roots at all: `2x² + 1 = 0` makes `2x` a unit. -/
theorem rootSet_two_pow_eq_empty {k : ℕ} (hk : 0 < k) [NeZero ((2 : ℕ) ^ k)] :
    rootSet ((2 : ℕ) ^ k) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have hx' := mem_rootSet.mp hx
  have h2 : IsUnit (2 : ZMod ((2 : ℕ) ^ k)) :=
    isUnit_iff_exists_inv.mpr ⟨x * (-x), by linear_combination -hx'⟩
  have hnd := (isUnit_iff_not_dvd_val Nat.prime_two hk (2 : ZMod ((2 : ℕ) ^ k))).mp h2
  apply hnd
  have hcast : (2 : ZMod ((2 : ℕ) ^ k)) = ((2 : ℕ) : ZMod ((2 : ℕ) ^ k)) := by push_cast; ring
  rw [hcast, ZMod.val_natCast]
  exact (Nat.dvd_mod_iff (dvd_pow_self 2 hk.ne')).mpr dvd_rfl

/-- **The multiplicativity bound, `|R| ≤ 2^ω(u)`.** This is the left-hand inequality that
`prop:plusthin` needs; combined with `two_pow_omega_le_tau` it gives `|R| ≤ τ(u)`. -/
theorem rootSet_card_le_two_pow_omega : ∀ n : ℕ, ∀ h : NeZero n,
    (@rootSet n h).card ≤ 2 ^ n.primeFactors.card := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro h
      haveI := h
      have hpn : p.Prime := hp
      rcases eq_or_ne p 2 with rfl | hodd
      · rw [rootSet_two_pow_eq_empty hk]
        simp
      · refine le_trans (rootSet_card_prime_pow_le_two hpn hodd hk) ?_
        rw [Nat.primeFactors_prime_pow hk.ne' hpn]
        simp
  | zero => intro h; exact absurd rfl (NeZero.ne 0)
  | one =>
      intro h
      haveI := h
      calc (rootSet 1).card ≤ Fintype.card (ZMod 1) := Finset.card_le_univ _
        _ = 1 := by simp
        _ = 2 ^ (Nat.primeFactors 1).card := by simp
  | coprime a b ha hb hab iha ihb =>
      intro h
      haveI hA : NeZero a := ⟨by omega⟩
      haveI hB : NeZero b := ⟨by omega⟩
      haveI := h
      calc (rootSet (a * b)).card
          ≤ (rootSet a).card * (rootSet b).card := rootSet_card_mul_le hab
        _ ≤ 2 ^ a.primeFactors.card * 2 ^ b.primeFactors.card :=
            Nat.mul_le_mul (iha hA) (ihb hB)
        _ = 2 ^ (a.primeFactors.card + b.primeFactors.card) := (pow_add 2 _ _).symm
        _ = 2 ^ (a * b).primeFactors.card := by
            rw [Nat.primeFactors_mul (NeZero.ne a) (NeZero.ne b),
              Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hab)]


/-- **The lemma `prop:plusthin` was missing.** The number of roots of `2s² + 1 ≡ 0` modulo `u` is at
most `τ(u)`. With this the divisor-sum chain of `PlusThin.lean` is closed: the root count feeding
`count_in_residue_classes` is bounded by the divisor function, which is what
`count_le_divisor_sum` and `sum_tau_div_le_log_sq` consume. -/
theorem rootSet_card_le_tau (n : ℕ) [h : NeZero n] :
    (rootSet n).card ≤ n.divisors.card :=
  le_trans (rootSet_card_le_two_pow_omega n h) (two_pow_omega_le_tau (NeZero.ne n))

end Erdos307
