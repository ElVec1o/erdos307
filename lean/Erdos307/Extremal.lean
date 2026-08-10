import Mathlib

/-!
# Erdős #307 — T4′ groundwork: the smallest primes are extremal (crux lemma)

To discharge the hypothesis `hRatio` of `Erdos307.barrier`, we need that among all
`k`-element sets of primes, the `k` smallest primes minimise the product and maximise the
reciprocal sum.  Both follow term-by-term from the **crux** below: if `U` is a finite set of
primes enumerated in increasing order by `U.orderEmbOfFin rfl : Fin U.card ↪o ℕ`, then its
`i`-th element is at least the `i`-th prime `Nat.nth Nat.Prime i`.

Reason: the `i` earlier elements `e 0 < … < e (i-1)` are `i` distinct primes `< e i`, so at
least `i` primes lie below `e i`; since `e i` is itself the `(count primes < e i)`-th prime,
and `count ≥ i`, monotonicity of `Nat.nth` gives `Nat.nth Prime i ≤ e i`.

Status: written without a live checker — `Nat.nth`/`Nat.count` API names may need adjusting.

Paper: Lemma `lem:59`, Theorem `thm:barrier` (the extremality T4' rests on).
-/

namespace Erdos307

open Finset

/-- **Crux of T4′.**  For a finite set `U` of primes, the `i`-th element in increasing order
is at least the `i`-th prime. -/
lemma nth_prime_le_orderEmb {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) (i : Fin U.card) :
    Nat.nth Nat.Prime (i : ℕ) ≤ U.orderEmbOfFin rfl i := by
  have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
  set e := U.orderEmbOfFin rfl with he
  have hprime : Nat.Prime (e i) := hU _ (Finset.orderEmbOfFin_mem U rfl i)
  -- the `i` earlier elements are distinct primes `< e i`
  have hsub : (Finset.Iio i).image e ⊆ (Finset.range (e i)).filter Nat.Prime := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [Finset.mem_Iio] at hj
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨e.strictMono hj, hU _ (Finset.orderEmbOfFin_mem U rfl j)⟩
  -- hence at least `i` primes lie below `e i`
  have hcard : (i : ℕ) ≤ Nat.count Nat.Prime (e i) := by
    have h1 : ((Finset.Iio i).image e).card = (i : ℕ) := by
      rw [Finset.card_image_of_injective _ e.injective]
      simp [Fin.card_Iio]
    rw [Nat.count_eq_card_filter_range]
    calc (i : ℕ) = ((Finset.Iio i).image e).card := h1.symm
      _ ≤ ((Finset.range (e i)).filter Nat.Prime).card := Finset.card_le_card hsub
  -- `e i` is the `count`-th prime, and `count ≥ i`, so `nth i ≤ nth count = e i`
  calc Nat.nth Nat.Prime (i : ℕ)
        ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime (e i)) := Nat.nth_monotone hinf hcard
    _ = e i := Nat.nth_count hprime

/-- Reindex a product over a finite set as a product over `Fin U.card` via the order embedding. -/
lemma orderEmb_prod {M : Type*} [CommMonoid M] {U : Finset ℕ} (f : ℕ → M) :
    ∏ x ∈ U, f x = ∏ i : Fin U.card, f (U.orderEmbOfFin rfl i) := by
  have himg : Finset.univ.image (U.orderEmbOfFin rfl) = U := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, _, rfl⟩ := hy
      exact Finset.orderEmbOfFin_mem U rfl i
    · rw [Finset.card_image_of_injective _ (U.orderEmbOfFin rfl).injective,
        Finset.card_univ, Fintype.card_fin]
  conv_lhs => rw [← himg]
  rw [Finset.prod_image (fun x _ y _ h => (U.orderEmbOfFin rfl).injective h)]

/-- Additive analogue of `orderEmb_prod`. -/
lemma orderEmb_sum {M : Type*} [AddCommMonoid M] {U : Finset ℕ} (f : ℕ → M) :
    ∑ x ∈ U, f x = ∑ i : Fin U.card, f (U.orderEmbOfFin rfl i) := by
  have himg : Finset.univ.image (U.orderEmbOfFin rfl) = U := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, _, rfl⟩ := hy
      exact Finset.orderEmbOfFin_mem U rfl i
    · rw [Finset.card_image_of_injective _ (U.orderEmbOfFin rfl).injective,
        Finset.card_univ, Fintype.card_fin]
  conv_lhs => rw [← himg]
  rw [Finset.sum_image (fun x _ y _ h => (U.orderEmbOfFin rfl).injective h)]

/-- **Product extremality.**  The product of a set of primes is at least the product of the
`Nat`-th smallest primes of the same count. -/
lemma prod_first_primes_le {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) :
    ∏ i ∈ Finset.range U.card, Nat.nth Nat.Prime i ≤ ∏ p ∈ U, p := by
  rw [orderEmb_prod (U := U) (fun x => x),
      ← Fin.prod_univ_eq_prod_range (fun i => Nat.nth Nat.Prime i) U.card]
  exact Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => nth_prime_le_orderEmb hU i)

/-- **Reciprocal-sum extremality.**  The reciprocal sum of a set of primes is at most that of
the smallest primes of the same count. -/
lemma recipSum_le_first_primes {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) :
    ∑ p ∈ U, (p : ℚ)⁻¹ ≤ ∑ i ∈ Finset.range U.card, ((Nat.nth Nat.Prime i : ℚ))⁻¹ := by
  rw [orderEmb_sum (U := U) (fun x => ((x : ℚ))⁻¹),
      ← Fin.sum_univ_eq_sum_range (fun i => ((Nat.nth Nat.Prime i : ℚ))⁻¹) U.card]
  apply Finset.sum_le_sum
  intro i _
  have hle : (Nat.nth Nat.Prime (i : ℕ) : ℚ) ≤ (U.orderEmbOfFin rfl i : ℚ) := by
    exact_mod_cast nth_prime_le_orderEmb hU i
  have hpos : (0 : ℚ) < (Nat.nth Nat.Prime (i : ℕ) : ℚ) := by
    exact_mod_cast (Nat.prime_nth_prime (i : ℕ)).pos
  gcongr

/-- **Reduction.**  Given the (proven) extremality, the barrier hypothesis `hRatio` for a prime
support `U` follows from the single concrete inequality `hmono` about the smallest `U.card`
primes: `(4·10¹¹²)·∑_{i<k} 1/p_i ≤ ∏_{i<k} p_i`.  This isolates the *entire* remaining gap into
`hmono`, a finite arithmetic fact about `Nat.nth Nat.Prime`. -/
lemma hRatio_of_extremal {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime)
    (hmono : (4 * 10 ^ 112 : ℚ) * (∑ i ∈ Finset.range U.card, ((Nat.nth Nat.Prime i : ℚ))⁻¹)
              ≤ ∏ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ)) :
    (4 * 10 ^ 112 : ℚ) * (∑ p ∈ U, (p : ℚ)⁻¹) ≤ ((∏ p ∈ U, p : ℕ) : ℚ) := by
  have h1 : (∑ p ∈ U, (p : ℚ)⁻¹)
      ≤ ∑ i ∈ Finset.range U.card, ((Nat.nth Nat.Prime i : ℚ))⁻¹ := recipSum_le_first_primes hU
  have h2 : (∏ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ)) ≤ ((∏ p ∈ U, p : ℕ) : ℚ) := by
    have hnat := prod_first_primes_le hU
    calc (∏ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ))
        = ((∏ i ∈ Finset.range U.card, Nat.nth Nat.Prime i : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((∏ p ∈ U, p : ℕ) : ℚ) := by exact_mod_cast hnat
  calc (4 * 10 ^ 112 : ℚ) * (∑ p ∈ U, (p : ℚ)⁻¹)
      ≤ (4 * 10 ^ 112 : ℚ) * (∑ i ∈ Finset.range U.card, ((Nat.nth Nat.Prime i : ℚ))⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ (∏ i ∈ Finset.range U.card, (Nat.nth Nat.Prime i : ℚ)) := hmono
    _ ≤ ((∏ p ∈ U, p : ℕ) : ℚ) := h2

end Erdos307
