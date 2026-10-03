import Erdos307.Lvl60Factor
import Erdos307.PairClosed

/-!
# Pair sector: the two necessary conditions from a cycle

Track B, obligation (a). A two-cycle on `R ∪ {p}` (`p ∉ R` prime) forces, with `D = ∏R`, `N = csum R`:

* `p (2D - N) ≤ D` (the tail bound), and
* for every odd `ℓ ∈ R`: `(p | ℓ) = ((∏(R∖ℓ)) | ℓ)` (the character condition).

These are exactly the two tests the pair-sector computation applies to each `(R, p)`; this file is their
kernel-checked derivation from the cycle equations, with no computation.

Paper: Proposition `prop:pairclosed` (the reduction to the finite check).
-/

namespace Erdos307

open Finset

theorem pair_necessary {R P Q : Finset ℕ} {p : ℕ} (hR : ∀ r ∈ R, r.Prime) (hp : p.Prime)
    (hpR : p ∉ R) (hdisj : Disjoint P Q) (hU : P ∪ Q = R ∪ {p})
    (h1 : csum P = dprod Q) (h2 : csum Q = dprod P) :
    (p : ℤ) * (2 * dprod R - csum R) ≤ dprod R ∧
      ∀ ℓ ∈ R, ℓ ≠ 2 → ∀ [Fact ℓ.Prime],
        legendreSym ℓ (p : ℤ) = legendreSym ℓ ((dprod (R.erase ℓ) : ℕ) : ℤ) := by
  obtain ⟨a, b, hab, -, -, hsq⟩ := lvl60_factor_ab hR hp hpR hdisj hU h1 h2
  have hab' : (a : ℤ) * b = dprod R * p := by exact_mod_cast hab
  have hsq' : ((a : ℤ) + b) ^ 2 = ((csum R : ℤ) + 2 * dprod R) * p + dprod R := by
    exact_mod_cast hsq
  have hNd : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (csum R : ℤ) * p + dprod R := by nlinarith
  refine ⟨pair_tail_bound _ _ _ _ _ hab' hNd, ?_⟩
  intro ℓ hℓ _ _
  have hℓp : ℓ.Prime := hR ℓ hℓ
  have hX : ∀ r ∈ R.erase ℓ, r.Prime := fun r hr => hR r (Finset.mem_of_mem_erase hr)
  have hRe : R = R.erase ℓ ∪ {ℓ} := by
    ext x; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · intro hx; by_cases h : x = ℓ <;> simp [h, hx]
    · rintro (⟨-, hx⟩ | rfl) <;> assumption
  have hcs : csum R = ℓ * csum (R.erase ℓ) + dprod (R.erase ℓ) := by
    conv_lhs => rw [hRe]
    exact csum_insert_prime (Finset.notMem_erase ℓ R) hℓp.pos
  have hD : dprod R = ℓ * dprod (R.erase ℓ) := by
    conv_lhs => rw [hRe]
    unfold dprod
    rw [Finset.prod_union (by simp [Finset.disjoint_singleton_right])]
    simp [mul_comm]
  have hdp : ¬ ℓ ∣ dprod (R.erase ℓ) := by
    intro hd; unfold dprod at hd
    obtain ⟨r, hr, hℓr⟩ := (Prime.dvd_finsetProd_iff hℓp.prime _).1 hd
    have := (Nat.prime_dvd_prime_iff_eq hℓp (hX r hr)).1 hℓr
    exact Finset.notMem_erase ℓ R (this ▸ hr)
  have hpℓ : ¬ ℓ ∣ p := by
    intro hd
    have : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓp hp).1 hd
    exact hpR (this ▸ hℓ)
  have he : (((dprod (R.erase ℓ) : ℕ) : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact hdp
  have hm : ((p : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact hpℓ
  refine (pair_legendre ℓ (dprod R) (csum R) p (dprod (R.erase ℓ)) a b hab' hNd
    (by exact_mod_cast hD) ?_ he hm).symm.symm
  rw [hcs]; push_cast
  simp

end Erdos307
