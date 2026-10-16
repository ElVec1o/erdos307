import Erdos307.Level60Sectors

/-!
# Necessary conditions on the tail prime `q` (the q-sieve)

For a base `S ∋ 2` and a tail prime `q`, `x² = A q + D` (`A = N + 2D`, `D = ∏S`) forces:

* `two_adic_class`: `q ≡ A (1 - D) (mod 8)` (`x` is odd);
* `tail_legendre`: `(q | ℓ) = ((D/ℓ) | ℓ)` for every odd `ℓ ∈ S`.

These are the two filters of `code/qsieve/q_sieve.rs`, the first of which that program does not use (a factor `4`).

Paper: Proposition `prop:lvl60factor`, `prop:level60closed`.
-/

namespace Erdos307

open Finset

theorem sq_mod_eight_of_odd {x : ℤ} (hx : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  have h : (2 * k + 1) ^ 2 = 8 * (k * (k + 1) / 2) + 1 := by
    have he : Even (k * (k + 1)) := Int.even_mul_succ_self k
    obtain ⟨m, hm⟩ := he
    have : k * (k + 1) / 2 = m := by omega
    rw [this]; nlinarith [hm]
  omega

/-- `x² = A q + D` with `A`, `q` odd and `D` even forces `A q + D ≡ 1 (mod 8)`. -/
theorem two_adic_sum {x A q D : ℤ} (hA : A % 2 = 1) (hq : q % 2 = 1) (hD : D % 2 = 0)
    (h : x ^ 2 = A * q + D) : (A * q + D) % 8 = 1 := by
  have hodd : x % 2 = 1 := by
    by_contra hne
    have hev : x % 2 = 0 := by omega
    obtain ⟨k, hk⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
    have : (A * q + D) % 2 = 1 := by
      have h1 : (A * q) % 2 = 1 := by rw [Int.mul_emod, hA, hq]; norm_num
      omega
    have h2 : x ^ 2 % 2 = 0 := by rw [hk]; ring_nf; omega
    omega
  rw [← h]; exact sq_mod_eight_of_odd hodd

/-- The residue class of `q` modulo `8`: `q ≡ A (1 - D)`. -/
theorem two_adic_class {x A q D : ℤ} (hA : A % 2 = 1) (hq : q % 2 = 1) (hD : D % 2 = 0)
    (h : x ^ 2 = A * q + D) : q % 8 = (A * (1 - D)) % 8 := by
  have h1 := two_adic_sum hA hq hD h
  have hA8 : A % 8 = 1 ∨ A % 8 = 3 ∨ A % 8 = 5 ∨ A % 8 = 7 := by omega
  have hq8 : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  have hD8 : D % 8 = 0 ∨ D % 8 = 2 ∨ D % 8 = 4 ∨ D % 8 = 6 := by omega
  have e1 : (A * q + D) % 8 = ((A % 8) * (q % 8) + D % 8) % 8 := by
    rw [Int.add_emod, Int.mul_emod]; simp
  have e2 : (A * (1 - D)) % 8 = ((A % 8) * ((1 - D % 8) % 8)) % 8 := by
    have : (1 - D) % 8 = (1 - D % 8) % 8 := by omega
    rw [Int.mul_emod, this]
  rw [e1] at h1; rw [e2]
  rcases hA8 with ha | ha | ha | ha <;> rcases hq8 with hq | hq | hq | hq <;> rcases hD8 with hd | hd | hd | hd <;>
    simp [ha, hq, hd] at h1 ⊢

/-- For an odd `ℓ ∈ S`, `x² = A q + D` gives `(q | ℓ) = ((∏(S∖ℓ)) | ℓ)` when `ℓ ∤ q`. -/
theorem tail_legendre {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) {ℓ q : ℕ} (hℓ : ℓ ∈ S) [Fact ℓ.Prime]
    (hq : ¬ ℓ ∣ q) {x : ℤ} (hx : x ^ 2 = ((csum S : ℤ) + 2 * dprod S) * q + dprod S) :
    legendreSym ℓ (q : ℤ) = legendreSym ℓ ((dprod (S.erase ℓ) : ℕ) : ℤ) := by
  have hℓp : ℓ.Prime := hS ℓ hℓ
  have hX : ∀ r ∈ S.erase ℓ, r.Prime := fun r hr => hS r (Finset.mem_of_mem_erase hr)
  have hSe : S = S.erase ℓ ∪ {ℓ} := by
    ext y; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · intro hy; by_cases h : y = ℓ <;> simp [h, hy]
    · rintro (⟨-, hy⟩ | rfl) <;> assumption
  have hcs : csum S = ℓ * csum (S.erase ℓ) + dprod (S.erase ℓ) := by
    conv_lhs => rw [hSe]
    exact csum_insert_prime (Finset.notMem_erase ℓ S) hℓp.pos
  have hD : dprod S = ℓ * dprod (S.erase ℓ) := by
    conv_lhs => rw [hSe]
    unfold dprod
    rw [Finset.prod_union (by simp [Finset.disjoint_singleton_right])]
    simp [mul_comm]
  have hdp : ¬ ℓ ∣ dprod (S.erase ℓ) := by
    intro hd; unfold dprod at hd
    obtain ⟨r, hr, hℓr⟩ := (Prime.dvd_finsetProd_iff hℓp.prime _).1 hd
    have := (Nat.prime_dvd_prime_iff_eq hℓp (hX r hr)).1 hℓr
    exact Finset.notMem_erase ℓ S (this ▸ hr)
  have he : (((dprod (S.erase ℓ) : ℕ) : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact hdp
  have hm : ((q : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact hq
  -- x² ≡ e q (mod ℓ), with e = ∏(S∖ℓ)
  have hc := congrArg (fun z : ℤ => (z : ZMod ℓ)) hx
  have hl : ((ℓ : ℕ) : ZMod ℓ) = 0 := ZMod.natCast_self ℓ
  simp only [hcs, hD] at hc
  push_cast at hc
  rw [hl] at hc
  simp only [zero_mul, zero_add, add_zero, mul_zero] at hc
  have hsq : IsSquare ((((dprod (S.erase ℓ) : ℕ) : ℤ) * q : ℤ) : ZMod ℓ) := by
    refine ⟨((x : ℤ) : ZMod ℓ), ?_⟩
    push_cast
    rw [← hc]; ring
  have hem : ((((dprod (S.erase ℓ) : ℕ) : ℤ) * q : ℤ) : ZMod ℓ) ≠ 0 := by
    push_cast; exact mul_ne_zero (by simpa using he) (by simpa using hm)
  have h1 : legendreSym ℓ ((dprod (S.erase ℓ) : ℕ) : ℤ) * legendreSym ℓ (q : ℤ) = 1 := by
    rw [← legendreSym.mul]; exact (legendreSym.eq_one_iff ℓ hem).2 hsq
  have h2 : legendreSym ℓ ((dprod (S.erase ℓ) : ℕ) : ℤ) ^ 2 = 1 := legendreSym.sq_one ℓ he
  linear_combination (-(legendreSym ℓ (q : ℤ))) * h2 + legendreSym ℓ ((dprod (S.erase ℓ) : ℕ) : ℤ) * h1

end Erdos307
