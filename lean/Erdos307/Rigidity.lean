import Mathlib

/-!
# Erdős #307 — Rigidity (Lean targets T1, T2)

For a finite set `S` of distinct primes write
* `dprod S = ∏_{p ∈ S} p`,
* `csum S = ∑_{p ∈ S} (dprod S)/p`  (the cofactor sum), so `∑_{p∈S} 1/p = csum S / dprod S`.

**T1 (Rigidity / coprimality).** `Nat.Coprime (csum S) (dprod S)`: the fraction `∑ 1/p` is already
in lowest terms.

**T2 (Solution structure).** If `(N_P/D_P)·(N_Q/D_Q) = 1` in `ℚ` with both fractions reduced,
then `N_P = D_Q` and `N_Q = D_P`.
-/

namespace Erdos307

open Finset

/-- `dprod S = ∏_{p ∈ S} p`. -/
def dprod (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- The cofactor sum `csum S = ∑_{p ∈ S} (dprod S)/p`.  When the elements of `S` are primes this is
the numerator of `∑_{p∈S} 1/p` in lowest terms (see `rigidity_coprime`). -/
def csum (S : Finset ℕ) : ℕ := ∑ p ∈ S, dprod S / p

/-- For `p ∈ S` with `p > 0`, `dprod S / p = ∏_{q ∈ S.erase p} q`. -/
lemma dprod_div (S : Finset ℕ) {p : ℕ} (hp : p ∈ S) (hp0 : 0 < p) :
    dprod S / p = ∏ q ∈ S.erase p, q := by
  have h : dprod S = p * ∏ q ∈ S.erase p, q := by
    unfold dprod
    exact (Finset.mul_prod_erase S (fun q => q) hp).symm
  rw [h, Nat.mul_div_cancel_left _ hp0]

/-- **T1 (Rigidity).** For a finite set of distinct primes, the reciprocal-sum fraction
`csum S / dprod S` is already in lowest terms: `gcd (csum S) (dprod S) = 1`. -/
theorem rigidity_coprime (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Nat.Coprime (csum S) (dprod S) := by
  rw [Nat.coprime_comm]
  -- Reduce to: no prime `p ∈ S` divides `csum S` (since `dprod S = ∏_{p∈S} p`).
  have key : ∀ p ∈ S, ¬ p ∣ csum S := by
    intro p hp hdvd
    have hpp : p.Prime := hS p hp
    -- Split `csum S = (dprod S)/p + ∑_{r ∈ S.erase p} (dprod S)/r`.
    have hsplit : csum S = dprod S / p + ∑ r ∈ S.erase p, dprod S / r := by
      rw [csum, ← Finset.add_sum_erase S (fun r => dprod S / r) hp]
    rw [hsplit] at hdvd
    -- `p` divides every term of the erased sum, hence the whole sum.
    have hsum : p ∣ ∑ r ∈ S.erase p, dprod S / r := by
      refine Finset.dvd_sum (fun r hr => ?_)
      rw [Finset.mem_erase] at hr
      obtain ⟨hrp, hrS⟩ := hr
      have hr0 : 0 < r := (hS r hrS).pos
      rw [dprod_div S hrS hr0]
      exact Finset.dvd_prod_of_mem (fun q => q)
        (Finset.mem_erase.mpr ⟨fun h => hrp h.symm, hp⟩)
    -- Therefore `p ∣ (dprod S)/p`.
    have hm : p ∣ dprod S / p := by
      rw [add_comm] at hdvd
      exact (Nat.dvd_add_right hsum).mp hdvd
    -- But `(dprod S)/p = ∏_{q ∈ S.erase p} q` is a product of primes ≠ p, so `p ∤` it.
    rw [dprod_div S hp hpp.pos] at hm
    have hcop : Nat.Coprime p (∏ q ∈ S.erase p, q) := by
      refine Nat.Coprime.prod_right (fun q hq => ?_)
      rw [Finset.mem_erase] at hq
      obtain ⟨hqp, hqS⟩ := hq
      exact (Nat.coprime_primes hpp (hS q hqS)).mpr (fun h => hqp h.symm)
    exact hpp.coprime_iff_not_dvd.mp hcop hm
  -- Assemble coprimality of the product from the per-prime statements.
  have : Nat.Coprime (∏ p ∈ S, p) (csum S) :=
    Nat.Coprime.prod_left
      (fun p hp => ((hS p hp).coprime_iff_not_dvd).mpr (key p hp))
  exact this

/-- **T2 (Solution structure).** If `(N_P/D_P)·(N_Q/D_Q) = 1` in `ℚ`, with both fractions in
lowest terms and nonzero denominators, then `N_P = D_Q` and `N_Q = D_P`. -/
theorem solution_structure {NP DP NQ DQ : ℕ}
    (hP : Nat.Coprime NP DP) (hQ : Nat.Coprime NQ DQ)
    (hDP : DP ≠ 0) (hDQ : DQ ≠ 0)
    (h : (NP : ℚ) / DP * ((NQ : ℚ) / DQ) = 1) :
    NP = DQ ∧ NQ = DP := by
  have hDP' : (DP : ℚ) ≠ 0 := by exact_mod_cast hDP
  have hDQ' : (DQ : ℚ) ≠ 0 := by exact_mod_cast hDQ
  -- Cross-multiply to the integer identity `NP * NQ = DP * DQ`.
  have hmul : (NP : ℚ) * NQ = DP * DQ := by
    field_simp at h
    linear_combination h
  have hnat : NP * NQ = DP * DQ := by exact_mod_cast hmul
  -- `NP ∣ DQ` and `DQ ∣ NP`, hence equal; then cancel.
  have h1 : NP ∣ DQ := hP.dvd_of_dvd_mul_left ⟨NQ, hnat.symm⟩
  have h2 : DQ ∣ NP := hQ.symm.dvd_of_dvd_mul_right ⟨DP, by rw [hnat]; ring⟩
  have hPDQ : NP = DQ := Nat.dvd_antisymm h1 h2
  refine ⟨hPDQ, ?_⟩
  rw [hPDQ] at hnat
  have hcanc : DQ * NQ = DQ * DP := by rw [hnat]; ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hDQ) hcanc

end Erdos307
