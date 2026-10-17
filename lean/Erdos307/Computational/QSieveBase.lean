import QNative.QSieve
import Erdos307.Computational.Euler
import Erdos307.KillSearch
import Erdos307.QSieveLemmas

/-!
# The q-sieve for one base

`sieveBase Sl` runs the sieve over the tail prime `q ≤ N 2^40 / D` for the base with ascending prime list `Sl`:
`q ≡ q0 (mod 8)` (`two_adic_class`), the Legendre condition at every odd prime of `Sl` (`tail_legendre`), the
first nine odd primes as a wheel, and the two exact squares at every survivor. `sieveBase_sound`: if it returns
`true`, no tail prime `q` with `q D ≤ N 2^40` carries a solution of the two squares.

Paper: Proposition `prop:level60closed` (the sieve for `ρ > 2^-40`).
-/

namespace Erdos307

open QS

def sieveBase (Sl : List Nat) : Bool :=
  let D := Sl.prod
  let N := dval Sl
  let A := N + 2 * D
  let B := N - 2 * D
  let odd := Sl.filter (· ≠ 2)
  sieveRun (N * 2 ^ 40 / D) A B D (((A : ℤ) * (1 - (D : ℤ))) % 8).toNat
    ((odd.take 9).map fun p => (p, qTab D p)) ((odd.drop 9).map fun p => (p, qTab D p))

/-- A prime of the base, and a larger prime `q` satisfying the first square, passes the table of `p`. -/
theorem good_of_square {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) {p q : ℕ} (hpS : p ∈ S) (hp2 : p ≠ 2)
    (hq : q.Prime) (hpq : p < q) {x : ℤ}
    (hx : x ^ 2 = ((csum S : ℤ) + 2 * dprod S) * q + dprod S) : good (dprod S) p (q % p) := by
  haveI : Fact p.Prime := ⟨hS p hpS⟩
  have hnd : ¬ p ∣ q := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq (hS p hpS) hq).1 hd
    omega
  have hleg := tail_legendre hS hpS hnd hx
  rw [legendreSym_eq_eulerSym hp2 q] at hleg
  have hdiv : dprod S / p = dprod (S.erase p) := dprod_div S hpS (hS p hpS).pos
  refine ⟨fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0), ?_⟩
  show eulerSym p (q % p) = eulerSym p ((dprod S / p) % p)
  rw [hdiv, hleg, legendreSym_eq_eulerSym hp2 (dprod (S.erase p))]

theorem sieveBase_sound {Sl : List ℕ} (hnd : Sl.Nodup) (hp : ∀ p ∈ Sl, p.Prime) (h2 : 2 ∈ Sl)
    (hT : 2 * dprod Sl.toFinset ≤ csum Sl.toFinset) (h : sieveBase Sl = true)
    (q : ℕ) (hq : q.Prime) (hlt : ∀ s ∈ Sl, s < q)
    (hqD : q * dprod Sl.toFinset ≤ csum Sl.toFinset * 2 ^ 40) :
    ¬ TailArith Sl.toFinset q := by
  set S := Sl.toFinset with hSdef
  have hSp : ∀ r ∈ S, r.Prime := fun r hr => hp r (List.mem_toFinset.1 hr)
  have hD : dprod S = Sl.prod := dprod_toFinset_list hnd
  have hN : csum S = dval Sl := csum_toFinset_list hnd
  rintro ⟨x, y, -, -, hx, hy⟩
  have h2S : 2 ∈ S := List.mem_toFinset.2 h2
  have hNodd : Odd (csum S) := csum_odd_of_two_mem hSp h2S
  have hDev : 2 ∣ dprod S := by unfold dprod; exact Finset.dvd_prod_of_mem _ h2S
  have hq2 : 2 < q := hlt 2 h2
  have hqodd : q % 2 = 1 := Nat.odd_iff.1 (hq.odd_of_ne_two (by omega))
  have hA : ((csum S : ℤ) + 2 * dprod S) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hNodd
    have : (csum S : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    omega
  have hqz : (q : ℤ) % 2 = 1 := by omega
  have hDz : (dprod S : ℤ) % 2 = 0 := by obtain ⟨k, hk⟩ := hDev; omega
  have h8 := two_adic_class hA hqz hDz hx
  -- the class of `q` modulo 8, as the natural number used by the sieve
  have hAcast : (((dval Sl + 2 * Sl.prod : ℕ)) : ℤ) = (csum S : ℤ) + 2 * dprod S := by
    rw [hN, hD]; push_cast; ring
  have hq0 : q % 8 = ((((dval Sl + 2 * Sl.prod : ℕ) : ℤ) * (1 - (Sl.prod : ℤ))) % 8).toNat := by
    have hm0 : 0 ≤ (((dval Sl + 2 * Sl.prod : ℕ) : ℤ) * (1 - (Sl.prod : ℤ))) % 8 :=
      Int.emod_nonneg _ (by norm_num)
    have hsame : (((dval Sl + 2 * Sl.prod : ℕ) : ℤ) * (1 - (Sl.prod : ℤ))) =
        ((csum S : ℤ) + 2 * dprod S) * (1 - (dprod S : ℤ)) := by rw [hAcast, hD]
    rw [hsame] at hm0 ⊢
    omega
  have hq8lt : ((((dval Sl + 2 * Sl.prod : ℕ) : ℤ) * (1 - (Sl.prod : ℤ))) % 8).toNat < 8 := by
    have := Int.emod_lt_of_pos (((dval Sl + 2 * Sl.prod : ℕ) : ℤ) * (1 - (Sl.prod : ℤ))) (by norm_num : (0 : ℤ) < 8)
    have := Int.emod_nonneg (((dval Sl + 2 * Sl.prod : ℕ) : ℤ) * (1 - (Sl.prod : ℤ))) (by norm_num : (8 : ℤ) ≠ 0)
    omega
  have hqmax : q ≤ dval Sl * 2 ^ 40 / Sl.prod := by
    rw [Nat.le_div_iff_mul_le (by rw [← hD]; exact dprod_pos hSp)]
    rw [hD, hN] at hqD; exact hqD
  -- every odd prime of the base accepts `q`
  have hacc : ∀ p ∈ Sl.filter (· ≠ 2), 0 < p ∧ (qTab Sl.prod p).get! (q % p) ≠ 0 := by
    intro p hpm
    obtain ⟨hpS, hp2⟩ := List.mem_filter.1 hpm
    have hp2' : p ≠ 2 := by simpa using hp2
    have hgood := good_of_square hSp (List.mem_toFinset.2 hpS) hp2' hq (hlt p hpS) hx
    rw [hD] at hgood
    exact ⟨(hp p hpS).pos, (qTab_ne (hp p hpS).pos).2 hgood⟩
  unfold sieveBase at h
  simp only at h
  have key := sieveRun_sound hq8lt (by
      intro e he
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 he
      exact (hacc p (List.mem_of_mem_take hpm)).1) h q hqmax hq0 (by
      intro e he
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 he
      exact (hacc p (List.mem_of_mem_take hpm)).2) (by
      intro e he
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 he
      exact (hacc p (List.mem_of_mem_drop hpm)).2)
  -- both squares hold, contradiction
  have hx' : dval Sl + 2 * Sl.prod = dval Sl + 2 * Sl.prod := rfl
  have hsqA : isSq ((dval Sl + 2 * Sl.prod) * q + Sl.prod) = true := by
    refine isSq_of_mul_self (m := x.natAbs) ?_
    have : (((dval Sl + 2 * Sl.prod) * q + Sl.prod : ℕ) : ℤ) = x ^ 2 := by
      rw [hx, hN, hD]; push_cast; ring
    have h3 : ((x.natAbs * x.natAbs : ℕ) : ℤ) = x ^ 2 := by
      rw [Nat.cast_mul, Int.natAbs_mul_self' x]; ring
    exact_mod_cast this.trans h3.symm
  have hT' : 2 * Sl.prod ≤ dval Sl := by rw [← hD, ← hN]; exact hT
  have hsqB : isSq ((dval Sl - 2 * Sl.prod) * q + Sl.prod) = true := by
    refine isSq_of_mul_self (m := y.natAbs) ?_
    have : (((dval Sl - 2 * Sl.prod) * q + Sl.prod : ℕ) : ℤ) = y ^ 2 := by
      rw [hy, hN, hD]; push_cast [Nat.cast_sub hT']; ring
    have h3 : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y ^ 2 := by
      rw [Nat.cast_mul, Int.natAbs_mul_self' y]; ring
    exact_mod_cast this.trans h3.symm
  rw [hsqA, hsqB] at key
  simp at key

end Erdos307
