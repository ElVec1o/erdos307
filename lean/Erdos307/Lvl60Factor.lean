import Erdos307.Frame
import Erdos307.PairForm

/-!
# Single-tail families are decided by factoring

`prop:lvl60factor`. Let `S` be a set of primes containing `2`, `D = ∏ S`, `N = csum S = D'`,
`A = N + 2D`, and let `q ∉ S` be a prime such that `S ∪ {q}` splits into a two-cycle `(P, Q)`
(`csum P = ∏ Q`, `csum Q = ∏ P`). Then

* `A` is odd and coprime to `D`;
* `x = ∏ P + ∏ Q` satisfies `x² = A q + D` and `0 < x < A`.

The bound `x < A` needs no numerical input about the base: the side `R` of the cycle not containing
`q` lies in `S` and `∏(other side) = csum R ≤ csum S = N`, so `q ≤ N`, whence
`x² = Aq + D ≤ AN + D < A²`.

Not formalised: the count `2^ω(A)` of square roots of `D` mod `A` and the Tonelli-Shanks/CRT
computation of them (a statement about an algorithm, not about the cycle).

Paper: Proposition `prop:lvl60factor`.
-/

namespace Erdos307

open Finset

/-- `csum` is monotone along inclusion of prime sets. -/
lemma csum_mono_sub {Q S : Finset ℕ} (hQS : Q ⊆ S) (hS : ∀ p ∈ S, p.Prime) :
    csum Q ≤ csum S := by
  have hdv : dprod Q ∣ dprod S := Finset.prod_dvd_prod_of_subset _ _ _ hQS
  have hle : dprod Q ≤ dprod S := Nat.le_of_dvd (dprod_pos hS) hdv
  unfold csum
  calc ∑ p ∈ Q, dprod Q / p ≤ ∑ p ∈ Q, dprod S / p :=
        Finset.sum_le_sum fun p _ => Nat.div_le_div_right hle
    _ ≤ ∑ p ∈ S, dprod S / p := Finset.sum_le_sum_of_subset hQS

/-- `N = csum S` is odd when `2 ∈ S`. -/
lemma csum_odd_of_two_mem {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S) : Odd (csum S) := by
  have hX : ∀ p ∈ S.erase 2, p.Prime := fun p hp => hS p (Finset.mem_of_mem_erase hp)
  have hSe : S = S.erase 2 ∪ {2} := by
    ext x; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · intro hx; by_cases h : x = 2 <;> simp [h, hx]
    · rintro (⟨-, hx⟩ | rfl) <;> assumption
  have hodd : Odd (dprod (S.erase 2)) := by
    unfold dprod
    refine Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun p hp => ?_
    have hp' := Finset.mem_erase.1 hp
    exact (hX p hp).odd_of_ne_two hp'.1
  rw [hSe, csum_insert_prime (Finset.notMem_erase 2 S) (by norm_num)]
  exact (Even.add_odd (by exact ⟨_, by ring⟩) hodd)

/-- `gcd(A, D) = 1` where `A = N + 2D`. -/
lemma coprime_A_D {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Nat.Coprime (csum S + 2 * dprod S) (dprod S) := by
  apply Nat.coprime_of_dvd
  intro p hp hpA hpD
  have hpS : p ∈ S := by
    unfold dprod at hpD
    obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hpD
    rwa [(Nat.prime_dvd_prime_iff_eq hp (hS r hr)).1 hpr]
  have hpN : p ∣ csum S := by
    have : p ∣ 2 * dprod S := Dvd.dvd.mul_left hpD 2
    exact (Nat.dvd_add_left this).1 hpA
  have hX : ∀ r ∈ S.erase p, r.Prime := fun r hr => hS r (Finset.mem_of_mem_erase hr)
  have hSe : S = S.erase p ∪ {p} := by
    ext x; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · intro hx; by_cases h : x = p <;> simp [h, hx]
    · rintro (⟨-, hx⟩ | rfl) <;> assumption
  rw [hSe, csum_insert_prime (Finset.notMem_erase p S) hp.pos] at hpN
  have hd : p ∣ dprod (S.erase p) := (Nat.dvd_add_right (Dvd.intro _ rfl)).1 hpN
  unfold dprod at hd
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
  have := (Nat.prime_dvd_prime_iff_eq hp (hX r hr)).1 hpr
  exact (Finset.notMem_erase p S) (this ▸ hr)

/-- Core, with `q` on the `P` side. -/
lemma lvl60_core {S P Q : Finset ℕ} {q : ℕ} (hS : ∀ p ∈ S, p.Prime) (hq : q.Prime) (hqS : q ∉ S)
    (hdisj : Disjoint P Q) (hU : P ∪ Q = S ∪ {q}) (hqP : q ∈ P)
    (h1 : csum P = dprod Q) (h2 : csum Q = dprod P) :
    (dprod P + dprod Q) ^ 2 = (csum S + 2 * dprod S) * q + dprod S ∧
      0 < dprod P + dprod Q ∧ dprod P + dprod Q < csum S + 2 * dprod S ∧
      dprod P * dprod Q = dprod S * q := by
  have hU' : ∀ p ∈ P ∪ Q, p.Prime := by
    rw [hU]; intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact hS p h
    · rw [Finset.mem_singleton.1 h]; exact hq
  have hP : ∀ p ∈ P, p.Prime := fun p hp => hU' p (Finset.mem_union_left _ hp)
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => hU' p (Finset.mem_union_right _ hp)
  have hD : 0 < dprod S := dprod_pos hS
  have hdS : Disjoint S ({q} : Finset ℕ) := by simpa [Finset.disjoint_singleton_right] using hqS
  have hcU : csum (S ∪ {q}) = q * csum S + dprod S := csum_insert_prime hqS hq.pos
  have hdU : dprod (S ∪ {q}) = dprod S * q := by
    rw [dprod_union_disjoint hdS]; simp [dprod]
  -- the pair equation with k = 0
  have hpair := (pair_form_iff hP hQ hdisj).2 ⟨0, by simpa using congrArg (Int.ofNat) h1, by
    simpa using congrArg (Int.ofNat) h2⟩
  rw [hU, hcU] at hpair
  have hab : dprod P * dprod Q = dprod S * q := by
    rw [← dprod_union_disjoint hdisj, hU, hdU]
  have hpair' : dprod P ^ 2 + dprod Q ^ 2 = q * csum S + dprod S := by exact_mod_cast hpair
  have hx : (dprod P + dprod Q) ^ 2 = (csum S + 2 * dprod S) * q + dprod S := by
    nlinarith [hpair', hab]
  refine ⟨hx, ?_, ?_, hab⟩
  · have := dprod_pos hP; omega
  · -- q ≤ N
    have hQS : Q ⊆ S := by
      intro y hy
      have : y ∈ S ∪ {q} := hU ▸ Finset.mem_union_right _ hy
      rcases Finset.mem_union.1 this with h | h
      · exact h
      · exfalso
        rw [Finset.mem_singleton.1 h] at hy
        exact Finset.disjoint_left.1 hdisj hqP hy
    have hqa : q ≤ dprod P := Nat.le_of_dvd (dprod_pos hP) (by
      unfold dprod; exact Finset.dvd_prod_of_mem _ hqP)
    have hqN : q ≤ csum S := by
      calc q ≤ dprod P := hqa
        _ = csum Q := h2.symm
        _ ≤ csum S := csum_mono_sub hQS hS
    by_contra hge
    replace hge := not_lt.1 hge
    set A := csum S + 2 * dprod S with hA
    have hsq : A ^ 2 ≤ (dprod P + dprod Q) ^ 2 := Nat.pow_le_pow_left hge 2
    rw [hx] at hsq
    have : A * q ≤ A * csum S := Nat.mul_le_mul_left _ hqN
    have hAN : A * csum S + dprod S < A ^ 2 := by
      have : A ^ 2 = A * csum S + A * (2 * dprod S) := by rw [hA]; ring
      have h3 : dprod S < A * (2 * dprod S) := by
        have : 1 < A := by rw [hA]; omega
        nlinarith
      omega
    omega

/-- **`prop:lvl60factor`.** For a two-cycle supported on `S ∪ {q}`: `A = N + 2D` is odd and coprime
to `D`, and `x = ∏P + ∏Q` satisfies `x² = Aq + D` with `0 < x < A`. -/
theorem lvl60_factor {S P Q : Finset ℕ} {q : ℕ} (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S)
    (hq : q.Prime) (hqS : q ∉ S) (hdisj : Disjoint P Q) (hU : P ∪ Q = S ∪ {q})
    (h1 : csum P = dprod Q) (h2' : csum Q = dprod P) :
    Odd (csum S + 2 * dprod S) ∧ Nat.Coprime (csum S + 2 * dprod S) (dprod S) ∧
      ∃ x : ℕ, x ^ 2 = (csum S + 2 * dprod S) * q + dprod S ∧ 0 < x ∧ x < csum S + 2 * dprod S := by
  refine ⟨?_, coprime_A_D hS, ?_⟩
  · exact (csum_odd_of_two_mem hS h2).add_even ⟨dprod S, by ring⟩
  · have hqU : q ∈ P ∪ Q := hU ▸ Finset.mem_union_right _ (Finset.mem_singleton_self q)
    rcases Finset.mem_union.1 hqU with hqP | hqQ
    · obtain ⟨hx, hp, hl, -⟩ := lvl60_core hS hq hqS hdisj hU hqP h1 h2'
      exact ⟨_, hx, hp, hl⟩
    · obtain ⟨hx, hp, hl, -⟩ := lvl60_core hS hq hqS hdisj.symm (by rwa [Finset.union_comm]) hqQ h2' h1
      exact ⟨_, by rwa [add_comm] at hx, by omega, by omega⟩

/-- `prop:lvl60factor`, with the two factors exposed: `∏P · ∏Q = D q`, `x = ∏P + ∏Q`, so
`y = ∏P - ∏Q` satisfies `y² = B q + D` with `B = N - 2D` (the minus layer). -/
theorem lvl60_factor_ab {S P Q : Finset ℕ} {q : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hq : q.Prime) (hqS : q ∉ S) (hdisj : Disjoint P Q) (hU : P ∪ Q = S ∪ {q})
    (h1 : csum P = dprod Q) (h2' : csum Q = dprod P) :
    ∃ a b : ℕ, a * b = dprod S * q ∧ 0 < a + b ∧ a + b < csum S + 2 * dprod S ∧
      (a + b) ^ 2 = (csum S + 2 * dprod S) * q + dprod S := by
  have hqU : q ∈ P ∪ Q := hU ▸ Finset.mem_union_right _ (Finset.mem_singleton_self q)
  rcases Finset.mem_union.1 hqU with hqP | hqQ
  · obtain ⟨hx, hp, hl, hab⟩ := lvl60_core hS hq hqS hdisj hU hqP h1 h2'
    exact ⟨_, _, hab, hp, hl, hx⟩
  · obtain ⟨hx, hp, hl, hab⟩ :=
      lvl60_core hS hq hqS hdisj.symm (by rwa [Finset.union_comm]) hqQ h2' h1
    exact ⟨_, _, hab, hp, hl, hx⟩

end Erdos307
