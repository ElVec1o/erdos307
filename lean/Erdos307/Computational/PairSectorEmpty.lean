import Erdos307.Computational.PairLeaf
import Erdos307.Level60Sectors
import Erdos307.PairSector
import Erdos307.Closed
import Erdos307.Numeral

/-!
# Track B: `PairSectorEmpty` from one finite computation

`pair_sector_empty_of_check`: if the compiled search `pdfs (leaf (mkTabs 1667)) (primesUpTo 1667) 59 0 []`
returns `true`, then `PairSectorEmpty` holds. Everything except that single Boolean is kernel-checked:

* `pair_necessary`: a cycle on `R ∪ {p}` forces the tail bound and the character conditions;
* `leaf_sound`: the leaf refutes both for every `p` above `max R`;
* `pdfs_sound`: the pruned enumeration reaches every `R` in the window;
* `pair_sector_finite`: elements of `R` are `≤ 1667`.

Paper: Proposition `prop:pairclosed`.
-/

namespace Erdos307

open Finset

def primesUpTo (n : ℕ) : List ℕ := (List.range (n + 1)).filter Nat.Prime

theorem mem_primesUpTo {n x : ℕ} : x ∈ primesUpTo n ↔ x.Prime ∧ x ≤ n := by
  unfold primesUpTo
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

theorem primesUpTo_sorted (n : ℕ) : (primesUpTo n).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

/-- A cycle's support has mass `> 2`: `T(U) = (a² + b²)/(ab)` with `a ≠ b`. -/
theorem mass_gt_two_of_cycle {U : Finset ℕ} (hU : ∀ r ∈ U, r.Prime) (hne : U.Nonempty)
    (hc : IsCycle U) : 2 < mass U := by
  obtain ⟨P, Q, hdisj, hUe, h1, h2⟩ := hc
  subst hUe
  have hP : ∀ p ∈ P, p.Prime := fun p hp => hU p (Finset.mem_union_left _ hp)
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => hU p (Finset.mem_union_right _ hp)
  have hpair := (pair_form_iff hP hQ hdisj).2 ⟨0, by simpa using congrArg Int.ofNat h1,
    by simpa using congrArg Int.ofNat h2⟩
  have hpair' : dprod P ^ 2 + dprod Q ^ 2 = csum (P ∪ Q) := by exact_mod_cast hpair
  have hdU := dprod_union_disjoint hdisj
  have hDpos : (0 : ℚ) < dprod (P ∪ Q) := by exact_mod_cast dprod_pos hU
  have hmass : mass (P ∪ Q) = (csum (P ∪ Q) : ℚ) / dprod (P ∪ Q) := recipSum_eq _ hU
  have hneab : dprod P ≠ dprod Q := by
    intro h
    have hcop := coprime_dprod_of_disjoint hP hQ hdisj
    rw [← h] at hcop
    have h1' : dprod P = 1 := (Nat.coprime_self _).1 hcop
    have hP0 : P = ∅ := by
      by_contra hPne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hPne
      have : x ∣ dprod P := Finset.dvd_prod_of_mem _ hx
      rw [h1'] at this
      exact (hP x hx).one_lt.ne' (Nat.dvd_one.1 this)
    have hQ0 : Q = ∅ := by
      by_contra hQne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hQne
      have : x ∣ dprod Q := Finset.dvd_prod_of_mem _ hx
      rw [← h, h1'] at this
      exact (hQ x hx).one_lt.ne' (Nat.dvd_one.1 this)
    subst hP0; subst hQ0; simp at hne
  rw [hmass, lt_div_iff₀ hDpos]
  have : (dprod (P ∪ Q) : ℚ) = dprod P * dprod Q := by exact_mod_cast hdU
  have hc2 : (csum (P ∪ Q) : ℚ) = (dprod P : ℚ) ^ 2 + (dprod Q : ℚ) ^ 2 := by exact_mod_cast hpair'.symm
  rw [this, hc2]
  have : (dprod P : ℚ) ≠ dprod Q := by exact_mod_cast hneab
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.2 this)]

lemma le_getLast_of_sorted {L : List ℕ} (hs : L.Pairwise (· < ·)) (hne : L ≠ []) :
    ∀ x ∈ L, x ≤ L.getLast hne := by
  intro x hx
  have h := List.dropLast_append_getLast hne
  rw [← h] at hs hx
  rw [List.pairwise_append] at hs
  rcases List.mem_append.1 hx with h1 | h1
  · exact (hs.2.2 x h1 _ (by simp)).le
  · simp at h1; exact h1.le

theorem pair_sector_empty_of_check
    (hcheck : pdfs (leaf (mkTabs 1667)) (primesUpTo 1667) 59 0 [] = true) : PairSectorEmpty := by
  intro U hU hcard p hpU hmax hm hcyc
  set R := U.erase p with hR
  have hRp : ∀ r ∈ R, r.Prime := fun r hr => hU r (Finset.mem_of_mem_erase hr)
  have hpP := hU p hpU
  have hpR : p ∉ R := Finset.notMem_erase p U
  have hcardR : R.card = 59 := by rw [hR, Finset.card_erase_of_mem hpU, hcard]
  have hgt := mass_gt_two_of_cycle hU ⟨p, hpU⟩ hcyc
  have hlt : ∀ r ∈ R, r < p := fun r hr =>
    lt_of_le_of_ne (hmax r (Finset.mem_of_mem_erase hr)) (Finset.ne_of_mem_erase hr)
  have hmassR : mass U = mass R + (p : ℚ)⁻¹ := by have := mass_erase hpU; linarith
  -- elements are at most 1667
  have hB : ∀ x ∈ R, x ≤ 1667 := by
    intro x hx
    have hxpos : (0 : ℚ) < x := by exact_mod_cast (hRp x hx).pos
    have hcx : (R.erase x).card = 58 := by rw [Finset.card_erase_of_mem hx, hcardR]
    have hs : mass (R.erase x) ≤ 1.9988 := by
      have h1 := recipSum_le_first_primes (U := R.erase x) (fun r hr => hRp r (Finset.mem_of_mem_erase hr))
      rw [hcx, sum_first58] at h1
      have h2 : (N58 : ℚ) / (P58 : ℚ) ≤ 1.9988 := by unfold N58 P58; norm_num
      unfold mass; linarith
    have hmx : mass R = mass (R.erase x) + (x : ℚ)⁻¹ := by
      have := mass_erase hx; linarith
    have hxp : (p : ℚ)⁻¹ < (x : ℚ)⁻¹ := inv_strictAnti₀ hxpos (by exact_mod_cast hlt x hx)
    have hmass : 2 - mass (R.erase x) ≤ 2 * (x : ℚ)⁻¹ := by linarith
    have := pair_sector_finite hxpos hs hmass
    exact_mod_cast this
  -- the sorted base and its last element
  set L := R.sort (· ≤ ·) with hL
  have hLs : L.Pairwise (· < ·) := Finset.sortedLT_sort R |>.pairwise
  have hLne : L ≠ [] := by
    intro h; have := Finset.length_sort (r := (· ≤ ·)) (s := R); rw [← hL, h] at this
    simp at this; omega
  set r := L.getLast hLne with hr
  have hrL : L.getLast? = some r := List.getLast?_eq_some_getLast hLne
  have hrR : r ∈ R := (Finset.mem_sort (· ≤ ·)).1 (List.getLast_mem hLne)
  have hrp : r < p := hlt r hrR
  have hrmax : ∀ x ∈ R, x ≤ r := fun x hx => le_getLast_of_sorted hLs hLne x ((Finset.mem_sort _).2 hx)
  have hr2 : r ≠ 2 := by
    intro h2
    have hsub : R ⊆ ({2} : Finset ℕ) := by
      intro x hx
      have := hrmax x hx; have := (hRp x hx).two_le
      simp only [Finset.mem_singleton]; omega
    have := Finset.card_le_card hsub
    simp at this; omega
  have hwin : Win L := by
    refine ⟨?_, r, hrL, ?_⟩
    · rw [hL, rsum_sort]; exact hm
    · have hrpos : (0 : ℚ) < r := by exact_mod_cast (hRp r hrR).pos
      have : (p : ℚ)⁻¹ < (r : ℚ)⁻¹ := inv_strictAnti₀ hrpos (by exact_mod_cast hrp)
      rw [hL, rsum_sort]; unfold mass at hmassR hgt; linarith
  have hsub : L.Sublist (primesUpTo 1667) := by
    refine sublist_of_pairwise_lt hLs (primesUpTo_sorted 1667) fun x hx => ?_
    have hx' := (Finset.mem_sort (· ≤ ·)).1 hx
    exact mem_primesUpTo.2 ⟨hRp x hx', hB x hx'⟩
  have hpos : ∀ x ∈ primesUpTo 1667, 0 < x := fun x hx => (mem_primesUpTo.1 hx).1.pos
  have hlen : L.length = 59 := by rw [hL, Finset.length_sort, hcardR]
  have hleaf := pdfs_sound (leaf (mkTabs 1667)) (primesUpTo 1667) (primesUpTo_sorted 1667) hpos 59 0 []
    (by simp [rsum]) hcheck L hsub hlen (by simpa using hwin)
  simp only [List.reverse_nil, List.nil_append] at hleaf
  -- cycle data
  obtain ⟨P, Q, hdisj, hUe, h1, h2⟩ := hcyc
  have hUS : P ∪ Q = R ∪ {p} := by
    rw [hUe]; ext x
    simp only [hR, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · intro hx; by_cases h : x = p
      · exact Or.inr h
      · exact Or.inl ⟨h, hx⟩
    · rintro (⟨-, hx⟩ | rfl)
      · exact hx
      · exact hpU
  obtain ⟨hnec1, hnec2⟩ := pair_necessary hRp hpP hpR hdisj hUS h1 h2
  have hNlt : csum R < 2 * dprod R := by
    have hD : (0 : ℚ) < dprod R := by exact_mod_cast dprod_pos hRp
    have : (csum R : ℚ) / dprod R < 2 := by rw [← recipSum_eq R hRp]; exact hm
    rw [div_lt_iff₀ hD] at this
    exact_mod_cast this
  obtain ⟨ℓ, hℓR, hℓ2, hf, hne⟩ :=
    leaf_sound hRp hB hNlt hrL hr2 (by simpa [hL] using hleaf) p hpP hrp hnec1
  exact hne (@hnec2 ℓ hℓR hℓ2 hf)

end Erdos307
