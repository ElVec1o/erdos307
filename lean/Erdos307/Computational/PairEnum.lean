import QNative.PairCore
import Erdos307.Sixty

/-!
# Track B, M2: soundness of the pair-sector base enumeration

A pruned DFS over a sorted list `l` of primes that visits every `K`-subset `R` of `l` in the *window*
`T(R) < 2 < T(R) + 1/max R`, calling an abstract `leaf` on each (ascending list). `pdfs_sound` says: if the
search returns `true` then `leaf R = true` for every such `R`. The leaf is a parameter, so the enumeration
logic is proved once, in the kernel, independent of what is checked at a leaf (obligation (b)).

This file has no `native_decide`: it is the V1 half of the V2 pair-sector checker.

Paper: Proposition `prop:pairclosed`.
-/

namespace Erdos307

theorem rsumN_eq : rsumN = rsum := rfl

/-- The window: mass below `2`, and above `2` once the reciprocal of the largest element is added. -/
def Win (L : List ℕ) : Prop :=
  rsum L < 2 ∧ ∃ r, L.getLast? = some r ∧ 2 < rsum L + (r : ℚ)⁻¹

theorem pdfs_sound (leaf : List ℕ → Bool) : ∀ (l : List ℕ), l.Pairwise (· < ·) → (∀ x ∈ l, 0 < x) →
    ∀ (need : ℕ) (cur : ℚ) (chosen : List ℕ), cur = rsum chosen →
    pdfs leaf l need cur chosen = true →
    ∀ V : List ℕ, V.Sublist l → V.length = need → Win (chosen.reverse ++ V) →
    leaf (chosen.reverse ++ V) = true := by
  intro l
  induction l with
  | nil =>
    intro _ _ need cur chosen hcur hd V hV hlen hw
    have hVnil : V = [] := List.sublist_nil.mp hV
    subst hVnil
    simp only [List.length_nil] at hlen
    subst hlen
    rw [pdfs] at hd
    obtain ⟨h1, r, hr, h2⟩ := hw
    have hrs : rsum (chosen.reverse ++ []) = cur := by
      rw [List.append_nil, hcur]; exact rsum_perm (List.reverse_perm chosen)
    rw [hrs] at h1 h2
    have hhead : chosen.head? = some r := by
      simpa [List.getLast?_reverse] using hr
    rw [if_pos ⟨h1, r, hhead, h2⟩] at hd
    simpa using hd
  | cons x xs ih =>
    intro hs hpos need cur chosen hcur hd V hV hlen hw
    obtain ⟨hxlt, hstail⟩ := List.pairwise_cons.mp hs
    have hptail : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    have hrs : ∀ W : List ℕ, rsum (chosen.reverse ++ W) = cur + rsum W := by
      intro W; rw [rsum_append, hcur]
      congr 1; exact rsum_perm (List.reverse_perm chosen)
    cases need with
    | zero =>
      have hVnil : V = [] := List.length_eq_zero_iff.mp hlen
      subst hVnil
      rw [pdfs] at hd
      obtain ⟨h1, r, hr, h2⟩ := hw
      rw [hrs] at h1 h2
      simp only [rsum, List.map_nil, List.sum_nil, add_zero] at h1 h2
      have hhead : chosen.head? = some r := by
        simpa [List.getLast?_reverse] using hr
      have h1' : cur < 2 := by simpa [rsum] using h1
      have h2' : 2 < cur + (r : ℚ)⁻¹ := by simpa [rsum] using h2
      rw [if_pos ⟨h1', r, hhead, h2'⟩] at hd
      simpa using hd
    | succ n =>
      rw [pdfs] at hd
      simp only [rsumN_eq] at hd
      by_cases hprune : 2 ≤ cur ∨ cur + rsum ((x :: xs).take (n + 1)) + (x : ℚ)⁻¹ ≤ 2
      · exfalso
        obtain ⟨hw1, r, hr, hw2⟩ := hw
        have hdom : rsum V ≤ rsum ((x :: xs).take (n + 1)) := by
          have := rsum_sublist_le hs hpos hV
          rwa [hlen] at this
        have hVne : V ≠ [] := by intro h; subst h; simp at hlen
        have hrV : r ∈ V := by
          have : (chosen.reverse ++ V).getLast? = V.getLast? :=
            List.getLast?_append_of_ne_nil _ hVne
          rw [this] at hr
          exact List.mem_of_getLast? hr
        have hrx : x ≤ r := by
          have hmem : r ∈ x :: xs := hV.subset hrV
          rcases List.mem_cons.1 hmem with rfl | hm
          · exact le_rfl
          · exact (hxlt r hm).le
        have hxpos : 0 < x := hpos x (List.mem_cons_self ..)
        have hinv : (r : ℚ)⁻¹ ≤ (x : ℚ)⁻¹ := inv_cast_le hxpos hrx
        have hnn : 0 ≤ rsum V := by
          unfold rsum
          refine List.sum_nonneg fun a ha => ?_
          obtain ⟨y, _, rfl⟩ := List.mem_map.1 ha
          positivity
        rw [hrs] at hw1 hw2
        rcases hprune with hp | hp <;> linarith [hdom, hinv, hw1, hw2, hp, hnn]
      · rw [if_neg hprune, Bool.and_eq_true] at hd
        obtain ⟨h1, h2⟩ := hd
        cases hV with
        | cons _ hV' =>
          exact ih hstail hptail (n + 1) cur chosen hcur h2 V hV' hlen hw
        | cons_cons _ hV' =>
          rename_i V'
          have hlen' : V'.length = n := by simpa using hlen
          have hcur' : cur + (x : ℚ)⁻¹ = rsum (x :: chosen) := by rw [rsum_cons, hcur, add_comm]
          have hL : (x :: chosen).reverse ++ V' = chosen.reverse ++ x :: V' := by simp
          have := ih hstail hptail n (cur + (x : ℚ)⁻¹) (x :: chosen) hcur' h1 V' hV' hlen'
            (by rw [hL]; exact hw)
          rwa [hL] at this

end Erdos307
