import Erdos307.Sixty
import Erdos307.JacobiAlg
import Erdos307.Level60Sectors

/-!
# Level 60, tail sector: the base enumeration, killed or listed

`enumA` is the scaled (integer) form of the `Sixty` search, returning the pools `V` (the `20` free primes
above `167`) of every `59`-prime base `S = forced39 ∪ V` with `T(S) ≥ 2`, in lexicographic order.
`enumA_complete` shows every such pool is returned. Its length (49,961) is checked by the kernel.

Paper: Proposition `prop:sectors`, Proposition `prop:tailkill`.
-/

namespace Erdos307

def enumA : List ℕ → ℕ → ℕ → List ℕ → List (List ℕ)
  | _, 0, cur, chosen => if thrM ≤ cur then [chosen.reverse] else []
  | [], _ + 1, _, _ => []
  | x :: xs, need + 1, cur, chosen =>
    if cur + wsum ((x :: xs).take (need + 1)) < thrM then []
    else enumA xs need (cur + wt x) (x :: chosen) ++ enumA xs (need + 1) cur chosen

lemma wsum_sublist_le {l V : List ℕ} (hs : l.Pairwise (· < ·)) (hpos : ∀ x ∈ l, 0 < x)
    (hdvd : ∀ x ∈ l, x ∣ Mscale) (hV : V.Sublist l) : wsum V ≤ wsum (l.take V.length) := by
  have hVp : ∀ x ∈ V, 0 < x := fun x hx => hpos x (hV.subset hx)
  have hVd : ∀ x ∈ V, x ∣ Mscale := fun x hx => hdvd x (hV.subset hx)
  have htp : ∀ x ∈ l.take V.length, 0 < x := fun x hx => hpos x (List.mem_of_mem_take hx)
  have htd : ∀ x ∈ l.take V.length, x ∣ Mscale := fun x hx => hdvd x (List.mem_of_mem_take hx)
  have h := rsum_sublist_le hs hpos hV
  have h1 := wsum_cast hVp hVd
  have h2 := wsum_cast htp htd
  have hM : (0 : ℚ) ≤ Mscale := by positivity
  have : (wsum V : ℚ) ≤ (wsum (l.take V.length) : ℚ) := by
    rw [h1, h2]; exact mul_le_mul_of_nonneg_left h hM
  exact_mod_cast this

theorem enumA_complete : ∀ (l : List ℕ), l.Pairwise (· < ·) → (∀ x ∈ l, 0 < x) → (∀ x ∈ l, x ∣ Mscale) →
    ∀ (need cur : ℕ) (chosen : List ℕ) (V : List ℕ), V.Sublist l → V.length = need →
    thrM ≤ cur + wsum V → chosen.reverse ++ V ∈ enumA l need cur chosen := by
  intro l
  induction l with
  | nil =>
    intro _ _ _ need cur chosen V hV hlen hthr
    have hVnil : V = [] := List.sublist_nil.mp hV
    subst hVnil
    simp only [List.length_nil] at hlen
    subst hlen
    simp [enumA, wsum] at hthr ⊢
    exact hthr
  | cons x xs ih =>
    intro hs hpos hdvd need cur chosen V hV hlen hthr
    obtain ⟨hxlt, hstail⟩ := List.pairwise_cons.mp hs
    have hptail : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    have hdtail : ∀ y ∈ xs, y ∣ Mscale := fun y hy => hdvd y (List.mem_cons_of_mem _ hy)
    cases need with
    | zero =>
      have hVnil : V = [] := List.length_eq_zero_iff.mp hlen
      subst hVnil
      simp [enumA, wsum] at hthr ⊢
      exact hthr
    | succ n =>
      unfold enumA
      by_cases hprune : cur + wsum ((x :: xs).take (n + 1)) < thrM
      · exfalso
        have hdom : wsum V ≤ wsum ((x :: xs).take (n + 1)) := by
          have := wsum_sublist_le hs hpos hdvd hV
          rwa [hlen] at this
        omega
      · rw [if_neg hprune]
        cases hV with
        | cons _ hV' =>
          exact List.mem_append_right _ (ih hstail hptail hdtail (n + 1) cur chosen V hV' hlen hthr)
        | cons_cons _ hV' =>
          rename_i V'
          have hlen' : V'.length = n := by simpa using hlen
          have hthr' : thrM ≤ (cur + wt x) + wsum V' := by
            simp only [wsum, List.map_cons, List.sum_cons] at hthr ⊢
            omega
          have hL : (x :: chosen).reverse ++ V' = chosen.reverse ++ x :: V' := by simp
          have := ih hstail hptail hdtail n (cur + wt x) (x :: chosen) V' hV' hlen' hthr'
          rw [hL] at this
          exact List.mem_append_left _ this

/-! ### The leaf: killed by a Jacobi symbol, or listed -/

/-- Fuel for `jacF`: the algorithm needs at most about `2 * bits` steps. -/
def jacFuel : ℕ := 4000

/-- `A` or `B` itself has Jacobi symbol `-1` against `D`: no certificate needed. -/
def directKilled (V : List ℕ) : Bool :=
  let l := forced39 ++ V
  let D := l.prod
  let N := dval l
  killCheck (N + 2 * D) D (N + 2 * D) jacFuel || killCheck (N - 2 * D) D (N - 2 * D) jacFuel

/-- A divisor `c` of `A` or of `B` has Jacobi symbol `-1` against `D`. -/
def certKilled (V : List ℕ) (c : ℕ) : Bool :=
  let l := forced39 ++ V
  let D := l.prod
  let N := dval l
  killCheck (N + 2 * D) D c jacFuel || killCheck (N - 2 * D) D c jacFuel

def leafKilled (V : List ℕ) (c : ℕ) : Bool := directKilled V || certKilled V c

/-- Check over the pools in enumeration order: a pool killed directly consumes nothing; otherwise it
consumes one certificate, and if that certificate fails it must be the next listed survivor. -/
def checkAll : List (List ℕ) → List ℕ → List (List ℕ) → Bool
  | [], [], [] => true
  | V :: vs, cs, L =>
    if directKilled V then checkAll vs cs L
    else match cs with
      | c :: cs' =>
        if certKilled V c then checkAll vs cs' L
        else match L with
          | s :: L' => decide (V = s) && checkAll vs cs' L'
          | [] => false
      | [] => false
  | _, _, _ => false

theorem checkAll_sound : ∀ (pools : List (List ℕ)) (certs : List ℕ) (L : List (List ℕ)),
    checkAll pools certs L = true → ∀ V ∈ pools, (∃ c, leafKilled V c = true) ∨ V ∈ L := by
  intro pools
  induction pools with
  | nil => intro _ _ _ V hV; simp at hV
  | cons W ws ih =>
    intro certs L h V hV
    unfold checkAll at h
    by_cases hd : directKilled W = true
    · rw [if_pos hd] at h
      rcases List.mem_cons.1 hV with rfl | hmem
      · exact Or.inl ⟨0, by simp [leafKilled, hd]⟩
      · exact ih certs L h V hmem
    · rw [if_neg hd] at h
      cases certs with
      | nil => simp at h
      | cons c cs =>
        simp only at h
        by_cases hk : certKilled W c = true
        · rw [if_pos hk] at h
          rcases List.mem_cons.1 hV with rfl | hmem
          · exact Or.inl ⟨c, by simp [leafKilled, hk]⟩
          · exact ih cs L h V hmem
        · rw [if_neg hk] at h
          cases L with
          | nil => simp at h
          | cons s L' =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨hWs, hrest⟩ := h
            rcases List.mem_cons.1 hV with rfl | hmem
            · exact Or.inr (by simp [hWs])
            · rcases ih cs L' hrest V hmem with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (List.mem_cons_of_mem _ h2)


/-! ### From the list value to the Finset statement -/

lemma dprod_toFinset_list {l : List ℕ} (hl : l.Nodup) : dprod l.toFinset = l.prod := by
  unfold dprod
  rw [List.prod_toFinset _ hl]; simp

lemma csum_toFinset_list {l : List ℕ} (hl : l.Nodup) : csum l.toFinset = dval l := by
  unfold csum dval
  rw [dprod_toFinset_list hl, List.sum_toFinset _ hl]

theorem leafKilled_notTail {V : List ℕ} {c : ℕ} {S : Finset ℕ}
    (hS : S = (forced39 ++ V).toFinset) (hnd : (forced39 ++ V).Nodup)
    (hT : 2 * dprod S ≤ csum S) (hk : leafKilled V c = true) (q : ℕ) : ¬ TailArith S q := by
  rintro ⟨x, y, -, -, hx, hy⟩
  have hD : dprod S = (forced39 ++ V).prod := by rw [hS]; exact dprod_toFinset_list hnd
  have hN : csum S = dval (forced39 ++ V) := by rw [hS]; exact csum_toFinset_list hnd
  unfold leafKilled directKilled certKilled at hk
  simp only [Bool.or_eq_true] at hk
  have hA : ((dval (forced39 ++ V) + 2 * (forced39 ++ V).prod : ℕ) : ℤ)
      = (csum S : ℤ) + 2 * dprod S := by rw [hN, hD]; push_cast; ring
  have hB : (((dval (forced39 ++ V) - 2 * (forced39 ++ V).prod : ℕ)) : ℤ)
      = (csum S : ℤ) - 2 * dprod S := by
    rw [Nat.cast_sub (by rw [← hN, ← hD]; exact hT), hN, hD]; push_cast; ring
  have hDz : (((forced39 ++ V).prod : ℕ) : ℤ) = dprod S := by rw [hD]
  rcases hk with (h | h) | (h | h)
  · exact killCheck_sound h x q (by rw [hA, hDz]; exact hx)
  · exact killCheck_sound h y q (by rw [hB, hDz]; exact hy)
  · exact killCheck_sound h x q (by rw [hA, hDz]; exact hx)
  · exact killCheck_sound h y q (by rw [hB, hDz]; exact hy)

/-! ### Every window base is a listed pool -/

theorem window_pool {S : Finset ℕ} (hU : ∀ r ∈ S, r.Prime) (hc : S.card = 59)
    (hT : (2 : ℚ) ≤ ∑ r ∈ S, (r : ℚ)⁻¹) :
    ∃ V ∈ enumA pool99 20 0 [], S = (forced39 ++ V).toFinset ∧ (forced39 ++ V).Nodup := by
  have hforced : ∀ p ∈ forced39, p ∈ S := fun p hp =>
    forced_mem hU hc hT (forced39_facts p hp).1 (forced39_facts p hp).2
  have hFsub : forced39.toFinset ⊆ S := fun p hp => hforced p (List.mem_toFinset.mp hp)
  set W := S \ forced39.toFinset with hW
  have hVcard : W.card = 20 := by
    rw [hW, Finset.card_sdiff, Finset.inter_eq_left.mpr hFsub, hc, forced39_card]
  have hVpool : ∀ r ∈ W, r ∈ pool99 := by
    intro r hrV
    have hrU : r ∈ S := (Finset.mem_sdiff.mp hrV).1
    have hrF : r ∉ forced39.toFinset := (Finset.mem_sdiff.mp hrV).2
    have hrp : r.Prime := hU r hrU
    have hle : r ≤ 795 := elt_le_795 hU hc hT hrU
    have hgt : 167 < r := by
      by_contra hle167
      have h167 : r ≤ 167 := by omega
      exact hrF (List.mem_toFinset.mpr (forced39_complete r (by omega) hrp))
    exact pool99_complete r (by omega) hrp hgt
  set V := W.sort (· ≤ ·) with hV
  have hVsorted : V.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  have hVsub : V.Sublist pool99 := by
    refine sublist_of_pairwise_lt hVsorted pool99_pairwise ?_
    intro x hx
    exact hVpool x ((Finset.mem_sort (· ≤ ·)).mp hx)
  have hVlen : V.length = 20 := by rw [hV, Finset.length_sort, hVcard]
  have hUsplit : forced39.toFinset ∪ W = S := Finset.union_sdiff_of_subset hFsub
  have hFdisj : Disjoint forced39.toFinset W := Finset.disjoint_sdiff
  have hthrV : thr ≤ 0 + rsum V := by
    have hsplitsum : ∑ r ∈ forced39.toFinset, (r : ℚ)⁻¹ + ∑ r ∈ W, (r : ℚ)⁻¹
        = ∑ r ∈ S, (r : ℚ)⁻¹ := by
      rw [← Finset.sum_union hFdisj, hUsplit]
    rw [hV, rsum_sort]
    unfold thr
    rw [← forced39_sum]
    linarith
  have hVp : ∀ x ∈ V, 0 < x := fun x hx => pool99_pos x (hVsub.subset hx)
  have hVd : ∀ x ∈ V, x ∣ Mscale := fun x hx => pool99_dvd x (hVsub.subset hx)
  have hthrN : thrM ≤ 0 + wsum V := by
    have h1 := wsum_cast hVp hVd
    have h2 : (thrM : ℚ) ≤ (wsum V : ℚ) := by
      rw [thrM_cast, h1]
      have hM : (0 : ℚ) ≤ Mscale := by positivity
      exact mul_le_mul_of_nonneg_left (by simpa using hthrV) hM
    exact_mod_cast (by simpa using h2 : (thrM : ℚ) ≤ ((0 + wsum V : ℕ) : ℚ))
  have hmem := enumA_complete pool99 pool99_pairwise pool99_pos pool99_dvd 20 0 [] V hVsub hVlen hthrN
  refine ⟨V, by simpa using hmem, ?_, ?_⟩
  · have hVfin : V.toFinset = W := by rw [hV]; exact Finset.sort_toFinset _ _
    rw [List.toFinset_append, hVfin, hUsplit]
  · rw [List.nodup_append]
    refine ⟨forced39_nodup, (Finset.sort_nodup _ _), ?_⟩
    intro a ha b hb hab
    have hbW : b ∈ W := (Finset.mem_sort (· ≤ ·)).1 hb
    rw [← hab] at hbW
    exact (Finset.mem_sdiff.1 hbW).2 (List.mem_toFinset.2 ha)

/-- **`TailSectorEmpty` from a kill certificate stream and a finite list of survivor pools.**
If `checkAll` accepts the pools of `enumA` with the certificates `certs` and the survivor list `L`
(every pool is killed by a Jacobi symbol or is the next element of `L`), then the tail sector is empty
as soon as it is empty over the listed pools. -/
theorem tail_of_survivors {certs : List ℕ} {L : List (List ℕ)}
    (hcheck : checkAll (enumA pool99 20 0 []) certs L = true)
    (hL : ∀ V ∈ L, (forced39 ++ V).Nodup → (∀ p ∈ forced39 ++ V, p.Prime) → 2 ∈ forced39 ++ V →
      2 * dprod (forced39 ++ V).toFinset ≤ csum (forced39 ++ V).toFinset →
      ¬ CycleLow (forced39 ++ V).toFinset ∧ ∀ q : ℕ, q.Prime →
      (∀ s ∈ forced39 ++ V, s < q) →
      ¬ (q * dprod (forced39 ++ V).toFinset ≤ csum (forced39 ++ V).toFinset * 2 ^ 40 ∧
        TailArith (forced39 ++ V).toFinset q)) : TailSectorEmpty := by
  intro S hSp h2S hcard hmass
  obtain ⟨V, hV, hSV, hnd⟩ := window_pool hSp hcard hmass
  have hD : (0 : ℚ) < dprod S := by exact_mod_cast dprod_pos hSp
  have hT : 2 * dprod S ≤ csum S := by
    have : (2 : ℚ) ≤ (csum S : ℚ) / dprod S := by
      rw [← recipSum_eq S hSp]; exact hmass
    rw [le_div_iff₀ hD] at this
    exact_mod_cast (by linarith : (2 * dprod S : ℚ) ≤ csum S)
  rcases checkAll_sound _ _ _ hcheck V hV with ⟨c, hk⟩ | hmem
  · exact Or.inl fun q _ _ => leafKilled_notTail hSV hnd hT hk q
  · subst hSV
    have hH := hL V hmem hnd (fun p hp => hSp p (List.mem_toFinset.2 hp)) (List.mem_toFinset.1 h2S) hT
    exact Or.inr ⟨hH.1, fun q hq hlt => hH.2 q hq fun s hs => hlt s (List.mem_toFinset.2 hs)⟩
  
end Erdos307
