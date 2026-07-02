import Mathlib
import Erdos307.Rigidity
import Erdos307.Barrier
import Erdos307.Capstone
import Erdos307.Extremal
import Erdos307.Numeral
import Erdos307.Closed

/-!
# Erdős #307 — closing the 59-prime level: `|P ∪ Q| ≥ 60`

Formalization of Proposition `close59` of the note.  Structure:

* Any solution has `T(U) = ∑_{r∈U} 1/r ≥ 2` on the (disjoint) support `U = P ∪ Q`.
* If `|U| = 59` then every prime `p ≤ 167` lies in `U` (else `T(U) ≤ S₆₀ − 1/p < 2`),
  and every element is `≤ 795` (else `T(U) ≤ S₅₈ + 1/796 < 2`).  So `U` is the 39
  forced primes plus 20 primes from the 99-element pool `(167, 795]`.
* A solution supported on `U` forces `csum U + 2·dprod U = (dprod P + dprod Q)²`
  (the Pythagorean/plus square), in particular a perfect square.
* A pruned DFS over the pool (`dfs`, proven sound: it covers *every* qualifying
  20-subset) checks by `native_decide` that `csum U + 2·dprod U` is a non-square
  for each of the 49,961 admissible supports.  Contradiction.

The only non-logical input is `native_decide` (the DFS run + small decidable facts),
consistent with the numeral tier of `Erdos307.Numeral`.
-/

namespace Erdos307

open Finset

/-! ## The forced primes, the pool, and the threshold -/

/-- The 39 primes `≤ 167` — forced into any 59-element support with `T > 2`. -/
def forced39 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167]

/-- The 99 primes in `(167, 795]` — the pool for the 20 free slots. -/
def pool99 : List ℕ :=
  [173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257,
   263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353,
   359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449,
   457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563,
   569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
   659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761,
   769, 773, 787]

/-- Reciprocal sum of a list. -/
def rsum (l : List ℕ) : ℚ := (l.map fun p => (p : ℚ)⁻¹).sum

/-- Threshold: the 20 pool primes must contribute mass `≥ thr` for `T(U) ≥ 2`. -/
def thr : ℚ := 2 - rsum forced39

/-- The plus-square value `csum + 2·dprod`, computed on a list. -/
def plusVal (l : List ℕ) : ℕ := (l.map fun p => l.prod / p).sum + 2 * l.prod

/-- Boolean non-squareness via `Nat.sqrt`. -/
def nsqB (n : ℕ) : Bool := decide (Nat.sqrt n * Nat.sqrt n ≠ n)

lemma nsqB_false_of_isSquare {n : ℕ} (h : IsSquare n) : nsqB n = false := by
  obtain ⟨k, hk⟩ := h
  subst hk
  simp [nsqB, Nat.sqrt_eq]

/-! ## List lemmas -/

lemma rsum_nil : rsum [] = 0 := rfl

lemma rsum_cons (x : ℕ) (l : List ℕ) : rsum (x :: l) = (x : ℚ)⁻¹ + rsum l := by
  simp [rsum]

lemma rsum_append (l₁ l₂ : List ℕ) : rsum (l₁ ++ l₂) = rsum l₁ + rsum l₂ := by
  simp [rsum]

lemma rsum_perm {l l' : List ℕ} (h : l.Perm l') : rsum l = rsum l' :=
  (h.map _).sum_eq

lemma plusVal_perm {l l' : List ℕ} (h : l.Perm l') : plusVal l = plusVal l' := by
  unfold plusVal
  rw [h.prod_eq, (h.map fun p => l'.prod / p).sum_eq]

/-- Domination: over a `<`-sorted list of positives, any `k`-sublist's reciprocal sum
is at most that of the first `k` elements. -/
lemma rsum_take_shift {x : ℕ} {xs : List ℕ} (hs : (x :: xs).Sorted (· < ·))
    (hx : 0 < x) (k : ℕ) : rsum (xs.take k) ≤ rsum ((x :: xs).take k) := by
  cases k with
  | zero => simp [rsum]
  | succ j =>
    -- (x :: xs).take (j+1) = x :: xs.take j
    show rsum (xs.take (j + 1)) ≤ rsum (x :: xs.take j)
    rw [List.take_succ, rsum_append, rsum_cons]
    have hopt : rsum (xs[j]?.toList) ≤ (x : ℚ)⁻¹ := by
      cases hg : xs[j]? with
      | none => simp [rsum]; positivity
      | some y =>
        have hy : y ∈ xs := List.mem_of_getElem? hg
        have hxy : x < y := (List.sorted_cons.mp hs).1 y hy
        have hy0 : (0 : ℚ) < x := by exact_mod_cast hx
        simp only [Option.toList, rsum, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
        gcongr
        · exact_mod_cast hx
        · exact_mod_cast hxy.le
    linarith [hopt]

lemma rsum_sublist_le : ∀ {l V : List ℕ}, l.Sorted (· < ·) → (∀ x ∈ l, 0 < x) →
    V.Sublist l → rsum V ≤ rsum (l.take V.length) := by
  intro l
  induction l with
  | nil =>
    intro V _ _ hV
    rw [List.sublist_nil.mp hV]
    simp [rsum]
  | cons x xs ih =>
    intro V hs hpos hV
    have hx : 0 < x := hpos x (List.mem_cons_self ..)
    cases hV with
    | cons _ hV' =>
      calc rsum V ≤ rsum (xs.take V.length) :=
              ih (List.sorted_cons.mp hs).2 (fun y hy => hpos y (List.mem_cons_of_mem _ hy)) hV'
        _ ≤ rsum ((x :: xs).take V.length) := rsum_take_shift hs hx _
    | cons₂ _ hV' =>
      rename_i V'
      show rsum (x :: V') ≤ rsum ((x :: xs).take (V'.length + 1))
      rw [rsum_cons, List.take_succ_cons, rsum_cons]
      have := ih (List.sorted_cons.mp hs).2
        (fun y hy => hpos y (List.mem_cons_of_mem _ hy)) hV'
      linarith

/-- Strictly sorted + subset ⇒ sublist. -/
lemma sublist_of_sorted_lt : ∀ {l₂ l₁ : List ℕ}, l₁.Sorted (· < ·) → l₂.Sorted (· < ·) →
    (∀ x ∈ l₁, x ∈ l₂) → l₁.Sublist l₂ := by
  intro l₂
  induction l₂ with
  | nil =>
    intro l₁ _ _ hsub
    cases l₁ with
    | nil => exact List.Sublist.refl _
    | cons a t => exact absurd (hsub a (List.mem_cons_self ..)) (List.not_mem_nil)
  | cons y t ih =>
    intro l₁ h₁ h₂ hsub
    cases l₁ with
    | nil => exact List.nil_sublist _
    | cons a s =>
      by_cases hay : a = y
      · subst hay
        refine List.Sublist.cons₂ _ (ih (List.sorted_cons.mp h₁).2 (List.sorted_cons.mp h₂).2 ?_)
        intro z hz
        have hz2 : z ∈ a :: t := hsub z (List.mem_cons_of_mem _ hz)
        rcases List.mem_cons.mp hz2 with hz3 | hz3
        · exact absurd (hz3 ▸ (List.sorted_cons.mp h₁).1 z hz) (lt_irrefl _)
        · exact hz3
      · -- a ≠ y, so a ∈ t and in fact all of a :: s embeds in t
        refine List.Sublist.cons _ (ih h₁ (List.sorted_cons.mp h₂).2 ?_)
        intro z hz
        have hz2 : z ∈ y :: t := hsub z hz
        rcases List.mem_cons.mp hz2 with hz3 | hz3
        · -- z = y is impossible: y would sit inside the strictly larger tail
          exfalso
          have ha : a ∈ y :: t := hsub a (List.mem_cons_self ..)
          rcases List.mem_cons.mp ha with ha2 | ha2
          · exact hay ha2
          · -- a ∈ t so y < a; but z = y ∈ a :: s means y = a or a < y
            have hya : y < a := (List.sorted_cons.mp h₂).1 a ha2
            rcases List.mem_cons.mp hz with hz4 | hz4
            · exact hay (hz4 ▸ hz3).symm ▸ (lt_irrefl y (hz3 ▸ hz4 ▸ hya)) |>.elim
            · have : a < z := (List.sorted_cons.mp h₁).1 z hz4
              exact absurd (hz3 ▸ this) (lt_asymm hya)
        · exact hz3

/-! ## The verified search -/

/-- Pruned DFS.  Returns `true` iff every completion `V` (a `need`-subset of `l`) with
`thr ≤ cur + rsum V` has `plusVal (forced39 ++ V ++ chosen)` a non-square. -/
def dfs : List ℕ → ℕ → ℚ → List ℕ → Bool
  | _, 0, cur, chosen => if thr ≤ cur then nsqB (plusVal (forced39 ++ chosen)) else true
  | [], _ + 1, _, _ => true
  | x :: xs, need + 1, cur, chosen =>
    if cur + rsum ((x :: xs).take (need + 1)) < thr then true
    else dfs xs need (cur + (x : ℚ)⁻¹) (x :: chosen) && dfs xs (need + 1) cur chosen

theorem dfs_sound : ∀ (l : List ℕ), l.Sorted (· < ·) → (∀ x ∈ l, 0 < x) →
    ∀ (need : ℕ) (cur : ℚ) (chosen : List ℕ), dfs l need cur chosen = true →
    ∀ V : List ℕ, V.Sublist l → V.length = need → thr ≤ cur + rsum V →
    nsqB (plusVal (forced39 ++ (V ++ chosen))) = true := by
  intro l
  induction l with
  | nil =>
    intro _ _ need cur chosen hdfs V hV hlen hthr
    have hVnil : V = [] := List.sublist_nil.mp hV
    subst hVnil
    simp only [List.length_nil] at hlen
    subst hlen
    rw [dfs] at hdfs
    rw [rsum_nil, add_zero] at hthr
    rw [if_pos hthr] at hdfs
    simpa using hdfs
  | cons x xs ih =>
    intro hs hpos need cur chosen hdfs V hV hlen hthr
    have hstail := (List.sorted_cons.mp hs).2
    have hptail : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    cases need with
    | zero =>
      have hVnil : V = [] := List.length_eq_zero_iff.mp hlen
      subst hVnil
      rw [dfs] at hdfs
      rw [rsum_nil, add_zero] at hthr
      rw [if_pos hthr] at hdfs
      simpa using hdfs
    | succ n =>
      rw [dfs] at hdfs
      by_cases hprune : cur + rsum ((x :: xs).take (n + 1)) < thr
      · -- pruned: no qualifying V can exist
        exfalso
        have hdom : rsum V ≤ rsum ((x :: xs).take (n + 1)) := by
          have := rsum_sublist_le hs hpos hV
          rwa [hlen] at this
        linarith
      · rw [if_neg hprune, Bool.and_eq_true] at hdfs
        obtain ⟨h1, h2⟩ := hdfs
        cases hV with
        | cons _ hV' =>
          exact ih hstail hptail (n + 1) cur chosen h2 V hV' hlen hthr
        | cons₂ _ hV' =>
          rename_i V'
          have hlen' : V'.length = n := by simpa using hlen
          have hthr' : thr ≤ (cur + (x : ℚ)⁻¹) + rsum V' := by
            rw [rsum_cons] at hthr; linarith
          have hres := ih hstail hptail n (cur + (x : ℚ)⁻¹) (x :: chosen) h1 V' hV' hlen' hthr'
          -- reorder: V' ++ (x :: chosen) ~ (x :: V') ++ chosen
          have hperm : (forced39 ++ (V' ++ (x :: chosen))).Perm
              (forced39 ++ ((x :: V') ++ chosen)) := by
            refine List.Perm.append_left _ ?_
            simpa using (List.perm_middle (a := x) (l₁ := V') (l₂ := chosen)).symm
          rwa [plusVal_perm hperm] at hres

/-! ## Finset ↔ list bridges -/

lemma list_prod_toList (U : Finset ℕ) : U.toList.prod = ∏ p ∈ U, p := by
  rw [Finset.prod_eq_multiset_prod]
  conv_rhs => rw [← Multiset.coe_toList U.val]
  simp [Multiset.map_coe, Finset.toList]

lemma list_sum_toList {M : Type*} [AddCommMonoid M] (U : Finset ℕ) (f : ℕ → M) :
    (U.toList.map f).sum = ∑ p ∈ U, f p := by
  rw [Finset.sum_eq_multiset_sum]
  conv_rhs => rw [← Multiset.coe_toList U.val]
  simp [Multiset.map_coe, Finset.toList]

lemma prod_sort (U : Finset ℕ) : (U.sort (· ≤ ·)).prod = dprod U := by
  rw [(Finset.sort_perm_toList U (· ≤ ·)).prod_eq, list_prod_toList]; rfl

lemma rsum_sort (U : Finset ℕ) : rsum (U.sort (· ≤ ·)) = ∑ r ∈ U, (r : ℚ)⁻¹ := by
  unfold rsum
  rw [((Finset.sort_perm_toList U (· ≤ ·)).map _).sum_eq, list_sum_toList]

lemma plusVal_sort (U : Finset ℕ) : plusVal (U.sort (· ≤ ·)) = csum U + 2 * dprod U := by
  unfold plusVal
  rw [prod_sort]
  congr 1
  rw [((Finset.sort_perm_toList U (· ≤ ·)).map _).sum_eq, list_sum_toList]
  rfl

/-! ## The Pythagorean plus-square -/

lemma csum_union_eq {P Q : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q)
    (hdisj : Disjoint P Q) :
    csum (P ∪ Q) = dprod Q * csum P + dprod P * csum Q := by
  unfold csum dprod
  rw [Finset.prod_union hdisj, Finset.sum_union hdisj, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hdvd : p ∣ ∏ x ∈ P, x := Finset.dvd_prod_of_mem _ hp
    rw [mul_comm (∏ x ∈ P, x) (∏ x ∈ Q, x), Nat.mul_div_assoc _ hdvd]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have hdvd : q ∣ ∏ x ∈ Q, x := Finset.dvd_prod_of_mem _ hq
    rw [Nat.mul_div_assoc _ hdvd]

lemma plus_square {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdisj : Disjoint P Q) (h1 : csum P = dprod Q) (h2 : csum Q = dprod P) :
    csum (P ∪ Q) + 2 * dprod (P ∪ Q) = (dprod P + dprod Q) ^ 2 := by
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  have hQpos : ∀ q ∈ Q, 0 < q := fun q hq => (hQ q hq).pos
  have hdu : dprod (P ∪ Q) = dprod P * dprod Q := by
    unfold dprod; exact Finset.prod_union hdisj
  rw [csum_union_eq hPpos hQpos hdisj, h1, h2, hdu]
  ring

/-! ## Numeric facts -/

/-- Any prime `p ≤ 167` lies in a 59-element prime support with `T ≥ 2`. -/
lemma forced_mem {U : Finset ℕ} (hU : ∀ r ∈ U, r.Prime) (hc : U.card = 59)
    (hT : (2 : ℚ) ≤ ∑ r ∈ U, (r : ℚ)⁻¹) {p : ℕ} (hp : p.Prime) (hple : p ≤ 167) :
    p ∈ U := by
  by_contra hpn
  have hWprime : ∀ r ∈ insert p U, r.Prime := by
    intro r hr
    rcases Finset.mem_insert.mp hr with h | h
    · exact h ▸ hp
    · exact hU r h
  have hWcard : (insert p U).card = 60 := by
    rw [Finset.card_insert_of_not_mem hpn, hc]
  have hbound := recipSum_le_first_primes hWprime
  rw [hWcard] at hbound
  have hsum60 : ∑ i ∈ Finset.range 60, ((Nat.nth Nat.Prime i : ℕ) : ℚ)⁻¹
      = (N59 : ℚ) / (P59 : ℚ) + (281 : ℚ)⁻¹ := by
    rw [Finset.sum_range_succ, sum_first59, np59]
    norm_num
  have hWsum : ∑ r ∈ insert p U, (r : ℚ)⁻¹ = (p : ℚ)⁻¹ + ∑ r ∈ U, (r : ℚ)⁻¹ :=
    Finset.sum_insert hpn
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpinv : (167 : ℚ)⁻¹ ≤ (p : ℚ)⁻¹ := by
    gcongr
    · norm_num
    · exact_mod_cast hple
  have hnum : (N59 : ℚ) / (P59 : ℚ) + (281 : ℚ)⁻¹ < (167 : ℚ)⁻¹ + 2 := by
    unfold N59 P59; norm_num
  rw [hWsum, hsum60] at hbound
  linarith

/-- Every element of such a support is `≤ 795`. -/
lemma elt_le_795 {U : Finset ℕ} (hU : ∀ r ∈ U, r.Prime) (hc : U.card = 59)
    (hT : (2 : ℚ) ≤ ∑ r ∈ U, (r : ℚ)⁻¹) {r : ℕ} (hr : r ∈ U) : r ≤ 795 := by
  by_contra hgt
  push_neg at hgt
  have herase : ∀ x ∈ U.erase r, x.Prime := fun x hx => hU x (Finset.mem_of_mem_erase hx)
  have hecard : (U.erase r).card = 58 := by
    rw [Finset.card_erase_of_mem hr, hc]
  have hbound := recipSum_le_first_primes herase
  rw [hecard] at hbound
  have hsplit : ∑ x ∈ U.erase r, (x : ℚ)⁻¹ + (r : ℚ)⁻¹ = ∑ x ∈ U, (x : ℚ)⁻¹ :=
    Finset.sum_erase_add U _ hr
  have hr0 : (0 : ℚ) < r := by exact_mod_cast (hU r hr).pos
  have hrinv : (r : ℚ)⁻¹ ≤ (796 : ℚ)⁻¹ := by
    gcongr
    · norm_num
    · exact_mod_cast hgt
  have h58 := sum_first58
  have hnum : (N58 : ℚ) / (P58 : ℚ) + (796 : ℚ)⁻¹ < 2 := by
    unfold N58 P58; norm_num
  rw [sum_first58] at hbound
  linarith

/-! ## The main theorem -/

/-- **Closing the 59-prime level.**  Any solution of #307 has `|P ∪ Q| ≥ 60`. -/
theorem erdos307_sixty {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) :
    60 ≤ (P ∪ Q).card := by
  have h59 := card_ge_59 hP hQ heq
  rcases Nat.lt_or_ge (P ∪ Q).card 60 with hc | hc
  swap
  · exact hc
  have hcard : (P ∪ Q).card = 59 := by omega
  exfalso
  -- solution facts
  have hUprime : ∀ r ∈ P ∪ Q, r.Prime := by
    intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · exact hP r h
    · exact hQ r h
  have heq' : (csum P : ℚ) / (dprod P : ℚ) * ((csum Q : ℚ) / (dprod Q : ℚ)) = 1 := by
    rw [← recipSum_eq P hP, ← recipSum_eq Q hQ]; exact heq
  obtain ⟨hNPDQ, hNQDP⟩ := solution_structure (rigidity_coprime P hP) (rigidity_coprime Q hQ)
    (by exact_mod_cast (dprod_pos hP).ne') (by exact_mod_cast (dprod_pos hQ).ne') heq'
  have hdisj : Disjoint P Q := solution_disjoint hP hQ hNQDP
  have hs0 : (∑ p ∈ P, (p : ℚ)⁻¹) ≠ 0 := by
    intro h; rw [h, zero_mul] at heq; norm_num at heq
  have hs_pos : 0 < ∑ p ∈ P, (p : ℚ)⁻¹ :=
    lt_of_le_of_ne (Finset.sum_nonneg fun p hp => by positivity) (Ne.symm hs0)
  have hT : (2 : ℚ) ≤ ∑ r ∈ P ∪ Q, (r : ℚ)⁻¹ := by
    rw [Finset.sum_union hdisj]; exact recip_sum_ge_two hs_pos heq
  set U := P ∪ Q with hU
  -- the plus value is a perfect square
  have hsq : IsSquare (csum U + 2 * dprod U) := by
    rw [plus_square hP hQ hdisj hNPDQ hNQDP]
    exact ⟨dprod P + dprod Q, (sq (dprod P + dprod Q)).symm ▸ by ring⟩
  -- decompose U into forced ∪ V
  have hforced : ∀ p ∈ forced39, p ∈ U := by
    have hall : ∀ p ∈ forced39, p.Prime ∧ p ≤ 167 := by native_decide
    intro p hp
    exact forced_mem hUprime hcard hT (hall p hp).1 (hall p hp).2
  set forcedF : Finset ℕ := forced39.toFinset with hFdef
  have hFsub : forcedF ⊆ U := by
    intro p hp
    exact hforced p (List.mem_toFinset.mp hp)
  have hFcard : forcedF.card = 39 := by native_decide
  set V : Finset ℕ := U \ forcedF with hVdef
  have hVcard : V.card = 20 := by
    rw [hVdef, Finset.card_sdiff hFsub, hcard, hFcard]
  have hVpool : ∀ r ∈ V, r ∈ pool99 := by
    have hmem : ∀ r < 796, r.Prime → 167 < r → r ∈ pool99 := by native_decide
    have hsmall : ∀ r < 168, r.Prime → r ∈ forced39 := by native_decide
    intro r hrV
    have hrU : r ∈ U := Finset.mem_sdiff.mp hrV |>.1
    have hrF : r ∉ forcedF := Finset.mem_sdiff.mp hrV |>.2
    have hrp : r.Prime := hUprime r hrU
    have hle : r ≤ 795 := elt_le_795 hUprime hcard hT hrU
    have hgt : 167 < r := by
      by_contra hle167
      push_neg at hle167
      exact hrF (List.mem_toFinset.mpr (hsmall r (by omega) hrp))
    exact hmem r (by omega) hrp hgt
  -- sorted list of V is a sublist of the pool
  set LV : List ℕ := V.sort (· ≤ ·) with hLV
  have hLVsorted : LV.Sorted (· < ·) := Finset.sort_sorted_lt V
  have hpoolsorted : pool99.Sorted (· < ·) := by native_decide
  have hLVsub : LV.Sublist pool99 := by
    refine sublist_of_sorted_lt hLVsorted hpoolsorted ?_
    intro x hx
    exact hVpool x ((Finset.mem_sort (· ≤ ·)).mp hx)
  have hLVlen : LV.length = 20 := by
    rw [hLV, Finset.length_sort, hVcard]
  -- mass of V exceeds the threshold
  have hUsplit : forcedF ∪ V = U := by
    rw [hVdef]; exact Finset.union_sdiff_of_subset hFsub
  have hFdisj : Disjoint forcedF V := Finset.disjoint_sdiff
  have hFsum : ∑ r ∈ forcedF, (r : ℚ)⁻¹ = rsum forced39 := by
    rw [hFdef]
    have hnd : forced39.Nodup := by native_decide
    rw [List.sum_toFinset _ hnd]
    rfl
  have hVsum : rsum LV = ∑ r ∈ V, (r : ℚ)⁻¹ := rsum_sort V
  have hthrV : thr ≤ 0 + rsum LV := by
    have : ∑ r ∈ forcedF, (r : ℚ)⁻¹ + ∑ r ∈ V, (r : ℚ)⁻¹ = ∑ r ∈ U, (r : ℚ)⁻¹ := by
      rw [← Finset.sum_union hFdisj, hUsplit]
    rw [hVsum]
    unfold thr
    rw [← hFsum]
    linarith
  -- run the verified search
  have hrun : dfs pool99 20 0 [] = true := by native_decide
  have hpoolpos : ∀ x ∈ pool99, 0 < x := by native_decide
  have hout := dfs_sound pool99 hpoolsorted hpoolpos 20 0 [] hrun LV hLVsub hLVlen hthrV
  -- bridge to the Finset value
  have hperm : (forced39 ++ (LV ++ [])).Perm (U.sort (· ≤ ·)) := by
    rw [List.append_nil]
    rw [← Multiset.coe_eq_coe]
    have h1 : (↑(forced39 ++ LV) : Multiset ℕ) = ↑forced39 + ↑LV := by
      simp [Multiset.coe_add]
    have h2 : (↑forced39 : Multiset ℕ) = forcedF.val := by
      rw [hFdef]
      have hnd : forced39.Nodup := by native_decide
      simp [List.toFinset, Multiset.toFinset, hnd.dedup]
    have h3 : (↑LV : Multiset ℕ) = V.val := by
      rw [hLV, ← Multiset.coe_eq_coe.mpr (Finset.sort_perm_toList V (· ≤ ·))]
      simp [Multiset.coe_toList]
    have h4 : (↑(U.sort (· ≤ ·)) : Multiset ℕ) = U.val := by
      rw [← Multiset.coe_eq_coe.mpr (Finset.sort_perm_toList U (· ≤ ·))]
      simp [Multiset.coe_toList]
    rw [h1, h2, h3, h4, ← hUsplit]
    rw [← Finset.disjUnion_eq_union _ _ hFdisj]
    simp [Finset.disjUnion]
  have hfinal : nsqB (csum U + 2 * dprod U) = true := by
    have := hout
    rwa [plusVal_perm hperm, plusVal_sort] at this
  rw [nsqB_false_of_isSquare hsq] at hfinal
  exact absurd hfinal (by simp)

end Erdos307
