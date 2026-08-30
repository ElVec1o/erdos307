import Mathlib
import Erdos307.Rigidity
import Erdos307.Barrier
import Erdos307.Capstone
import Erdos307.Extremal
import Erdos307.Numeral
import Erdos307.Closed
import Erdos307.NonSquare

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
  20-subset) checks that `csum U + 2·dprod U` is a non-square for each of the 49,961
  admissible supports.  Contradiction.

The search is run by the **kernel**. `dfs` compares rationals, which the kernel cannot reduce at
all -- `Nat.gcd` is well-founded recursion, not a GMP primitive -- so the execution was previously
delegated to `native_decide`. Scaling by `Mscale`, the product of the 138 primes in play, clears the
denominators exactly, and `dfsA` then takes the same branches as `dfs` over the integers; the leaf
test uses the residue certificate of `Erdos307.NonSquare` in place of `Nat.sqrt`, and the product
and cofactor sum are carried down the recursion instead of rebuilt at each leaf. `dfsA_run` is
`decide`, and `dfs_run` follows through `dfs_of_dfsA`. There is no `native_decide` and no
`ofReduceBool`: `erdos307_sixty`, like everything else here, carries only the three standard
axioms.

Paper: Proposition `prop:close59`, Theorem `thm:barrier` at level 60.
-/

set_option maxRecDepth 100000

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

/-- Reciprocal sum of a list.  (The `p : ℕ` ascription matters: without it Lean coerces
the *list* to `List ℚ`, which breaks every syntactic rewrite downstream.) -/
def rsum (l : List ℕ) : ℚ := (l.map fun p : ℕ => (p : ℚ)⁻¹).sum

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

lemma rsum_perm {l l' : List ℕ} (h : l.Perm l') : rsum l = rsum l' := by
  unfold rsum
  exact (h.map fun p : ℕ => (p : ℚ)⁻¹).sum_eq

lemma plusVal_perm {l l' : List ℕ} (h : l.Perm l') : plusVal l = plusVal l' := by
  unfold plusVal
  rw [h.prod_eq, (h.map fun p => l'.prod / p).sum_eq]

/-- Reciprocal-of-cast monotonicity, packaged once. -/
lemma inv_cast_le {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y) : (y : ℚ)⁻¹ ≤ (x : ℚ)⁻¹ := by
  gcongr

/-- Shifting `take` across a strictly smaller head can only increase the mass. -/
lemma rsum_take_shift {x : ℕ} {xs : List ℕ} (hlt : ∀ y ∈ xs, x < y)
    (hx : 0 < x) (k : ℕ) : rsum (xs.take k) ≤ rsum ((x :: xs).take k) := by
  cases k with
  | zero => simp [rsum]
  | succ j =>
    have h1 : (x :: xs).take (j + 1) = x :: xs.take j := rfl
    rw [h1, rsum_cons, List.take_add_one, rsum_append]
    have h2 : rsum (xs[j]?.toList) ≤ (x : ℚ)⁻¹ := by
      cases hg : xs[j]? with
      | none =>
        have : rsum ((none : Option ℕ).toList) = 0 := rfl
        rw [this]
        positivity
      | some y =>
        have hy : y ∈ xs := List.mem_of_getElem? hg
        have h3 : rsum ((some y).toList) = (y : ℚ)⁻¹ := by simp [rsum]
        rw [h3]
        exact inv_cast_le hx (hlt y hy).le
    linarith

/-- Domination: over a `<`-pairwise list of positives, any sublist's reciprocal sum
is at most that of the first `length` elements. -/
lemma rsum_sublist_le : ∀ {l V : List ℕ}, l.Pairwise (· < ·) → (∀ x ∈ l, 0 < x) →
    V.Sublist l → rsum V ≤ rsum (l.take V.length) := by
  intro l
  induction l with
  | nil =>
    intro V _ _ hV
    rw [List.sublist_nil.mp hV]
    simp [rsum]
  | cons x xs ih =>
    intro V hs hpos hV
    have hx : 0 < x := hpos x (by simp)
    obtain ⟨hxlt, hstail⟩ := List.pairwise_cons.mp hs
    have hptail : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    cases hV with
    | cons _ hV' =>
      calc rsum V ≤ rsum (xs.take V.length) := ih hstail hptail hV'
        _ ≤ rsum ((x :: xs).take V.length) := rsum_take_shift hxlt hx _
    | cons_cons _ hV' =>
      rename_i V'
      have h1 : rsum (x :: V') = (x : ℚ)⁻¹ + rsum V' := rsum_cons x V'
      have h2 : (x :: xs).take ((x :: V').length) = x :: xs.take V'.length := rfl
      rw [h1, h2, rsum_cons]
      have := ih hstail hptail hV'
      linarith

/-- Strictly increasing + subset ⇒ sublist. -/
lemma sublist_of_pairwise_lt : ∀ {l₂ l₁ : List ℕ}, l₁.Pairwise (· < ·) →
    l₂.Pairwise (· < ·) → (∀ x ∈ l₁, x ∈ l₂) → l₁.Sublist l₂ := by
  intro l₂
  induction l₂ with
  | nil =>
    intro l₁ _ _ hsub
    cases l₁ with
    | nil => exact List.Sublist.refl _
    | cons a t =>
      exfalso
      simpa using hsub a (by simp)
  | cons y t ih =>
    intro l₁ h₁ h₂ hsub
    obtain ⟨hyt, ht⟩ := List.pairwise_cons.mp h₂
    cases l₁ with
    | nil => exact List.nil_sublist _
    | cons a s =>
      obtain ⟨has, hs⟩ := List.pairwise_cons.mp h₁
      rcases List.mem_cons.mp (hsub a (by simp)) with hay | hat
      · -- head match: a = y
        subst hay
        refine List.Sublist.cons_cons _ (ih hs ht ?_)
        intro z hz
        rcases List.mem_cons.mp (hsub z (List.mem_cons_of_mem _ hz)) with hzy | hzt
        · -- z = a yet a < z
          exfalso
          have h4 : a < z := has z hz
          omega
        · exact hzt
      · -- a strictly inside t: everything embeds in t
        refine List.Sublist.cons _ (ih h₁ ht ?_)
        intro z hz
        rcases List.mem_cons.mp (hsub z hz) with hzy | hzt
        · -- z = y is impossible: y < a ≤ z
          exfalso
          have hya : y < a := hyt a hat
          rcases List.mem_cons.mp hz with hza | hzs
          · omega
          · have haz : a < z := has z hzs
            omega
        · exact hzt

/-! ## The verified search -/

/-- Pruned DFS.  Returns `true` iff every completion `V` (a `need`-subset of `l`) with
`thr ≤ cur + rsum V` has `plusVal (forced39 ++ V ++ chosen)` a non-square. -/
def dfs : List ℕ → ℕ → ℚ → List ℕ → Bool
  | _, 0, cur, chosen => if thr ≤ cur then nsqB (plusVal (forced39 ++ chosen)) else true
  | [], _ + 1, _, _ => true
  | x :: xs, need + 1, cur, chosen =>
    if cur + rsum ((x :: xs).take (need + 1)) < thr then true
    else dfs xs need (cur + (x : ℚ)⁻¹) (x :: chosen) && dfs xs (need + 1) cur chosen

theorem dfs_sound : ∀ (l : List ℕ), l.Pairwise (· < ·) → (∀ x ∈ l, 0 < x) →
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
    obtain ⟨hxlt, hstail⟩ := List.pairwise_cons.mp hs
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
      · exfalso
        have hdom : rsum V ≤ rsum ((x :: xs).take (n + 1)) := by
          have := rsum_sublist_le hs hpos hV
          rwa [hlen] at this
        linarith
      · rw [if_neg hprune, Bool.and_eq_true] at hdfs
        obtain ⟨h1, h2⟩ := hdfs
        cases hV with
        | cons _ hV' =>
          exact ih hstail hptail (n + 1) cur chosen h2 V hV' hlen hthr
        | cons_cons _ hV' =>
          rename_i V'
          have hlen' : V'.length = n := by simpa using hlen
          have hthr' : thr ≤ (cur + (x : ℚ)⁻¹) + rsum V' := by
            rw [rsum_cons] at hthr; linarith
          have hres := ih hstail hptail n (cur + (x : ℚ)⁻¹) (x :: chosen) h1 V' hV' hlen' hthr'
          have hperm : (forced39 ++ (V' ++ (x :: chosen))).Perm
              (forced39 ++ ((x :: V') ++ chosen)) := by
            refine List.Perm.append_left _ ?_
            simpa using (List.perm_middle (a := x) (l₁ := V') (l₂ := chosen)).symm
          rwa [plusVal_perm hperm] at hres

/-! ## Finset ↔ list bridges -/

lemma list_prod_toList (U : Finset ℕ) : U.toList.prod = ∏ p ∈ U, p := by
  rw [Finset.prod_eq_multiset_prod]
  conv_rhs => rw [← Multiset.coe_toList U.val]
  simp [Finset.toList]

lemma list_sum_toList {M : Type*} [AddCommMonoid M] (U : Finset ℕ) (f : ℕ → M) :
    (U.toList.map f).sum = ∑ p ∈ U, f p := by
  rw [Finset.sum_eq_multiset_sum]
  conv_rhs => rw [← Multiset.coe_toList U.val]
  simp [Finset.toList]

lemma prod_sort (U : Finset ℕ) : (U.sort (· ≤ ·)).prod = dprod U := by
  rw [(Finset.sort_perm_toList U (· ≤ ·)).prod_eq, list_prod_toList]; rfl

lemma rsum_sort (U : Finset ℕ) : rsum (U.sort (· ≤ ·)) = ∑ r ∈ U, (r : ℚ)⁻¹ := by
  unfold rsum
  have h := (Finset.sort_perm_toList U (· ≤ ·)).map (fun p : ℕ => (p : ℚ)⁻¹)
  rw [h.sum_eq]
  exact list_sum_toList U _

lemma plusVal_sort (U : Finset ℕ) : plusVal (U.sort (· ≤ ·)) = csum U + 2 * dprod U := by
  unfold plusVal
  rw [prod_sort]
  congr 1
  have h := (Finset.sort_perm_toList U (· ≤ ·)).map (fun p : ℕ => dprod U / p)
  rw [h.sum_eq]
  rw [list_sum_toList U (fun p => dprod U / p)]
  rfl

/-! ## The Pythagorean plus-square -/

lemma csum_union_eq {P Q : Finset ℕ} (hdisj : Disjoint P Q) :
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

lemma plus_square {P Q : Finset ℕ} (hdisj : Disjoint P Q)
    (h1 : csum P = dprod Q) (h2 : csum Q = dprod P) :
    csum (P ∪ Q) + 2 * dprod (P ∪ Q) = (dprod P + dprod Q) ^ 2 := by
  have hdu : dprod (P ∪ Q) = dprod P * dprod Q := by
    unfold dprod; exact Finset.prod_union hdisj
  rw [csum_union_eq hdisj, h1, h2, hdu]
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
    rw [Finset.card_insert_of_notMem hpn, hc]
  have hbound := recipSum_le_first_primes hWprime
  rw [hWcard] at hbound
  have hsum60 : ∑ i ∈ Finset.range 60, ((Nat.nth Nat.Prime i : ℕ) : ℚ)⁻¹
      = (N59 : ℚ) / (P59 : ℚ) + (281 : ℚ)⁻¹ := by
    rw [Finset.sum_range_succ, sum_first59, np59]
    norm_num
  have hWsum : ∑ r ∈ insert p U, (r : ℚ)⁻¹ = (p : ℚ)⁻¹ + ∑ r ∈ U, (r : ℚ)⁻¹ :=
    Finset.sum_insert hpn
  have hpinv : (167 : ℚ)⁻¹ ≤ (p : ℚ)⁻¹ := inv_cast_le hp.pos hple
  have hnum : (N59 : ℚ) / (P59 : ℚ) + (281 : ℚ)⁻¹ < (167 : ℚ)⁻¹ + 2 := by
    unfold N59 P59; norm_num
  rw [hWsum, hsum60] at hbound
  linarith

/-- Every element of such a support is `≤ 795`. -/
lemma elt_le_795 {U : Finset ℕ} (hU : ∀ r ∈ U, r.Prime) (hc : U.card = 59)
    (hT : (2 : ℚ) ≤ ∑ r ∈ U, (r : ℚ)⁻¹) {r : ℕ} (hr : r ∈ U) : r ≤ 795 := by
  by_contra hgt
  have hgt' : 796 ≤ r := by omega
  have herase : ∀ x ∈ U.erase r, x.Prime := fun x hx => hU x (Finset.mem_of_mem_erase hx)
  have hecard : (U.erase r).card = 58 := by
    rw [Finset.card_erase_of_mem hr, hc]
  have hbound := recipSum_le_first_primes herase
  rw [hecard] at hbound
  have hsplit : ∑ x ∈ U.erase r, (x : ℚ)⁻¹ + (r : ℚ)⁻¹ = ∑ x ∈ U, (x : ℚ)⁻¹ :=
    Finset.sum_erase_add U _ hr
  have hrinv : (r : ℚ)⁻¹ ≤ (796 : ℚ)⁻¹ := inv_cast_le (by norm_num) hgt'
  have hnum : (N58 : ℚ) / (P58 : ℚ) + (796 : ℚ)⁻¹ < 2 := by
    unfold N58 P58; norm_num
  rw [sum_first58] at hbound
  linarith

/-! ## Decidable facts, hoisted so each gets its own heartbeat/codegen budget -/

lemma forced39_facts : ∀ p ∈ forced39, p.Prime ∧ p ≤ 167 := by decide

set_option maxHeartbeats 2000000 in
lemma pool99_complete : ∀ r < 796, r.Prime → 167 < r → r ∈ pool99 := by decide

lemma forced39_complete : ∀ r < 168, r.Prime → r ∈ forced39 := by decide

lemma forced39_card : forced39.toFinset.card = 39 := by decide

lemma forced39_nodup : forced39.Nodup := by decide

lemma forced39_sum : ∑ r ∈ forced39.toFinset, (r : ℚ)⁻¹ = rsum forced39 := by
  rw [rsum]
  exact List.sum_toFinset _ forced39_nodup

lemma forced39_coe : (↑forced39 : Multiset ℕ) = forced39.toFinset.val := by decide

lemma pool99_pairwise : pool99.Pairwise (· < ·) := by decide

lemma pool99_pos : ∀ x ∈ pool99, 0 < x := by decide


/-! ## The search, run by the kernel

`dfs` compares rationals, and the kernel cannot reduce `Rat` comparisons: `Nat.gcd` is well-founded
recursion, not a GMP primitive, so `decide` on `dfs` does not evaluate at all. That is why the search
was previously delegated to `native_decide`, at the cost of the `Lean.ofReduceBool` axiom.

Scaling by `Mscale`, the product of all `138` primes in play, removes the rationals without
approximation: every `1/p` becomes the integer `Mscale / p`, and `thr` becomes the integer `thrM`, so
the scaled search `dfsA` takes *exactly* the same branches as `dfs`. Two further changes make the
kernel run it in well under a minute: the leaf test uses the modular certificate of
`Erdos307.NonSquare` in place of `Nat.sqrt`, and the product and cofactor-sum are carried down the
recursion rather than recomputed from `chosen` at each of the `49,961` leaves.
-/

/-- The product of `forced39 ++ pool99`: the common denominator of every reciprocal in play. -/
def Mscale : ℕ := 587711349675320102989400444802724115225082390560315736634930041277275195793926797047357491327110462658195324486047607003645301092965092456412595768353430843365413065818682917883304285583082671336687009563216918389800112386407484406460630913698814543629186115898642231481641279546576957597435648091657212688633258316137955056230

/-- `Mscale * thr`, an integer. -/
def thrM : ℕ := 51939544712372837647132640693577364405383408682167116022881026223508385622321458625953051757761670930410762435263904996223412245192936938377507142658269568299072467675482885770362996356391496756103183827391682873428828074408124338251716757174763359832316200290202236585011125358070640802967809934728716326824038096278558994409

/-- The scaled reciprocal `Mscale / p`, exact for every `p` in play. -/
def wt (x : ℕ) : ℕ := Mscale / x

def wsum (l : List ℕ) : ℕ := (l.map wt).sum

/-- `∏ forced39`. -/
def P0 : ℕ := 962947420735983927056946215901134429196419130606213075415963491270

/-- `∑_{p ∈ forced39} (∏ forced39)/p`. -/
def D0 : ℕ := 1840793455149223796977553240989608507934961889604586193282330007699

/-- The cofactor sum, so that `plusVal l = dval l + 2 * l.prod` definitionally. -/
def dval (l : List ℕ) : ℕ := (l.map fun p => l.prod / p).sum

lemma plusVal_eq (l : List ℕ) : plusVal l = dval l + 2 * l.prod := rfl

/-- The scaled search. `pr` and `ds` carry `∏` and `dval` of `forced39 ++ chosen`. -/
def dfsA : List ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | _, 0, cur, pr, ds => if thrM ≤ cur then nsqCert (ds + 2 * pr) else true
  | [], _ + 1, _, _, _ => true
  | x :: xs, need + 1, cur, pr, ds =>
    if cur + wsum ((x :: xs).take (need + 1)) < thrM then true
    else dfsA xs need (cur + wt x) (x * pr) (pr + x * ds)
      && dfsA xs (need + 1) cur pr ds

set_option maxHeartbeats 0 in
/-- The whole search, checked by the kernel. Roughly a minute. -/
theorem dfsA_run : dfsA pool99 20 0 P0 D0 = true := by decide


/-! ### The bridge: the scaled search implies the rational one -/

lemma Mscale_pos : 0 < Mscale := by decide

lemma pool99_dvd : ∀ x ∈ pool99, x ∣ Mscale := by decide

lemma forced39_dvd : ∀ x ∈ forced39, x ∣ Mscale := by decide

lemma wt_cast {x : ℕ} (hx : 0 < x) (hd : x ∣ Mscale) : (wt x : ℚ) = (Mscale : ℚ) / x := by
  rw [wt, Nat.cast_div hd (by exact_mod_cast hx.ne')]

lemma wsum_cast : ∀ {l : List ℕ}, (∀ p ∈ l, 0 < p) → (∀ p ∈ l, p ∣ Mscale) →
    (wsum l : ℚ) = (Mscale : ℚ) * rsum l := by
  intro l
  induction l with
  | nil => intro _ _; simp [wsum, rsum]
  | cons a t ih =>
    intro hpos hdvd
    have ha : 0 < a := hpos a (List.mem_cons_self)
    have had : a ∣ Mscale := hdvd a (List.mem_cons_self)
    have ht1 : ∀ p ∈ t, 0 < p := fun p hp => hpos p (List.mem_cons_of_mem _ hp)
    have ht2 : ∀ p ∈ t, p ∣ Mscale := fun p hp => hdvd p (List.mem_cons_of_mem _ hp)
    have hrec : (wsum t : ℚ) = (Mscale : ℚ) * rsum t := ih ht1 ht2
    have hexp : wsum (a :: t) = wt a + wsum t := by simp [wsum]
    have hane : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    rw [hexp, Nat.cast_add, wt_cast ha had, hrec, rsum_cons, div_eq_mul_inv]
    ring

lemma thrM_add : thrM + wsum forced39 = 2 * Mscale := by decide

lemma thrM_cast : (thrM : ℚ) = (Mscale : ℚ) * thr := by
  have h := thrM_add
  have hf1 : ∀ p ∈ forced39, 0 < p := by decide
  have := wsum_cast hf1 forced39_dvd
  have hc : (thrM : ℚ) + (wsum forced39 : ℚ) = 2 * (Mscale : ℚ) := by exact_mod_cast h
  rw [this] at hc
  rw [thr, mul_sub]
  linear_combination hc

lemma nsqCert_to_nsqB {n : ℕ} (h : nsqCert n = true) : nsqB n = true := by
  have := not_isSquare_of_nsqCert h
  simp only [nsqB, decide_eq_true_eq, ne_eq]
  intro hsq
  exact this ⟨Nat.sqrt n, hsq.symm⟩

lemma dval_perm {l l' : List ℕ} (h : l.Perm l') : dval l = dval l' := by
  simp only [dval]
  rw [h.prod_eq]
  exact (h.map _).sum_eq

lemma dval_cons {x : ℕ} {l : List ℕ} (hx : 0 < x) :
    dval (x :: l) = l.prod + x * dval l := by
  simp only [dval, List.map_cons, List.sum_cons, List.prod_cons]
  have h1 : x * l.prod / x = l.prod := Nat.mul_div_cancel_left _ hx
  rw [h1]
  congr 1
  have h2 : ∀ p ∈ l, x * l.prod / p = x * (l.prod / p) := fun p hp =>
    Nat.mul_div_assoc x (List.dvd_prod hp)
  rw [List.map_congr_left h2]
  exact List.sum_map_mul_left l (fun p => l.prod / p) x

set_option maxHeartbeats 1000000 in
theorem dfs_of_dfsA : ∀ (l : List ℕ), (∀ x ∈ l, 0 < x) → (∀ x ∈ l, x ∣ Mscale) →
    ∀ (need : ℕ) (curN : ℕ) (curQ : ℚ) (pr ds : ℕ) (chosen : List ℕ),
    (curN : ℚ) = (Mscale : ℚ) * curQ →
    pr = (forced39 ++ chosen).prod →
    ds = dval (forced39 ++ chosen) →
    dfsA l need curN pr ds = true → dfs l need curQ chosen = true := by
  intro l
  induction l with
  | nil =>
    intro _ _ need curN curQ pr ds chosen hcur hpr hds hA
    cases need with
    | zero =>
      rw [dfs]
      by_cases h : thr ≤ curQ
      · rw [if_pos h]
        rw [dfsA] at hA
        have hM : (thrM : ℚ) ≤ (curN : ℚ) := by
          rw [thrM_cast, hcur]
          have hM0 : (0 : ℚ) < Mscale := by exact_mod_cast Mscale_pos
          exact mul_le_mul_of_nonneg_left h (le_of_lt hM0)
        have hMn : thrM ≤ curN := by exact_mod_cast hM
        rw [if_pos hMn] at hA
        have hval : ds + 2 * pr = plusVal (forced39 ++ chosen) := by
          rw [plusVal_eq, hpr, hds]
        rw [hval] at hA
        exact nsqCert_to_nsqB hA
      · rw [if_neg h]
    | succ n => rw [dfs]
  | cons x xs ih =>
    intro hpos hdvd need curN curQ pr ds chosen hcur hpr hds hA
    have hx : 0 < x := hpos x (List.mem_cons_self)
    have hxd : x ∣ Mscale := hdvd x (List.mem_cons_self)
    have ht1 : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    have ht2 : ∀ y ∈ xs, y ∣ Mscale := fun y hy => hdvd y (List.mem_cons_of_mem _ hy)
    have hMQ : (0 : ℚ) < Mscale := by exact_mod_cast Mscale_pos
    cases need with
    | zero =>
      rw [dfs]
      by_cases h : thr ≤ curQ
      · rw [if_pos h]
        rw [dfsA] at hA
        have hM : (thrM : ℚ) ≤ (curN : ℚ) := by
          rw [thrM_cast, hcur]
          exact mul_le_mul_of_nonneg_left h (le_of_lt hMQ)
        have hMn : thrM ≤ curN := by exact_mod_cast hM
        rw [if_pos hMn] at hA
        have hval : ds + 2 * pr = plusVal (forced39 ++ chosen) := by
          rw [plusVal_eq, hpr, hds]
        rw [hval] at hA
        exact nsqCert_to_nsqB hA
      · rw [if_neg h]
    | succ n =>
      rw [dfs]
      by_cases hprune : curQ + rsum ((x :: xs).take (n + 1)) < thr
      · rw [if_pos hprune]
      · rw [if_neg hprune]
        push_neg at hprune
        -- the scaled search did not prune either
        have htake1 : ∀ p ∈ (x :: xs).take (n + 1), 0 < p := fun p hp =>
          hpos p (List.mem_of_mem_take hp)
        have htake2 : ∀ p ∈ (x :: xs).take (n + 1), p ∣ Mscale := fun p hp =>
          hdvd p (List.mem_of_mem_take hp)
        have hws := wsum_cast htake1 htake2
        have hnoprune : ¬ (curN + wsum ((x :: xs).take (n + 1)) < thrM) := by
          intro hc
          have : (curN : ℚ) + (wsum ((x :: xs).take (n + 1)) : ℚ) < (thrM : ℚ) := by
            exact_mod_cast hc
          rw [hcur, hws, thrM_cast] at this
          have hfac : (Mscale : ℚ) * (curQ + rsum ((x :: xs).take (n + 1)))
              < (Mscale : ℚ) * thr := by rw [mul_add]; exact this
          exact absurd hprune (not_le.mpr (lt_of_mul_lt_mul_left hfac (le_of_lt hMQ)))
        rw [dfsA, if_neg hnoprune, Bool.and_eq_true] at hA
        obtain ⟨hA1, hA2⟩ := hA
        rw [Bool.and_eq_true]
        constructor
        · refine ih ht1 ht2 n (curN + wt x) (curQ + (x : ℚ)⁻¹) (x * pr) (pr + x * ds) (x :: chosen)
            ?_ ?_ ?_ hA1
          · rw [Nat.cast_add, hcur, wt_cast hx hxd, div_eq_mul_inv]
            ring
          · rw [hpr, (List.perm_middle (a := x) (l₁ := forced39) (l₂ := chosen)).prod_eq,
              List.prod_cons]
          · rw [hds, hpr, dval_perm (List.perm_middle (a := x) (l₁ := forced39) (l₂ := chosen)),
              dval_cons hx]
        · exact ih ht1 ht2 (n + 1) curN curQ pr ds chosen hcur hpr hds hA2

lemma dfs_run : dfs pool99 20 0 [] = true := by
  refine dfs_of_dfsA pool99 pool99_pos pool99_dvd 20 0 0 P0 D0 [] (by norm_num) ?_ ?_ dfsA_run
  · show P0 = (forced39 ++ []).prod
    decide
  · show D0 = dval (forced39 ++ [])
    decide

/-! ## The main theorem -/

set_option maxHeartbeats 1000000 in
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
  -- the plus value is a perfect square
  have hsq : IsSquare (csum (P ∪ Q) + 2 * dprod (P ∪ Q)) := by
    rw [plus_square hdisj hNPDQ hNQDP]
    exact ⟨dprod P + dprod Q, by ring⟩
  -- forced primes
  have hforced : ∀ p ∈ forced39, p ∈ P ∪ Q := by
    intro p hp
    exact forced_mem hUprime hcard hT (forced39_facts p hp).1 (forced39_facts p hp).2
  have hFsub : forced39.toFinset ⊆ P ∪ Q := by
    intro p hp
    exact hforced p (List.mem_toFinset.mp hp)
  -- the 20 free slots land in the pool
  have hVcard : ((P ∪ Q) \ forced39.toFinset).card = 20 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFsub, hcard, forced39_card]
  have hVpool : ∀ r ∈ (P ∪ Q) \ forced39.toFinset, r ∈ pool99 := by
    intro r hrV
    have hrU : r ∈ P ∪ Q := (Finset.mem_sdiff.mp hrV).1
    have hrF : r ∉ forced39.toFinset := (Finset.mem_sdiff.mp hrV).2
    have hrp : r.Prime := hUprime r hrU
    have hle : r ≤ 795 := elt_le_795 hUprime hcard hT hrU
    have hgt : 167 < r := by
      by_contra hle167
      have h167 : r ≤ 167 := by omega
      exact hrF (List.mem_toFinset.mpr (forced39_complete r (by omega) hrp))
    exact pool99_complete r (by omega) hrp hgt
  -- sorted list of the free slots is a sublist of the pool
  have hLVsorted : (((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort _).pairwise
  have hLVsub : (((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·)).Sublist pool99 := by
    refine sublist_of_pairwise_lt hLVsorted pool99_pairwise ?_
    intro x hx
    exact hVpool x ((Finset.mem_sort (· ≤ ·)).mp hx)
  have hLVlen : (((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·)).length = 20 := by
    rw [Finset.length_sort, hVcard]
  -- the free-slot mass exceeds the threshold
  have hUsplit : forced39.toFinset ∪ ((P ∪ Q) \ forced39.toFinset) = P ∪ Q :=
    Finset.union_sdiff_of_subset hFsub
  have hFdisj : Disjoint forced39.toFinset ((P ∪ Q) \ forced39.toFinset) :=
    Finset.disjoint_sdiff
  have hVsum : rsum (((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·))
      = ∑ r ∈ (P ∪ Q) \ forced39.toFinset, (r : ℚ)⁻¹ := rsum_sort _
  have hthrV : thr ≤ 0 + rsum (((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·)) := by
    have hsplitsum : ∑ r ∈ forced39.toFinset, (r : ℚ)⁻¹
        + ∑ r ∈ (P ∪ Q) \ forced39.toFinset, (r : ℚ)⁻¹ = ∑ r ∈ P ∪ Q, (r : ℚ)⁻¹ := by
      rw [← Finset.sum_union hFdisj, hUsplit]
    rw [hVsum]
    unfold thr
    rw [← forced39_sum]
    linarith
  -- run the verified search
  have hout := dfs_sound pool99 pool99_pairwise pool99_pos 20 0 [] dfs_run
    (((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·)) hLVsub hLVlen hthrV
  -- bridge back to the Finset value
  have hperm : (forced39 ++ ((((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·)) ++ [])).Perm
      ((P ∪ Q).sort (· ≤ ·)) := by
    rw [List.append_nil]
    rw [← Multiset.coe_eq_coe]
    have h2 : (↑forced39 : Multiset ℕ) = forced39.toFinset.val := forced39_coe
    have h3 : (↑(((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·)) : Multiset ℕ)
        = ((P ∪ Q) \ forced39.toFinset).val :=
      Multiset.coe_eq_coe.mpr (Finset.sort_perm_toList _ _) |>.trans
        (Multiset.coe_toList _)
    have h4 : (↑((P ∪ Q).sort (· ≤ ·)) : Multiset ℕ) = (P ∪ Q).val :=
      Multiset.coe_eq_coe.mpr (Finset.sort_perm_toList _ _) |>.trans
        (Multiset.coe_toList _)
    have hval : forced39.toFinset.val + ((P ∪ Q) \ forced39.toFinset).val = (P ∪ Q).val := by
      conv_rhs => rw [← hUsplit, ← Finset.disjUnion_eq_union _ _ hFdisj]
      rw [Finset.disjUnion_val]
    calc (↑(forced39 ++ (((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·))) : Multiset ℕ)
        = ↑forced39 + ↑(((P ∪ Q) \ forced39.toFinset).sort (· ≤ ·)) := by
          first
          | rfl
          | simp
      _ = forced39.toFinset.val + ((P ∪ Q) \ forced39.toFinset).val := by rw [h2, h3]
      _ = (P ∪ Q).val := hval
      _ = ↑((P ∪ Q).sort (· ≤ ·)) := h4.symm
  have hfinal : nsqB (csum (P ∪ Q) + 2 * dprod (P ∪ Q)) = true := by
    have h5 := hout
    rw [plusVal_perm hperm, plusVal_sort] at h5
    exact h5
  rw [nsqB_false_of_isSquare hsq] at hfinal
  exact absurd hfinal (by simp)

end Erdos307
