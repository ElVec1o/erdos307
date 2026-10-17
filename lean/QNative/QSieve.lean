import Mathlib.Tactic

/-!
# The q-sieve, Nat-level core (Track B, M5)

Generic, proved building blocks for the sieve over the tail prime `q`:

* `good D p x`: `x ≢ 0` and the Euler symbol of `x` modulo `p` equals that of `(D/p) mod p`;
* `allPass`: `q` passes the table of every prime in a list;
* `scanQ`: the arithmetic progression `q, q + W, …` is scanned, each survivor of the tables is tested by the two
  exact squares;
* `wheelOf`: the residues modulo `W = 8 ∏ p` passing the first tables, built by lifting prime by prime, with
  `wheel_complete`.

Paper: Proposition `prop:level60closed` (the sieve for `ρ > 2^-40`).
-/

namespace Erdos307

/-- Same definition as `Erdos307.eulerSym` (in `Computational/Euler.lean`); duplicated so that this precompiled module
has no project imports. `QS.eulerN_eq` identifies them. -/
def eulerN (ℓ x : Nat) : Int :=
  let r := x ^ (ℓ / 2) % ℓ
  if r = 0 then 0 else if r = 1 then 1 else -1

namespace QS

/-- The character condition on a residue. -/
def good (D p x : Nat) : Prop := x ≠ 0 ∧ eulerN p x = eulerN p ((D / p) % p)

instance (D p x : Nat) : Decidable (good D p x) := by unfold good; infer_instance

/-- The table of `good D p`: entry `x < p` is `1` iff `good D p x`. -/
def qTab (D p : Nat) : ByteArray :=
  ByteArray.mk ((Array.range p).map fun x => if good D p x then (1 : UInt8) else 0)

theorem qTab_get {D p x : Nat} (hx : x < p) :
    (qTab D p).get! x = if good D p x then (1 : UInt8) else 0 := by
  unfold qTab ByteArray.get!
  simp [hx]

theorem qTab_ne {D p q : Nat} (hp : 0 < p) :
    (qTab D p).get! (q % p) ≠ 0 ↔ good D p (q % p) := by
  rw [qTab_get (Nat.mod_lt _ hp)]
  by_cases h : good D p (q % p) <;> simp [h]

/-- `q` passes every table in the list. -/
def allPass (q : Nat) : List (Nat × ByteArray) → Bool
  | [] => true
  | e :: r => (e.2.get! (q % e.1) != 0) && allPass q r

theorem allPass_of_forall {q : Nat} {l : List (Nat × ByteArray)}
    (h : ∀ e ∈ l, e.2.get! (q % e.1) ≠ 0) : allPass q l = true := by
  induction l with
  | nil => rfl
  | cons e r ih =>
    simp only [allPass, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨h e (List.mem_cons_self), ih fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

def isSq (n : Nat) : Bool := Nat.sqrt n * Nat.sqrt n == n

theorem isSq_of_mul_self {n m : Nat} (h : n = m * m) : isSq n = true := by
  subst h; simp [isSq, Nat.sqrt_eq]

/-- Scan `q, q + W, …, q + W (k-1)`: at every survivor of the tables, the two exact squares must not both hold. -/
def scanQ (rest : List (Nat × ByteArray)) (A B D W : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | q, k + 1 =>
    (if allPass q rest then !(isSq (A * q + D) && isSq (B * q + D)) else true) &&
      scanQ rest A B D W (q + W) k

theorem scanQ_sound (rest : List (Nat × ByteArray)) (A B D W : Nat) :
    ∀ (k q : Nat), scanQ rest A B D W q k = true → ∀ j < k, allPass (q + W * j) rest = true →
      (isSq (A * (q + W * j) + D) && isSq (B * (q + W * j) + D)) = false := by
  intro k
  induction k with
  | zero => intro q _ j hj; omega
  | succ k ih =>
    intro q h j hj hp
    unfold scanQ at h
    rw [Bool.and_eq_true] at h
    cases j with
    | zero =>
      have := h.1
      simp only [Nat.mul_zero, Nat.add_zero] at hp ⊢
      rw [if_pos hp] at this
      rcases (by simpa using this : isSq (A * q + D) = false ∨ isSq (B * q + D) = false) with h | h <;> simp [h]
    | succ j =>
      have := ih (q + W) h.2 j (by omega) (by
        have e : q + W + W * j = q + W * (j + 1) := by ring
        rwa [e])
      have e : q + W + W * j = q + W * (j + 1) := by ring
      rwa [e] at this

/-! ### The wheel: residues modulo `W = 8 ∏ p` passing the first tables -/

/-- Lift the residues `R` modulo `W` to residues modulo `W p` passing the table of `p`. -/
def lift (W p : Nat) (tab : ByteArray) (R : List Nat) : List Nat :=
  R.flatMap fun r => (List.range p).filterMap fun t =>
    if tab.get! ((r + W * t) % p) != 0 then some (r + W * t) else none

theorem mem_lift {W p : Nat} {tab : ByteArray} {R : List Nat} {x : Nat} :
    x ∈ lift W p tab R ↔ ∃ r ∈ R, ∃ t < p, x = r + W * t ∧ tab.get! (x % p) ≠ 0 := by
  unfold lift
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨r, hr, t, ht, h⟩
    by_cases hc : tab.get! ((r + W * t) % p) != 0
    · rw [if_pos hc] at h
      have hx : r + W * t = x := Option.some.inj h
      subst hx
      exact ⟨r, hr, t, ht, rfl, by simpa using hc⟩
    · rw [if_neg hc] at h; simp at h
  · rintro ⟨r, hr, t, ht, hx, hp⟩
    subst hx
    refine ⟨r, hr, t, ht, ?_⟩
    rw [if_pos (by simpa using hp)]

def wheelOf (q0 : Nat) (tabs : List (Nat × ByteArray)) : Nat × List Nat :=
  tabs.foldl (fun (st : Nat × List Nat) e => (st.1 * e.1, lift st.1 e.1 e.2 st.2)) (8, [q0])

theorem wheel_fold (q0 : Nat) : ∀ (tabs done : List (Nat × ByteArray)) (W : Nat) (R : List Nat),
    0 < W → 8 ∣ W → (∀ e ∈ done, e.1 ∣ W) → (∀ e ∈ tabs, 0 < e.1) →
    (∀ x < W, x % 8 = q0 → (∀ e ∈ done, e.2.get! (x % e.1) ≠ 0) → x ∈ R) →
    let st := tabs.foldl (fun (st : Nat × List Nat) e => (st.1 * e.1, lift st.1 e.1 e.2 st.2)) (W, R)
    0 < st.1 ∧ 8 ∣ st.1 ∧
      (∀ x < st.1, x % 8 = q0 → (∀ e ∈ done ++ tabs, e.2.get! (x % e.1) ≠ 0) → x ∈ st.2) ∧
      (∀ e ∈ done ++ tabs, e.1 ∣ st.1) := by
  intro tabs
  induction tabs with
  | nil =>
    intro done W R hW h8 hdiv _ hC
    simp only [List.foldl_nil, List.append_nil]
    exact ⟨hW, h8, hC, hdiv⟩
  | cons e t ih =>
    intro done W R hW h8 hdiv hpos hC
    have hep : 0 < e.1 := hpos e List.mem_cons_self
    have hW1 : 0 < W * e.1 := Nat.mul_pos hW hep
    have h81 : 8 ∣ W * e.1 := Dvd.dvd.mul_right h8 _
    have hdiv1 : ∀ e' ∈ done ++ [e], e'.1 ∣ W * e.1 := by
      intro e' he'
      rcases List.mem_append.1 he' with h | h
      · exact Dvd.dvd.mul_right (hdiv e' h) _
      · rw [List.mem_singleton.1 h]; exact Dvd.intro_left _ rfl
    have hC1 : ∀ x < W * e.1, x % 8 = q0 → (∀ e' ∈ done ++ [e], e'.2.get! (x % e'.1) ≠ 0) →
        x ∈ lift W e.1 e.2 R := by
      intro x hx h8x hpass
      have hr : x % W < W := Nat.mod_lt _ hW
      have hr8 : x % W % 8 = q0 := by rw [Nat.mod_mod_of_dvd _ h8]; exact h8x
      have hrpass : ∀ e' ∈ done, e'.2.get! (x % W % e'.1) ≠ 0 := by
        intro e' he'
        rw [Nat.mod_mod_of_dvd _ (hdiv e' he')]
        exact hpass e' (List.mem_append_left _ he')
      have hxr := hC (x % W) hr hr8 hrpass
      have ht : x / W < e.1 := by
        rw [Nat.div_lt_iff_lt_mul hW]; rw [mul_comm]; exact hx
      refine mem_lift.2 ⟨x % W, hxr, x / W, ht, ?_, hpass e (List.mem_append_right _ (by simp))⟩
      have := Nat.mod_add_div x W
      omega
    have := ih (done ++ [e]) (W * e.1) (lift W e.1 e.2 R) hW1 h81 hdiv1
      (fun e' he' => hpos e' (List.mem_cons_of_mem _ he')) hC1
    simp only [List.foldl_cons]
    simpa [List.append_assoc] using this

theorem wheel_complete {q0 : Nat} (hq0 : q0 < 8) (tabs : List (Nat × ByteArray))
    (hpos : ∀ e ∈ tabs, 0 < e.1) :
    0 < (wheelOf q0 tabs).1 ∧ 8 ∣ (wheelOf q0 tabs).1 ∧
      (∀ e ∈ tabs, e.1 ∣ (wheelOf q0 tabs).1) ∧
      ∀ x < (wheelOf q0 tabs).1, x % 8 = q0 → (∀ e ∈ tabs, e.2.get! (x % e.1) ≠ 0) →
        x ∈ (wheelOf q0 tabs).2 := by
  have := wheel_fold q0 tabs [] 8 [q0] (by norm_num) (dvd_refl 8) (by simp) hpos (by
    intro x hx h8x _
    have : x = q0 := by omega
    simp [this])
  simp only [List.nil_append] at this
  exact ⟨this.1, this.2.1, this.2.2.2, this.2.2.1⟩

/-! ### The sieve over `q ≤ qmax` -/

/-- Wheel residues `r`, each scanned along `r, r + W, …` up to `qmax`. -/
def sieveRun (qmax A B D q0 : Nat) (wt rest : List (Nat × ByteArray)) : Bool :=
  let st := wheelOf q0 wt
  st.2.all fun r => if r ≤ qmax then scanQ rest A B D st.1 r ((qmax - r) / st.1 + 1) else true

theorem sieveRun_sound {qmax A B D q0 : Nat} {wt rest : List (Nat × ByteArray)} (hq0 : q0 < 8)
    (hpos : ∀ e ∈ wt, 0 < e.1) (h : sieveRun qmax A B D q0 wt rest = true) :
    ∀ q ≤ qmax, q % 8 = q0 → (∀ e ∈ wt, e.2.get! (q % e.1) ≠ 0) →
      (∀ e ∈ rest, e.2.get! (q % e.1) ≠ 0) → (isSq (A * q + D) && isSq (B * q + D)) = false := by
  intro q hq h8 hw hr
  obtain ⟨hW, hW8, hWdiv, hcomp⟩ := wheel_complete hq0 wt hpos
  set st := wheelOf q0 wt with hst
  have hrlt : q % st.1 < st.1 := Nat.mod_lt _ hW
  have hr8 : q % st.1 % 8 = q0 := by rw [Nat.mod_mod_of_dvd _ hW8]; exact h8
  have hrpass : ∀ e ∈ wt, e.2.get! (q % st.1 % e.1) ≠ 0 := by
    intro e he
    rw [Nat.mod_mod_of_dvd _ (hWdiv e he)]; exact hw e he
  have hmem := hcomp (q % st.1) hrlt hr8 hrpass
  unfold sieveRun at h
  simp only [List.all_eq_true] at h
  have hr_le : q % st.1 ≤ qmax := le_trans (Nat.mod_le _ _) hq
  have hscan := h (q % st.1) hmem
  rw [if_pos hr_le] at hscan
  have hj : q / st.1 < (qmax - q % st.1) / st.1 + 1 := by
    have h1 : q / st.1 ≤ (qmax - q % st.1) / st.1 := by
      rw [Nat.le_div_iff_mul_le hW, mul_comm]
      have h0 := Nat.mod_add_div q st.1
      generalize st.1 * (q / st.1) = m at h0 ⊢
      omega
    omega
  have hqe : q % st.1 + st.1 * (q / st.1) = q := Nat.mod_add_div q st.1
  have := scanQ_sound rest A B D st.1 _ (q % st.1) (by simpa using hscan) (q / st.1) hj (by
    rw [hqe]; exact allPass_of_forall hr)
  rwa [hqe] at this

end QS

end Erdos307
