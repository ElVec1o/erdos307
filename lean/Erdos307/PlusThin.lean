import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The semiprime plus-layer is provably thin

`prop:plusthin`. The number of semiprime plus-hits `N = pq ≤ X` is `O(√X (log X)²)` by a fully
elementary argument, and Erdős's bound `∑_{s≤Y} τ(2s²+1) ≪ Y log Y` sharpens it to `O(√X log X)`.
Under Bunyakovsky the `p = 5` family alone contributes `≫ √X / log X`, so conditionally the count is
sandwiched and the `√X` order of the empirical law is genuine on the semiprime stratum rather than
an artefact of the tested range.

The argument has an elementary skeleton and an analytic tail, and this file separates them
completely, formalising the first and naming the second.

**The skeleton, all proved here.**

* `plus_semiprime_identity`: for a semiprime plus-hit, `s² = N' + 2N = p + q + 2pq`, and then
  `2s² + 1 = (2p+1)(2q+1)` identically. This is what converts a plus-hit into a *factorisation* of a
  value of a fixed quadratic, and it is a one-line ring identity.
* `plus_range`: `s² ≤ 3N + 1`, because `p + q ≤ pq + 1` for `p, q ≥ 1`, which is `(p-1)(q-1) ≥ 0`.
  So `s` runs only to `Y = √(3X+1)`.
* `plus_recover`: the map `N ↦ (s, {2p+1, 2q+1})` is injective, since `2p+1` recovers `p`.
* `count_le_divisor_sum`: consequently the count is at most `∑_{s≤Y} τ(2s²+1)`. This is the
  reduction the whole proposition rests on, and it is proved here in full, by injecting into the
  disjoint union of the divisor sets.
* `two_roots_quadratic`: modulo an odd prime the congruence `2s² + 1 ≡ 0` has at most two
  solutions, because it reads `s² = c` in a field and `s² = s₀²` factors as `(s-s₀)(s+s₀) = 0`. The
  paper reaches the same conclusion through the discriminant `-8` being prime to every odd modulus;
  the field form needs no discriminant, only `2 ≠ 0`.
* `card_large_le_card_small` and `tau_le_two_small`: the divisor-pairing step. Each divisor
  exceeding `√n` maps to its cofactor below `√n`, injectively, so `τ(n) ≤ 2·#{u ∣ n : u² ≤ n}` and
  the sum over `s` may be reorganised over the *small* member `u ≤ √2 Y` only. This is the step that
  turns a divisor sum into a divisibility count.

**The analytic tail, cited and not proved.** Dirichlet's `∑_{u≤Z} τ(u) ∼ Z log Z` and
`∑_{u≤Z} τ(u)/u ∼ ½(log Z)²` give the `Y(log Y)²`; Erdős's bound gives the sharpening; Bunyakovsky
gives the conditional lower bound; and the lifting of the simple roots from `ℓ` to `ℓ^j` is Hensel.
Mathlib carries none of the divisor-sum asymptotics, so the passage from `count_le_divisor_sum` to
`O(√X (log X)²)` is not available in Lean and is not asserted here.

The `ω ≥ 3` stratum remains empirical, as `prop:strata` records; nothing here touches it.

Paper: Proposition `prop:plusthin`, Proposition `prop:plus`.
-/

namespace Erdos307

open Finset

/-! ### The identity that makes the plus-layer a factorisation problem -/

/-- **`prop:plus`(i).** With `s² = N' + 2N = p + q + 2pq` for a semiprime `N = pq`, the shifted
square factors: `2s² + 1 = (2p+1)(2q+1)`. A plus-hit is therefore a nontrivial factorisation of a
value of the fixed quadratic `2s² + 1`. -/
theorem plus_semiprime_identity (p q : ℕ) :
    2 * (p + q + 2 * (p * q)) + 1 = (2 * p + 1) * (2 * q + 1) := by ring

/-- **The range.** `p + q ≤ pq + 1` for `p, q ≥ 1`, so `s² ≤ 3N + 1` and `s` runs only to
`Y = √(3X+1)`. The inequality is `(p-1)(q-1) ≥ 0`. -/
theorem plus_range {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    p + q + 2 * (p * q) ≤ 3 * (p * q) + 1 := by nlinarith

/-- `2p + 1` recovers `p`, which is why the map `N ↦ (s, {2p+1, 2q+1})` is injective. -/
theorem plus_injective_aux (p : ℕ) : (2 * p + 1 - 1) / 2 = p := by omega

/-- The injection in the form used: from the unordered factorisation the semiprime is recovered. -/
theorem plus_recover {p q u v : ℕ} (hu : u = 2 * p + 1) (hv : v = 2 * q + 1) :
    ((u - 1) / 2) * ((v - 1) / 2) = p * q := by
  subst hu; subst hv; rw [plus_injective_aux, plus_injective_aux]

/-! ### The reduction to a divisor sum -/

/-- **The reduction.** If every element of `S` carries a root `s ≤ Y` and a divisor of `2s² + 1`,
and the pair determines the element, then `|S| ≤ ∑_{s ≤ Y} τ(2s²+1)`.

Applied with `S` the set of semiprime plus-hits below `X`, `root` the `s` of
`plus_semiprime_identity` and `dv` the factor `2p+1`, this is the step that turns the plus-layer
count into a divisor sum. `plus_range` supplies `Y = √(3X+1)` and `plus_recover` the injectivity. -/
theorem count_le_divisor_sum {α : Type*} [DecidableEq α] (S : Finset α) (Y : ℕ)
    (root dv : α → ℕ)
    (hroot : ∀ a ∈ S, root a ≤ Y)
    (hdiv : ∀ a ∈ S, dv a ∈ (2 * (root a) ^ 2 + 1).divisors)
    (hinj : Set.InjOn (fun a => (root a, dv a)) S) :
    S.card ≤ ∑ s ∈ range (Y + 1), (2 * s ^ 2 + 1).divisors.card := by
  have hcard : S.card ≤ ((range (Y + 1)).biUnion
      (fun s => ({s} : Finset ℕ) ×ˢ (2 * s ^ 2 + 1).divisors)).card := by
    refine Finset.card_le_card_of_injOn (fun a => (root a, dv a)) ?_ hinj
    intro a ha
    refine Finset.mem_biUnion.mpr ⟨root a, Finset.mem_range.mpr (Nat.lt_succ_of_le (hroot a ha)),
      Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hdiv a ha⟩⟩
  refine hcard.trans (le_of_eq ?_)
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun s _ => by
      rw [Finset.card_product, Finset.card_singleton, one_mul]
  · intro x _ y _ hxy
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨a, b⟩ hab hab'
    simp only [Finset.mem_product, Finset.mem_singleton] at hab hab'
    exact hxy (hab.1.symm.trans hab'.1)

/-! ### At most two roots modulo an odd prime -/

/-- **The Hensel root count, at the prime level.** In a field, `s² = c` has at most two solutions:
given one, every other is it or its negative. -/
theorem two_roots {F : Type*} [Field F] {c s₀ s : F} (h₀ : s₀ ^ 2 = c) (h : s ^ 2 = c) :
    s = s₀ ∨ s = -s₀ := by
  have hfac : (s - s₀) * (s + s₀) = 0 := by linear_combination h - h₀
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

/-- The form that actually occurs: `2s² + 1 ≡ 0 (mod ℓ)` has at most two solutions for `ℓ` an odd
prime, so its roots are simple and lift uniquely to `ℓ^j` by Hensel (cited). This is the paper's
appeal to the discriminant `-8` being prime to every odd modulus, in the form that needs only
`2 ≠ 0`. -/
theorem two_roots_quadratic {F : Type*} [Field F] {s₀ s : F} (h2 : (2 : F) ≠ 0)
    (h₀ : 2 * s₀ ^ 2 + 1 = 0) (h : 2 * s ^ 2 + 1 = 0) :
    s = s₀ ∨ s = -s₀ := by
  have hfac : (s - s₀) * (s + s₀) * 2 = 0 := by linear_combination h - h₀
  rcases mul_eq_zero.mp hfac with h1 | h1
  · rcases mul_eq_zero.mp h1 with h3 | h3
    · exact Or.inl (sub_eq_zero.mp h3)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h3)
  · exact absurd h1 h2

/-! ### The divisor-pairing step -/

/-- Every divisor of `n` exceeding `√n` has its cofactor below `√n`, and the pairing `u ↦ n/u` is
injective. So the large divisors are no more numerous than the small ones. -/
theorem card_large_le_card_small {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.filter (fun u => ¬ (u * u ≤ n))).card
      ≤ (n.divisors.filter (fun u => u * u ≤ n)).card := by
  refine Finset.card_le_card_of_injOn (fun u => n / u) ?_ ?_
  · intro u hu
    obtain ⟨hu1, hlarge⟩ := Finset.mem_filter.mp hu
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hu1
    have hlarge' : n < u * u := not_le.mp hlarge
    have hmul : u * (n / u) = n := Nat.mul_div_cancel' hdvd
    have hlt : n / u < u := by
      by_contra hc
      push_neg at hc
      have hle : u * u ≤ u * (n / u) := Nat.mul_le_mul (le_refl u) hc
      rw [hmul] at hle
      exact absurd hlarge' (not_lt.mpr hle)
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn⟩, ?_⟩
    calc n / u * (n / u) ≤ u * (n / u) := Nat.mul_le_mul hlt.le (le_refl (n / u))
      _ = n := hmul
  · intro a ha b hb hab
    obtain ⟨ha1, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    obtain ⟨hb1, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    obtain ⟨hda, -⟩ := Nat.mem_divisors.mp ha1
    obtain ⟨hdb, -⟩ := Nat.mem_divisors.mp hb1
    have ea : a * (n / a) = n := Nat.mul_div_cancel' hda
    have eb : b * (n / b) = n := Nat.mul_div_cancel' hdb
    have hab' : n / a = n / b := hab
    rw [hab'] at ea
    have hpos : 0 < n / b :=
      Nat.pos_of_ne_zero (by intro h; rw [h, mul_zero] at eb; exact hn eb.symm)
    exact Nat.eq_of_mul_eq_mul_right hpos (ea.trans eb.symm)

/-- **`τ(n) ≤ 2·#{u ∣ n : u² ≤ n}`.** The divisor count is controlled by the small divisors alone,
which is what lets `∑_{s≤Y} τ(2s²+1)` be reorganised as a divisibility count over `u ≤ √2 Y`, the
form in which Dirichlet's estimates apply. -/
theorem tau_le_two_small {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤ 2 * (n.divisors.filter (fun u => u * u ≤ n)).card := by
  have hsplit :
      (n.divisors.filter (fun u => u * u ≤ n)).card
        + (n.divisors.filter (fun u => ¬ (u * u ≤ n))).card = n.divisors.card :=
    Finset.card_filter_add_card_filter_not (fun u => u * u ≤ n)
  have hle := card_large_le_card_small hn
  omega

end Erdos307
