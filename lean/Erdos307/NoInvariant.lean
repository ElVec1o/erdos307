import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The certificate route, closed

This file formalises the structural results that close the pointwise route to the negative
direction of \#307, so that the chain from `thm:halflyap` to `thm:noinvariant` is machine-checked
rather than merely written out.

Two independent statements.

* **The mass-sum threshold** (`prop:masssumthreshold`). The argument of `thm:halflyap` uses only the
  bound `σ(n) + σ(n') < c`. Asking for `f` with `f x - f y > log x` on `{x + y < c}` is possible
  exactly when `c ≤ 2`: `half_works` gives `f = x/2` for `c ≤ 2`, and `no_f_above_two` shows the
  demand is contradictory for every `c > 2`, by the single point `x = y` with `1 < x < c/2`, where
  the left side vanishes and the right side is positive. So the region of `thm:halflyap` is not an
  artefact of the choice `λ = 1/2`; it is the exact reach of the mass-sum hypothesis.

* **Universality of the ansatz** (`prop:lyapuniversal`). Because `σ` is injective on squarefree
  integers (`lem:sigmainj`, `Erdos307.Injective`), the family `δ = log n + f (σ n)` of
  `def:lyap` is not a family at all: `exists_f_of_injective` shows every `δ` whatsoever has that
  shape. `increment_iff` then turns `δ (n') < δ n` into the criterion `(∗)` verbatim. Together they
  say that searching the ansatz is searching the space of all functions, which is why the tournament
  that produced `δ_λ` could not have been easier than the problem, and why `thm:lyapfalse` closes
  the branch rather than merely one candidate.

Nothing here decides \#307. These are statements about methods.

Paper: Proposition `prop:masssumthreshold`, Proposition `prop:lyapuniversal`, Theorem
`thm:noinvariant`.
-/

namespace Erdos307

open Real

/-! ### The mass-sum threshold -/

/-- For `c ≤ 2` the demand is met by `f x = x / 2`, which is `thm:halflyap`. -/
theorem half_works {c x y : ℝ} (hc : c ≤ 2) (hx : 0 < x) (_hy : 0 < y) (h : x + y < c) :
    Real.log x < x / 2 - y / 2 := by
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  have : y < 2 - x := by linarith
  linarith

/-- **`prop:masssumthreshold`, the negative half.** For every `c > 2` there is no `f` at all with
`f x - f y > log x` throughout `{x, y > 0, x + y < c}`. The witness is the diagonal point `x = y`
with `1 < x < c / 2`: there the right side is `0` and the left side is positive. -/
theorem no_f_above_two {c : ℝ} (hc : 2 < c) :
    ¬ ∃ f : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → x + y < c → Real.log x < f x - f y := by
  rintro ⟨f, hf⟩
  -- a point strictly between 1 and c/2
  set x : ℝ := (1 + c / 2) / 2 with hxdef
  have hx1 : 1 < x := by rw [hxdef]; linarith
  have hxc : x + x < c := by rw [hxdef]; linarith
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  have := hf x x hxpos hxpos hxc
  have hlog : 0 < Real.log x := Real.log_pos hx1
  simp at this
  linarith

/-- The threshold, both halves together: solvable at `c = 2`, unsolvable above it. -/
theorem mass_sum_threshold :
    (∀ x y : ℝ, 0 < x → 0 < y → x + y < 2 → Real.log x < x / 2 - y / 2) ∧
    ∀ c : ℝ, 2 < c → ¬ ∃ f : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → x + y < c →
      Real.log x < f x - f y :=
  ⟨fun _ _ hx hy h => half_works le_rfl hx hy h, fun _ hc => no_f_above_two hc⟩

/-- **`prop:masssumthreshold`, uniqueness of the constant.** If the linear function `f = l * id`
solves the mass-sum demand at `c = 2`, then `l = 1/2`. The proof is a local-minimum argument rather
than a two-sided limit: letting `y` rise to `2 - x` gives `log x ≤ 2l(x-1)` throughout `(0,2)`, so
`g(x) = 2l(x-1) - log x` is nonnegative there and vanishes at `1`, making `1` a local minimum; its
derivative `2l - 1` must therefore vanish. -/
theorem lambda_eq_half {l : ℝ}
    (h : ∀ x y : ℝ, 0 < x → 0 < y → x + y < 2 → Real.log x < l * (x - y)) :
    l = 1 / 2 := by
  -- the constant is positive, from a single point with `x > 1 > y`
  have hlpos : 0 < l := by
    have h1 : Real.log (3 / 2) < l * (3 / 2 - 1 / 10) :=
      h (3 / 2) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    have h2 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    nlinarith
  -- letting `y` rise to `2 - x` gives the limiting inequality on all of `(0,2)`
  have key : ∀ x : ℝ, 0 < x → x < 2 → Real.log x ≤ 2 * l * (x - 1) := by
    intro x hx hx2
    refine le_of_forall_pos_lt_add ?_
    intro e he
    set d : ℝ := min (e / l) ((2 - x) / 2) with hd
    have hdpos : 0 < d := lt_min (div_pos he hlpos) (by linarith)
    have hdle : d ≤ e / l := min_le_left _ _
    have hdle2 : d ≤ (2 - x) / 2 := min_le_right _ _
    have hy : 0 < 2 - x - d := by linarith
    have hlt := h x (2 - x - d) hx hy (by linarith)
    have hld : l * d ≤ e := by
      have : l * d ≤ l * (e / l) := by nlinarith
      rwa [mul_div_cancel₀ _ (ne_of_gt hlpos)] at this
    nlinarith
  -- `1` is a local minimum of `g`, so `g' 1 = 0`
  have hmin : IsLocalMin (fun x : ℝ => 2 * l * (x - 1) - Real.log x) 1 := by
    have hmem : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hmem] with x hx
    have hk := key x hx.1 hx.2
    simp only [Real.log_one]
    linarith
  have hderiv : HasDerivAt (fun x : ℝ => 2 * l * (x - 1) - Real.log x) (2 * l - 1) 1 := by
    have h1 : HasDerivAt (fun x : ℝ => 2 * l * (x - 1)) (2 * l) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).sub_const 1).const_mul (2 * l)
    have h2 : HasDerivAt Real.log 1 1 := by
      simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h1.sub h2
  have := hmin.hasDerivAt_eq_zero hderiv
  linarith

/-! ### Universality of the ansatz -/

/-- **`prop:lyapuniversal`, the reduction.** If `σ` is injective then *every* `δ` is of the form
`L + f ∘ σ`. With `L n = log n` and `σ` the mass, this is `def:lyap`'s ansatz, so the ansatz
restricts nothing: `lem:sigmainj` is exactly what collapses the family to the whole function space. -/
theorem exists_f_of_injective {S : Type*} [Nonempty S] (σ : S → ℝ) (hσ : Function.Injective σ)
    (δ L : S → ℝ) : ∃ f : ℝ → ℝ, ∀ n, δ n = L n + f (σ n) := by
  classical
  refine ⟨fun x => δ (Function.invFun σ x) - L (Function.invFun σ x), fun n => ?_⟩
  show δ n = L n + (δ (Function.invFun σ (σ n)) - L (Function.invFun σ (σ n)))
  rw [Function.leftInverse_invFun hσ n]
  ring

/-- The translation between a decreasing `δ` and the criterion `(∗)`. With `L n = log n` and
`L (n') = L n + log (σ n)`, which is `n' = n σ(n)`, the increment `δ (n') < δ n` is exactly
`log (σ n) < f (σ n) - f (σ n')`. -/
theorem increment_iff {S : Type*} (σ L δ : S → ℝ) (f : ℝ → ℝ) (D : S → S)
    (hδ : ∀ n, δ n = L n + f (σ n))
    (hL : ∀ n, L (D n) = L n + Real.log (σ n)) (n : S) :
    δ (D n) < δ n ↔ Real.log (σ n) < f (σ n) - f (σ (D n)) := by
  rw [hδ (D n), hδ n, hL n]
  constructor <;> intro h <;> linarith

/-- **The sign branch of `thm:noinvariant`, in the form used there.** If some `δ` decreases along
`D`, then `D` has no periodic point of period two; and by `exists_f_of_injective` such a `δ` is
equivalent to a solution of `(∗)`, which `thm:lyapfalse` refutes. Stated for period two because that
is the case `\#307` asks about; the same proof kills every period. -/
theorem no_two_cycle_of_decreasing {S : Type*} (δ : S → ℝ) (D : S → S)
    (hdec : ∀ n, δ (D n) < δ n) (a : S) : D (D a) ≠ a := by
  intro h
  have h1 : δ (D a) < δ a := hdec a
  have h2 : δ (D (D a)) < δ (D a) := hdec (D a)
  rw [h] at h2
  linarith

end Erdos307
