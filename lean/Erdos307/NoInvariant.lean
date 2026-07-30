import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
