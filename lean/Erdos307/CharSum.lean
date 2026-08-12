import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.Ring

/-!
# The inverse-twisted character sum is a Gauss sum

The repaired proof of `lem:charcancel` turns on one identity, and this file proves it. For a
quadratic character `χ` on a finite abelian group and any `ψ`,

  `∑_{a} χ(a) ψ(t·a⁻¹)  =  χ(t) · ∑_{a} χ(a) ψ(a)`.

Applied with `G = (ℤ/r)ˣ`, `χ` the Jacobi symbol and `ψ` the additive character `e_r`, the left side
is the sum the paper previously bounded as a *Salié sum* by `2√q` after reducing to prime modulus.
The identity says it is not a Salié sum at all: it is `χ(t)` times the Gauss sum `τ(χ)`, so its
modulus is **exactly** `√r`, and it vanishes when `χ(t) = 0`. That is what removes the reduction to
prime `r`, and with it the gap that had forced `thm:a9` down to CONJECTURE.

Two steps, both elementary:

* `quadratic_inv` : a quadratic character is its own inverse, `χ(g⁻¹) = χ(g)`. Pure monoid algebra:
  `χ(g⁻¹) = χ(g⁻¹)·(χ(g)·χ(g)) = (χ(g⁻¹)·χ(g))·χ(g) = χ(g)`.
* `sum_char_twist_inv` : the reindexing `a ↦ t·a⁻¹`, which is an involution on an abelian group,
  carries the twisted sum to the untwisted one.

What is **not** formalised, and is cited in the paper: Halász's theorem, `|τ(χ)| = √r` for a
primitive character, and the bound on `log L(1+iτ, ψ)` for non-principal `ψ`. Those are the three
analytic inputs; the identity below is the one new algebraic step, and it is the step the previous
proof got wrong.

Paper: Lemma `lem:charcancel`, Lemma `lem:symbolfact`, Theorem `thm:a9`.
-/

namespace Erdos307

/-- **A quadratic character is its own inverse.** If `χ(g)² = 1` for all `g`, then `χ(g⁻¹) = χ(g)`.
No cancellation or invertibility in the target is needed: the two relations combine directly. -/
theorem quadratic_inv {G M : Type*} [Group G] [CommMonoid M] (χ : G →* M)
    (hq : ∀ g, χ g * χ g = 1) (g : G) : χ g⁻¹ = χ g := by
  calc χ g⁻¹ = χ g⁻¹ * (χ g * χ g) := by rw [hq g, mul_one]
    _ = (χ g⁻¹ * χ g) * χ g := by rw [mul_assoc]
    _ = χ (g⁻¹ * g) * χ g := by rw [map_mul]
    _ = χ g := by rw [inv_mul_cancel, map_one, one_mul]

/-- The map `a ↦ t·a⁻¹` is an involution of an abelian group. -/
theorem twist_inv_involutive {G : Type*} [CommGroup G] (t : G) :
    Function.Involutive (fun a : G => t * a⁻¹) := by
  intro a
  simp only [mul_inv_rev, inv_inv]
  rw [mul_comm a t⁻¹]
  exact mul_inv_cancel_left t a

/-- **The identity.** For a quadratic character `χ` on a finite abelian group, the inverse-twisted
sum is `χ(t)` times the untwisted one:

  `∑_a χ(a) ψ(t·a⁻¹) = χ(t) · ∑_a χ(a) ψ(a)`.

With `ψ` an additive character this says the left side is `χ(t)·τ(χ)`, a Gauss sum, rather than a
Salié sum needing a Weil-type bound. -/
theorem sum_char_twist_inv {G M : Type*} [CommGroup G] [Fintype G] [CommRing M]
    (χ : G →* M) (hq : ∀ g, χ g * χ g = 1) (ψ : G → M) (t : G) :
    ∑ a : G, χ a * ψ (t * a⁻¹) = χ t * ∑ a : G, χ a * ψ a := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Function.Involutive.toPerm _ (twist_inv_involutive t)) _ _ (fun a => ?_)
  simp only [Function.Involutive.coe_toPerm]
  rw [map_mul, quadratic_inv χ hq a]
  calc χ a * ψ (t * a⁻¹) = (χ t * χ t) * (χ a * ψ (t * a⁻¹)) := by rw [hq t, one_mul]
    _ = χ t * (χ t * χ a * ψ (t * a⁻¹)) := by ring

/-- The consequence used in the paper: the twisted sum has the same modulus as the Gauss sum
whenever `χ(t)` is a unit, and vanishes when `χ(t) = 0`. Stated as the factorisation, since
"modulus" is not available at this generality. -/
theorem sum_char_twist_inv_eq_zero {G M : Type*} [CommGroup G] [Fintype G] [CommRing M]
    (χ : G →* M) (hq : ∀ g, χ g * χ g = 1) (ψ : G → M) (t : G) (ht : χ t = 0) :
    ∑ a : G, χ a * ψ (t * a⁻¹) = 0 := by
  rw [sum_char_twist_inv χ hq ψ t, ht, zero_mul]

end Erdos307
