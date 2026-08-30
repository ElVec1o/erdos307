import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-!
# The two complete character sums of `prop:localcomplete`

Regime (iii) of `prop:localcomplete` consumes two classical evaluations, supplied to
`Erdos307.regime_three_count` as hypotheses because Mathlib carries neither:

* the linear sum `∑_q χ(aq+b) = 0` for `a ≠ 0`;
* the quadratic sum `∑_q χ((aq+b)(cq+d)) = -χ(ac)` for `ad ≠ bc`.

Both are proved here for the quadratic character of a finite field of odd characteristic, so the
regime is no longer conditional on a cited input. The first is the reindexing `q ↦ aq+b`, a
bijection when `a ≠ 0`, followed by `quadraticChar_sum_zero`. The second is the classical argument:
factor out `χ(ac)`, translate to `∑_u χ(u(u+e))` with `e ≠ 0`, and for `u ≠ 0` write
`u(u+e) = u²(1 + e/u)`, so `χ` of it is `χ(1 + e/u)`; the map `u ↦ e/u` permutes the nonzero
elements, leaving `∑_{t ≠ 0} χ(1+t) = ∑_t χ(1+t) - χ(1) = -1`.

Paper: Proposition `prop:localcomplete`.
-/

namespace Erdos307

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The linear complete sum.** For `a ≠ 0` the map `q ↦ aq + b` is a bijection of `F`, so the sum
of the quadratic character over an affine line is the sum over `F`, which vanishes. -/
theorem sum_quadraticChar_affine (hF : ringChar F ≠ 2) {a b : F} (ha : a ≠ 0) :
    ∑ q : F, quadraticChar F (a * q + b) = 0 := by
  refine Eq.trans ?_ (quadraticChar_sum_zero (F := F) hF)
  refine Fintype.sum_equiv ((Equiv.mulLeft₀ a ha).trans (Equiv.addRight b))
    (fun q => quadraticChar F (a * q + b)) (fun x => quadraticChar F x) ?_
  intro q
  simp


/-- The core evaluation: for `e ≠ 0`, `∑_u χ(u(u+e)) = -1`. For `u ≠ 0` write
`u(u+e) = u²(1 + e/u)`, so the character value is `χ(1 + e/u)`; and `u ↦ e/u` permutes the nonzero
elements, so the sum becomes `∑_{t ≠ 0} χ(1+t) = ∑_t χ(1+t) - χ(1) = 0 - 1`. -/
theorem sum_quadraticChar_shift (hF : ringChar F ≠ 2) {e : F} (he : e ≠ 0) :
    ∑ u : F, quadraticChar F (u * (u + e)) = -1 := by
  classical
  -- restrict to the nonzero u, the u = 0 term vanishing
  have hsplit : ∑ u : F, quadraticChar F (u * (u + e))
      = ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (u * (u + e)) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]
    simp
  -- on the nonzero u the value is χ(1 + e/u)
  have hval : ∀ u ∈ Finset.univ.erase (0 : F),
      quadraticChar F (u * (u + e)) = quadraticChar F (1 + e / u) := by
    intro u hu
    have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
    have hfac : u * (u + e) = u ^ 2 * (1 + e / u) := by field_simp
    rw [hfac, map_mul, quadraticChar_sq_one' hu0, one_mul]
  rw [hsplit, Finset.sum_congr rfl hval]
  -- reindex u ↦ e/u, a bijection of the nonzero elements
  have hreidx : ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (1 + e / u)
      = ∑ t ∈ Finset.univ.erase (0 : F), quadraticChar F (1 + t) := by
    refine Finset.sum_nbij' (fun u => e / u) (fun t => e / t) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
      exact Finset.mem_erase.mpr ⟨div_ne_zero he hu0, Finset.mem_univ _⟩
    · intro t ht
      have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
      exact Finset.mem_erase.mpr ⟨div_ne_zero he ht0, Finset.mem_univ _⟩
    · intro u hu
      have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
      field_simp
    · intro t ht
      have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
      field_simp
    · intro u _; rfl
  rw [hreidx]
  -- and ∑_{t ≠ 0} χ(1+t) = ∑_t χ(1+t) - χ(1)
  have hall : ∑ t : F, quadraticChar F (1 + t) = 0 := by
    have h := sum_quadraticChar_affine (F := F) hF (a := 1) (b := 1) one_ne_zero
    simp only [one_mul] at h
    simpa [add_comm] using h
  have hsum : (∑ t ∈ Finset.univ.erase (0 : F), quadraticChar F (1 + t))
      + quadraticChar F (1 + (0 : F)) = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]
    exact hall
  simp only [add_zero, map_one] at hsum
  linarith

/-- **The quadratic complete sum.** For `a, c ≠ 0` and `ad ≠ bc`,
`∑_q χ((aq+b)(cq+d)) = -χ(ac)`. -/
theorem sum_quadraticChar_quadratic (hF : ringChar F ≠ 2) {a b c d : F}
    (ha : a ≠ 0) (hc : c ≠ 0) (hne : a * d ≠ b * c) :
    ∑ q : F, quadraticChar F ((a * q + b) * (c * q + d)) = -quadraticChar F (a * c) := by
  classical
  set β := b / a with hβ
  set δ := d / c with hδ
  have hfac : ∀ q : F, (a * q + b) * (c * q + d) = (a * c) * ((q + β) * (q + δ)) := by
    intro q
    rw [hβ, hδ]
    field_simp
  have hβδ : δ - β ≠ 0 := by
    rw [sub_ne_zero, hδ, hβ]
    intro h
    apply hne
    field_simp at h
    linear_combination h
  have hstep : ∑ q : F, quadraticChar F ((q + β) * (q + δ)) = -1 := by
    have hshift : ∑ q : F, quadraticChar F ((q + β) * (q + δ))
        = ∑ u : F, quadraticChar F (u * (u + (δ - β))) := by
      refine Fintype.sum_equiv (Equiv.addRight β)
        (fun q => quadraticChar F ((q + β) * (q + δ)))
        (fun u => quadraticChar F (u * (u + (δ - β)))) ?_
      intro q
      simp only [Equiv.coe_addRight]
      congr 1
      ring
    rw [hshift]
    exact sum_quadraticChar_shift hF hβδ
  calc ∑ q : F, quadraticChar F ((a * q + b) * (c * q + d))
      = ∑ q : F, quadraticChar F (a * c) * quadraticChar F ((q + β) * (q + δ)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hfac q, map_mul]
    _ = quadraticChar F (a * c) * ∑ q : F, quadraticChar F ((q + β) * (q + δ)) := by
        rw [Finset.mul_sum]
    _ = -quadraticChar F (a * c) := by rw [hstep]; ring

end Erdos307
