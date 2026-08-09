import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

/-!
# No polynomial family parametrises #307

`prop:nopoly`. Let `p₁(t),…,p_k(t)` and `q₁(t),…,q_l(t)` be integer polynomials, each prime for
infinitely many `t`, with `(Σᵢ 1/pᵢ(t))(Σⱼ 1/qⱼ(t)) = 1` for infinitely many `t`. Then every `pᵢ`
and every `qⱼ` is constant: the family is a single fixed solution.

This is the load-bearing member of the whole negative account of the residue. Remark
`rem:atomised` traces the three faces of the Lehmer obstruction, rank, density exponent and `P⁺`,
to this one proposition, and shows it sits exactly on the polynomial / super-polynomial boundary:
the fraction of a term's size that Stewart's bound certifies stays bounded below precisely when the
sequence grows polynomially, which is exactly what this excludes.

The proof has two steps, and both are formalised here.

* **The limit step.** Holding at infinitely many `t`, the relation holds identically as rational
  functions. A nonconstant `pᵢ` taking infinitely many prime, hence positive, values has positive
  leading coefficient on an infinite branch, so `pᵢ(t) → +∞` there. Splitting each side into
  constants and nonconstant members, `Σᵢ 1/pᵢ = A_P + ε_P(t)` with `ε_P(t) → 0⁺`, and letting
  `t → ∞` gives `A_P·A_Q = 1`. That is `const_prod_eq_one_of_tendsto`.

* **The vanishing step.** Subtracting the limit from the identity leaves
  `A_P ε_Q + A_Q ε_P + ε_P ε_Q = 0`. Every term is nonnegative, and `A_P A_Q = 1` forces both
  constants positive, so each term vanishes and hence `ε_P = ε_Q = 0`. Since a nonconstant member
  contributes a strictly positive summand, there are none. That is `eps_eq_zero_of_identity` and
  `nonconstant_empty`.

What is *not* formalised is the passage from "holds at infinitely many `t`" to "holds identically",
and the analytic fact that a nonconstant polynomial with infinitely many prime values tends to `+∞`
on a branch; both are inputs, and both are supplied to the theorems below as hypotheses (`hid`,
`hP`, `hQ`, `hfP`, `hfQ`) rather than assumed silently.

The hypothesis worth naming is *finiteness* of the family. The splitting into constants plus a
remainder tending to `0` uses it, so a family whose support grows with `t` is not covered. That gap
is real and useless: a growing support means a growing number of simultaneous primality conditions,
which is a harder demand than one, not an easier one.

Paper: Proposition `prop:nopoly`.
-/

namespace Erdos307

open Filter Topology

/-- **The limit step.** If `(A_P + ε_P t)(A_Q + ε_Q t) = 1` for every `t` and both remainders tend
to `0`, then the constant parts already satisfy the relation: `A_P · A_Q = 1`. -/
theorem const_prod_eq_one_of_tendsto {AP AQ : ℝ} {eP eQ : ℕ → ℝ}
    (hid : ∀ t, (AP + eP t) * (AQ + eQ t) = 1)
    (hP : Tendsto eP atTop (𝓝 0)) (hQ : Tendsto eQ atTop (𝓝 0)) :
    AP * AQ = 1 := by
  have hA : Tendsto (fun t => AP + eP t) atTop (𝓝 (AP + 0)) := tendsto_const_nhds.add hP
  have hB : Tendsto (fun t => AQ + eQ t) atTop (𝓝 (AQ + 0)) := tendsto_const_nhds.add hQ
  have h : Tendsto (fun t => (AP + eP t) * (AQ + eQ t)) atTop (𝓝 (AP * AQ)) := by
    have h2 := hA.mul hB
    rwa [add_zero, add_zero] at h2
  have h1 : Tendsto (fun t => (AP + eP t) * (AQ + eQ t)) atTop (𝓝 1) := by
    simp only [hid]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h h1

/-- **The vanishing step.** Given the limit relation `A_P A_Q = 1` and the full relation at one
value of `t`, both remainders vanish there. The mechanism is that `A_P A_Q = 1` forces both
constants strictly positive, so the three nonnegative terms of the difference must each be `0`. -/
theorem eps_eq_zero_of_identity {AP AQ eP eQ : ℝ}
    (hAP : 0 ≤ AP) (hAQ : 0 ≤ AQ) (hP : 0 ≤ eP) (hQ : 0 ≤ eQ)
    (hconst : AP * AQ = 1) (hfull : (AP + eP) * (AQ + eQ) = 1) :
    eP = 0 ∧ eQ = 0 := by
  have hAP' : 0 < AP := by
    rcases eq_or_lt_of_le hAP with h | h
    · exfalso; rw [← h, zero_mul] at hconst; exact zero_ne_one hconst
    · exact h
  have hAQ' : 0 < AQ := by
    rcases eq_or_lt_of_le hAQ with h | h
    · exfalso; rw [← h, mul_zero] at hconst; exact zero_ne_one hconst
    · exact h
  have key : AP * eQ + AQ * eP + eP * eQ = 0 := by linear_combination hfull - hconst
  have h1 : 0 ≤ AP * eQ := mul_nonneg hAP hQ
  have h2 : 0 ≤ AQ * eP := mul_nonneg hAQ hP
  have h3 : 0 ≤ eP * eQ := mul_nonneg hP hQ
  have e1 : AP * eQ = 0 := by linarith
  have e2 : AQ * eP = 0 := by linarith
  exact ⟨(mul_eq_zero.mp e2).resolve_left hAQ'.ne', (mul_eq_zero.mp e1).resolve_left hAP'.ne'⟩

/-- **`prop:nopoly`.** With the nonconstant members indexed by `NCP` and `NCQ`, each contributing a
strictly positive reciprocal, the identity forces both index sets empty: every member of the family
is constant, so the family is a single fixed solution and no polynomial parametrisation can reduce
\#307 to Bunyakovsky, Schinzel's Hypothesis H, or Bateman-Horn. -/
theorem nonconstant_empty {ι κ : Type*} {AP AQ : ℝ} {NCP : Finset ι} {NCQ : Finset κ}
    {fP : ι → ℝ} {fQ : κ → ℝ}
    (hAP : 0 ≤ AP) (hAQ : 0 ≤ AQ)
    (hfP : ∀ i ∈ NCP, 0 < fP i) (hfQ : ∀ j ∈ NCQ, 0 < fQ j)
    (hconst : AP * AQ = 1)
    (hfull : (AP + ∑ i ∈ NCP, fP i) * (AQ + ∑ j ∈ NCQ, fQ j) = 1) :
    NCP = ∅ ∧ NCQ = ∅ := by
  have hP : 0 ≤ ∑ i ∈ NCP, fP i := Finset.sum_nonneg fun i hi => (hfP i hi).le
  have hQ : 0 ≤ ∑ j ∈ NCQ, fQ j := Finset.sum_nonneg fun j hj => (hfQ j hj).le
  obtain ⟨h1, h2⟩ := eps_eq_zero_of_identity hAP hAQ hP hQ hconst hfull
  constructor
  · by_contra hne
    exact absurd h1 (Finset.sum_pos hfP (Finset.nonempty_of_ne_empty hne)).ne'
  · by_contra hne
    exact absurd h2 (Finset.sum_pos hfQ (Finset.nonempty_of_ne_empty hne)).ne'

/-- The two steps chained: from the identity at every `t`, with remainders tending to `0`, the
nonconstant part is empty at every `t`. This is the statement of `prop:nopoly` in the form the
paper uses it, with the polynomial input abstracted to its two consequences. -/
theorem nopoly {ι κ : Type*} {AP AQ : ℝ} {NCP : Finset ι} {NCQ : Finset κ}
    {fP : ℕ → ι → ℝ} {fQ : ℕ → κ → ℝ}
    (hAP : 0 ≤ AP) (hAQ : 0 ≤ AQ)
    (hfP : ∀ t, ∀ i ∈ NCP, 0 < fP t i) (hfQ : ∀ t, ∀ j ∈ NCQ, 0 < fQ t j)
    (hid : ∀ t, (AP + ∑ i ∈ NCP, fP t i) * (AQ + ∑ j ∈ NCQ, fQ t j) = 1)
    (hP : Tendsto (fun t => ∑ i ∈ NCP, fP t i) atTop (𝓝 0))
    (hQ : Tendsto (fun t => ∑ j ∈ NCQ, fQ t j) atTop (𝓝 0)) :
    NCP = ∅ ∧ NCQ = ∅ :=
  nonconstant_empty hAP hAQ (hfP 0) (hfQ 0) (const_prod_eq_one_of_tendsto hid hP hQ) (hid 0)

end Erdos307
