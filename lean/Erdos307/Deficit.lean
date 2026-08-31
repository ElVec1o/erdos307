import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.FieldSimp

/-!
# The algebraic layer of the uniform deficit bounds

`lem:deficit` bounds, uniformly in `p` and `q`, the number of squarefree `m ≤ N` with
`σ_p(m) ≡ c (mod p)` — and the two-prime version. Its analytic half (Halász, Siegel–Walfisz,
Siegel, the zero-free region) is not in Mathlib and is recorded as a blocker in `COVERAGE.md`.
Three lemmas *from* its algebraic half are formalised here. This is not the whole algebraic
layer: the Gauss-sum modulus `|τ(ψ₁)| = √p` giving `|c_ψ| = √p/(p-1)` for non-principal `ψ`, the
CRT factorisation `c_ψ = c⁽ᵖ⁾ c⁽ᑫ⁾`, and the Parseval/Cauchy–Schwarz bound
`∑_{ψ≠ψ₀}|c_ψ| ≤ √φ(pq)` are algebraic too and are **not** formalised here.

* `sigmaP_add_of_coprime` — `σ_p` is additive on coprime arguments, which is what makes the
  detector `e_p(t · σ_p(m))` multiplicative in `m` and so admissible for Halász. This is the
  only place the arithmetic of `m` enters the proof at all.
* `detector` — orthogonality: `∑_t e_p(t·x)` is `p` when `x = 0` and `0` otherwise. This is the
  identity that turns the congruence condition into a character sum, and it supplies the main
  term `N/p` (the `t = 0` contribution) as well as the requirement on the rest.
* `ramanujan` — `∑_{b ≠ 0} e_p(b) = -1`, and `principal_coeff`, which carries the reindexing
  `b ↦ s·b⁻¹` and the `1/(p-1)` normalisation to give the paper's principal Fourier coefficient
  `c⁽ᵖ⁾_{ψ₁,₀} = -1/(p-1)` in full. That is why the distance constant of `lem:deficit` is
  `1 - 1/(p-1) → 1`, larger than the `1 - √r/φ(r)` of `lem:charcancelunif`, and hence why the
  deficit bounds need no analogue of that lemma's `r ≥ 7` restriction. Only the principal
  character is treated.

The naming follows the paper. Nothing here is analytic; nothing here uses `native_decide`.

Paper: `lem:deficit`, three lemmas from the algebraic layer of its proof (not all of it), whose analytic half is the starred blocker recorded in
`COVERAGE.md`; `lem:symbolfact` for `σ_p`; `prop:condrate` consumes the bounds.
-/

namespace Erdos307

open Finset AddChar

variable (p : ℕ)

/-- `σ_p(m) = ∑_{ℓ ∣ m, ℓ prime} ℓ⁻¹` in `ℤ/p`, the symbol of `lem:symbolfact`. For squarefree
`m` coprime to `p` the paper's `m' ≡ m · σ_p(m)` holds, so `p ∣ m' - c·m ↔ σ_p(m) ≡ c`. -/
def sigmaP (m : ℕ) : ZMod p := ∑ l ∈ m.primeFactors, (l : ZMod p)⁻¹

@[simp] lemma sigmaP_one : sigmaP p 1 = 0 := by simp [sigmaP]

/-- **`σ_p` is additive on coprime arguments.** This is the whole reason the detector is
multiplicative, and hence the whole reason Halász's theorem applies. -/
theorem sigmaP_add_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaP p (m * n) = sigmaP p m + sigmaP p n := by
  classical
  unfold sigmaP
  rw [h.primeFactors_mul, Finset.sum_union h.disjoint_primeFactors]

/-- Consequently the detector is multiplicative on coprime arguments: this is the displayed
identity `e_p(t·σ_p(mn)) = e_p(t·σ_p(m))·e_p(t·σ_p(n))` of the proof. -/
theorem detector_mul_of_coprime (ψ : AddChar (ZMod p) ℂ) (t : ZMod p) {m n : ℕ}
    (h : Nat.Coprime m n) :
    ψ (t * sigmaP p (m * n)) = ψ (t * sigmaP p m) * ψ (t * sigmaP p n) := by
  rw [sigmaP_add_of_coprime p h, mul_add, ψ.map_add_eq_mul]

section Orthogonality

variable [NeZero p]

/-- **Orthogonality / the detector.** `∑_{t} e_p(t·x)` is `p` if `x = 0` and `0` otherwise.
The `x = 0` branch is the main term `N/p` of `lem:deficit`; the other branch is what the
analytic half must bound. -/
theorem detector (x : ZMod p) :
    ∑ t : ZMod p, ZMod.stdAddChar (t * x) = if x = 0 then (p : ℂ) else 0 := by
  classical
  have h : ∀ t : ZMod p, ZMod.stdAddChar (t * x)
      = AddChar.mulShift (ZMod.stdAddChar (N := p)) x t := by
    intro t; simp [AddChar.mulShift_apply, mul_comm]
  rw [Finset.sum_congr rfl (fun t _ => h t), AddChar.sum_eq_ite]
  by_cases hx : x = 0
  · have hz : AddChar.mulShift (ZMod.stdAddChar (N := p)) x = 0 := by
      ext t; simp [hx]
    rw [if_pos hz, if_pos hx, ZMod.card]
  · have hne : AddChar.mulShift (ZMod.stdAddChar (N := p)) x ≠ 0 :=
      ZMod.isPrimitive_stdAddChar p hx
    rw [if_neg hne, if_neg hx]

/-- **The Ramanujan sum.** `∑_{b ≠ 0} e_p(b) = -1`: the full sum vanishes and the omitted term is
`e_p(0) = 1`. This is the principal Fourier coefficient of `a ↦ e_p(t a⁻¹)`, so the distance
constant of `lem:deficit` is `1 - 1/(p-1) → 1`, larger than the `1 - √r/φ(r)` of
`lem:charcancelunif` — which is why the deficit bounds need no analogue of its `r ≥ 7` cutoff. -/
theorem ramanujan (hp : 1 < p) :
    ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, ZMod.stdAddChar b = -1 := by
  classical
  haveI : Fact (1 < p) := ⟨hp⟩
  have hall : ∑ b : ZMod p, ZMod.stdAddChar b = 0 := by
    have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
    have hd := detector (p := p) 1
    rw [if_neg h1] at hd
    simpa using hd
  have hsplit : ZMod.stdAddChar (0 : ZMod p)
      + ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, ZMod.stdAddChar b
      = ∑ b : ZMod p, ZMod.stdAddChar b :=
    Finset.add_sum_erase _ _ (Finset.mem_univ 0)
  rw [hall, AddChar.map_zero_eq_one] at hsplit
  exact eq_neg_of_add_eq_zero_right hsplit


/-- **The principal Fourier coefficient.** For `p` prime and `s ≠ 0`,
`(p-1)⁻¹ · ∑_{b ≠ 0} e_p(s·b⁻¹) = -(p-1)⁻¹`.

This is the paper's `c^{(p)}_{ψ₁,₀} = -1/(p-1)` in full: the reindexing, the `1/(p-1)`
normalisation, and the Ramanujan evaluation. It is why the distance constant of `lem:deficit` is
`1 - 1/(p-1) → 1`, larger than the `1 - √r/φ(r)` of `lem:charcancelunif`, and so why the deficit
bounds need no analogue of that lemma's `r ≥ 7` cutoff. Only the **principal** character is treated:
the non-principal coefficients `|c_ψ| = √p/(p-1)` need the Gauss-sum modulus, which is not
formalised here. -/
theorem principal_coeff (hp : p.Prime) {s : ZMod p} (hs : s ≠ 0) :
    ((p : ℂ) - 1)⁻¹ * ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        ZMod.stdAddChar (s * b⁻¹) = -((p : ℂ) - 1)⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hmaps : ∀ b ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      s * b⁻¹ ∈ (Finset.univ : Finset (ZMod p)).erase 0 := by
    intro b hb
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    exact Finset.mem_erase.mpr ⟨mul_ne_zero hs (inv_ne_zero hb0), Finset.mem_univ _⟩
  have hre : ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, ZMod.stdAddChar (s * b⁻¹)
      = ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, ZMod.stdAddChar b := by
    refine Finset.sum_nbij' (fun b => s * b⁻¹) (fun c => s * c⁻¹) hmaps hmaps ?_ ?_ ?_
    · intro b hb
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
      field_simp
    · intro c hc
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      field_simp
    · intro b _; rfl
  rw [hre, ramanujan p hp.one_lt, mul_neg, mul_one]

end Orthogonality

end Erdos307
