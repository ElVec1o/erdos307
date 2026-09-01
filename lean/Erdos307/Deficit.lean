import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Order.Chebyshev

/-!
# The algebraic layer of the uniform deficit bounds

`lem:deficit` bounds, uniformly in `p` and `q`, the number of squarefree `m ≤ N` with
`σ_p(m) ≡ c (mod p)` — and the two-prime version. Its analytic half (Halász, Siegel–Walfisz,
Siegel, the zero-free region) is not in Mathlib and is recorded as a blocker in `COVERAGE.md`.
Its *algebraic core* is formalised here. This file does **not** carry the whole algebraic layer,
and three successive drafts of this docstring claimed that it did. What is here:

* `sigmaP_add_of_coprime`, `detector_mul_of_coprime` — `σ_p` is additive on coprime arguments, so
  the detector `e_p(t·σ_p(m))` is multiplicative in `m` and hence admissible for Halász. This is
  the only place the arithmetic of `m` enters the proof at all.
* `detector` — orthogonality, `∑_t e_p(t·x) = p` or `0`. The `x = 0` branch is the main term.
* `ramanujan`, `principal_coeff` — `∑_{b≠0} e_p(b) = -1`, and with the reindexing `b ↦ s·b⁻¹` and
  the `1/(p-1)` normalisation, the paper's principal Fourier coefficient `c⁽ᵖ⁾_{ψ₁,₀} = -1/(p-1)`.
  That is why the distance constant of `lem:deficit` is `1 - 1/(p-1) → 1`, larger than the
  `1 - √r/φ(r)` of `lem:charcancelunif`, and hence why the deficit bounds need no analogue of that
  lemma's `r ≥ 7` cutoff.
* `gaussSum_modulus` — `τ(χ)·τ(χ⁻¹,ψ⁻¹) = p`. Note this stops **short** of `|τ(χ)| = √p` and so
  short of the coefficient value `|c_ψ| = √p/(p-1)` it is the input to.
* `coeff_factor` — the sum over a product group splits. This is the algebraic content behind the
  CRT factorisation `c_ψ = c⁽ᵖ⁾c⁽ᑫ⁾`, but stated generically: it is not the CRT step itself, which
  would need the ring equivalence and the character correspondence.
* `sum_nonprincipal_le` — Cauchy–Schwarz: total square mass `1` forces `ℓ¹` mass `≤ √(card-1)` off
  the principal term. This is the step that fixes the range of both uniform lemmas — it is where
  `√r · log L = o(L)`, and hence `r ≤ L²/(log L)^{2+ε}`, comes from. Parseval itself is a
  *hypothesis* here, not a theorem.

What is **not** here, and is not analytic either: the additive detection identity in the form the
proof uses; the `(0,0)`-term and `pq-1`-term bookkeeping; `|τ(χ)| = √p` and the coefficient value;
the CRT step proper; the three-case bound on `|c_{ψ₀}|` (one case of which a review found wrong in
the paper); Parseval; and the closing `pq ≤ L² ⇒ N(log N)^{-1/2} = o(N/(pq))`.

The naming follows the paper. Nothing here is analytic; nothing here uses `native_decide`.

Paper: `lem:deficit`, the algebraic core of its proof (see the list above for what is and is not covered), whose analytic half is the starred blocker recorded in
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


/-! ### The coefficient bookkeeping

Three further steps of `lem:deficit`'s algebraic layer. Together with `principal_coeff` they are
what the proof needs about the Fourier coefficients `c_ψ` before any analysis begins: how large the
non-principal ones are (Gauss sum), that they factor across the two primes (CRT), and that their
total mass is controlled (Parseval plus Cauchy--Schwarz).
-/

/-- **Gauss-sum modulus.** For a non-principal `χ` on `ℤ/p` and the standard primitive additive
character, `τ(χ)·τ(χ⁻¹, ψ⁻¹) = p`. This is the input behind the paper's
`|c_ψ| = √p/(p-1)` for non-principal `ψ`. -/
theorem gaussSum_modulus (hp : p.Prime) {χ : MulChar (ZMod p) ℂ} (hχ : χ ≠ 1) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ (ZMod.stdAddChar⁻¹) = (p : ℂ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have := gaussSum_mul_gaussSum_eq_card hχ (ZMod.isPrimitive_stdAddChar p)
  simpa [ZMod.card] using this

/-- **The CRT factorisation.** A coefficient built from a `p`-part and a `q`-part factors as the
product of the two coefficients. This is the paper's `c_ψ = c⁽ᵖ⁾_{ψ₁}·c⁽ᑫ⁾_{ψ₂}`, in the form the
proof actually uses: the sum over the product group splits. -/
theorem coeff_factor {G H : Type*} [Fintype G] [Fintype H] (f : G → ℂ) (g : H → ℂ) :
    ∑ x : G × H, f x.1 * g x.2 = (∑ a : G, f a) * (∑ b : H, g b) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- **Parseval plus Cauchy--Schwarz.** If the coefficients have total square mass `1`, the
non-principal ones have `ℓ¹` mass at most `√(card - 1)`. This is the paper's
`∑_{ψ≠ψ₀}|c_ψ| ≤ √(φ(pq))`, which is the step that fixes the range of both uniform lemmas: it is
where `√r · log L = o(L)` comes from, and hence where `r ≤ L²/(log L)^{2+ε}` comes from. -/
theorem sum_nonprincipal_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (psi0 : ι)
    (hnn : ∀ i, 0 ≤ c i) (hpar : ∑ i, (c i) ^ 2 = 1) :
    ∑ i ∈ (Finset.univ : Finset ι).erase psi0, c i
      ≤ Real.sqrt ((Fintype.card ι : ℝ) - 1) := by
  classical
  set s := (Finset.univ : Finset ι).erase psi0 with hs
  have hcard : (s.card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    have : s.card = Fintype.card ι - 1 := by
      rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [this]
    have h1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨psi0⟩
    push_cast [Nat.cast_sub h1]
    ring
  have hsq : (∑ i ∈ s, c i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (c i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsub : ∑ i ∈ s, (c i) ^ 2 ≤ 1 := by
    rw [← hpar]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ => sq_nonneg (c i))
  have hle : (∑ i ∈ s, c i) ^ 2 ≤ (Fintype.card ι : ℝ) - 1 := by
    calc (∑ i ∈ s, c i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (c i) ^ 2 := hsq
      _ ≤ (s.card : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
      _ = (Fintype.card ι : ℝ) - 1 := by rw [mul_one, hcard]
  have hnonneg : 0 ≤ ∑ i ∈ s, c i := Finset.sum_nonneg fun i _ => hnn i
  calc ∑ i ∈ s, c i = Real.sqrt ((∑ i ∈ s, c i) ^ 2) := (Real.sqrt_sq hnonneg).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) - 1) := Real.sqrt_le_sqrt hle

end Orthogonality

end Erdos307
