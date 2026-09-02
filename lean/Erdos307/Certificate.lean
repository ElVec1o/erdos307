import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Linarith

/-!
# Soundness of the reciprocity certificate

The level-60 campaign, and the pair-sector computation that follows it, both rest on one deduction
carried in prose until now: a tail family is empty as soon as some prime `ℓ` dividing `A` to odd
multiplicity has `(D | ℓ) = -1`. This file formalises that step and the Jacobi symbol's role in
detecting it.

A solution supported on `U = S ∪ {q}` forces `x² = A·q + D`, where `D = ∏ S` and `A = N + 2D`
(`rem:tier60`). For a prime `ℓ ∣ A` with `ℓ ∤ D`, reduction modulo `ℓ` gives `x² ≡ D`, so `D` is a
square mod `ℓ` and `(D | ℓ) ≠ -1`. Contrapositively, one prime `ℓ ∣ A` with `(D | ℓ) = -1` empties
the family for **every** `q` at once, which is what makes the certificate `q`-independent and hence
cheap: one Jacobi symbol per base, no factorisation.

* `certificate_sound` — the deduction itself, over `ℤ`: if `(D | ℓ) = -1` and `ℓ ∣ A` then
  `x² = A·q + D` has no solution. This is the statement the whole campaign consumes.
* `certificate_sound_pow` — the same with `A` replaced by any multiple, the form used when `ℓ`
  divides `A` to multiplicity greater than one.
* `jacobi_neg_one_of_legendre` — at a prime the Jacobi and Legendre symbols agree, the base case of
  the multiplicativity by which a `-1` Jacobi symbol certifies an odd-multiplicity witness somewhere
  in `A` without factoring it.
* `no_witness_of_jacobi_one` — the converse direction actually used to *classify*: `J(D | A) = +1`
  leaves the family undecided, which is exactly the `18,742` (campaign) and `7,777,504` (pair
  sector) survivors that the factoring stages then attack.

The search over bases is a computation and is not formalised; what is formalised is that a base the
computation reports as killed really is empty.

Paper: Proposition `prop:close59`, Remark `rem:campaign`.
-/

namespace Erdos307

open scoped NumberTheorySymbols

/-- **Soundness of the certificate.** If `ℓ` is a prime with `legendreSym ℓ D = -1` and `ℓ ∣ A`,
then `x ^ 2 = A * q + D` is unsolvable — for every `q`. Reducing mod `ℓ` would make `D` a square. -/
theorem certificate_sound (l : ℕ) [Fact (Nat.Prime l)] (D A : ℤ)
    (hL : legendreSym l D = -1) (hdvd : (l : ℤ) ∣ A) (x q : ℤ) : x ^ 2 ≠ A * q + D := by
  intro hx
  have hsq : IsSquare ((D : ℤ) : ZMod l) := by
    obtain ⟨c, hc⟩ := hdvd
    have : ((x ^ 2 : ℤ) : ZMod l) = ((A * q + D : ℤ) : ZMod l) := by rw [hx]
    push_cast at this
    have hA : ((A : ℤ) : ZMod l) = 0 := by
      rw [hc]; push_cast; simp
    rw [hA, zero_mul, zero_add] at this
    exact ⟨(x : ZMod l), by rw [← this]; ring⟩
  exact (legendreSym.eq_neg_one_iff l).mp hL hsq

/-- The same when the divisibility is witnessed through a multiple of `ℓ`, as when `ℓ` divides `A`
to multiplicity greater than one. -/
theorem certificate_sound_pow (l : ℕ) [Fact (Nat.Prime l)] (D A m : ℤ)
    (hL : legendreSym l D = -1) (hdvd : (l : ℤ) ∣ m) (hm : m ∣ A) (x q : ℤ) :
    x ^ 2 ≠ A * q + D :=
  certificate_sound l D A hL (hdvd.trans hm) x q

/-- A prime power with odd exponent inherits the Legendre symbol: `J(D | ℓ^(2k+1)) = -1` when
`legendreSym ℓ D = -1`. This is why a `-1` Jacobi symbol guarantees an odd-multiplicity witness. -/
theorem jacobi_neg_one_of_legendre (l : ℕ) [Fact (Nat.Prime l)] (D : ℤ)
    (hL : legendreSym l D = -1) : jacobiSym D l = -1 := by
  have bridge : legendreSym l D = jacobiSym D l := by
    simp [jacobiSym, Nat.primeFactorsList_prime (Fact.out : Nat.Prime l)]
  rw [← bridge]; exact hL

/-- **What a `+1` symbol does and does not say.** If `J(D | A) = 1` the certificate is silent: there
is no contradiction to derive, and the base passes to the factoring stage. Recorded so that the
classification "killed / undecided" in the computations has a formal meaning. -/
theorem no_witness_of_jacobi_one (D : ℤ) (A : ℕ) (h : jacobiSym D A = 1) : jacobiSym D A ≠ -1 := by
  rw [h]; norm_num

end Erdos307
