import Mathlib.Algebra.Group.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

/-!
# The congruential branch of `thm:noinvariant`

Branch (1) of `thm:noinvariant` concerns certificates of the second kind: a function `φ` whose
increment along `n ↦ n'` is a constant `c` in a finite group. Around a two-cycle the increment is
traversed twice, so such a `φ` forces `2c = 0`; a `φ` with `2c ≠ 0` would therefore preclude
two-cycles outright.

This file formalises that mechanism, in an arbitrary additive commutative group and for an arbitrary map, since
nothing arithmetic is involved in it:

* `two_nsmul_eq_zero_of_period_two` is the mechanism, `2c = 0`;
* `no_period_two_of_two_nsmul_ne_zero` is the certificate it would yield;
* `const_increment_iterate` records the general form `φ (D^[k] n) = φ n + k • c`, which is what makes
  the two-cycle case a special case of "the increment is traversed `k` times";
* `period_two_of_const_increment_of_ne` is the contrapositive used in the paper's phrasing.

What is *not* formalised here, and is stated at `PROVED` rather than `VERIFIED` in the paper, is the
emptiness of the class: that no such `φ` with `2c ≠ 0` exists for the arithmetic derivative. That
rests on `prop:localcomplete`, the solubility of the cycle system modulo every `m`, which is an
arithmetic input of the same kind as `thm:structure` in `Erdos307.HalfLyap` and the Atkin-Morain
certificate in `Erdos307.LyapFalse`. So this file closes the mechanism of branch (1) and cites its
emptiness, and the paper says which is which.

Nothing here decides \#307.

Paper: Theorem `thm:noinvariant` (1), Proposition `prop:localcomplete`.
-/

namespace Erdos307

variable {S : Type*} {A : Type*} [AddCommGroup A]

/-- If `φ` has constant increment `c` along `D`, then `φ (D^[k] n) = φ n + k • c`. -/
theorem const_increment_iterate (φ : S → A) (D : S → S) (c : A)
    (h : ∀ n, φ (D n) = φ n + c) (n : S) : ∀ k : ℕ, φ (D^[k] n) = φ n + k • c := by
  intro k
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih (D n), h n, succ_nsmul]
      abel

/-- **The mechanism of branch (1).** A point of period two forces `2c = 0`: the increment is
traversed twice and returns to where it started. -/
theorem two_nsmul_eq_zero_of_period_two (φ : S → A) (D : S → S) (c : A)
    (h : ∀ n, φ (D n) = φ n + c) {a : S} (ha : D (D a) = a) : (2 : ℕ) • c = 0 := by
  have h1 : φ (D (D a)) = φ a + (2 : ℕ) • c := by
    rw [h (D a), h a, two_nsmul]; abel
  rw [ha] at h1
  have : φ a + (2 : ℕ) • c = φ a + 0 := by rw [← h1]; abel
  exact (add_left_cancel this)

/-- **The certificate branch (1) would supply.** If some `φ` has constant increment `c` with
`2c ≠ 0`, then `D` has no point of period two. This is the implication the paper's dichotomy
records; `prop:localcomplete` is what makes its hypothesis unsatisfiable for the arithmetic
derivative, so the branch is empty rather than useful. -/
theorem no_period_two_of_two_nsmul_ne_zero (φ : S → A) (D : S → S) (c : A)
    (h : ∀ n, φ (D n) = φ n + c) (hc : (2 : ℕ) • c ≠ 0) (a : S) : D (D a) ≠ a := fun ha =>
  hc (two_nsmul_eq_zero_of_period_two φ D c h ha)

/-- Contrapositive form: if a point of period two exists, every constant increment satisfies
`2c = 0`, so no congruential certificate of this shape can exist. -/
theorem period_two_of_const_increment_of_ne (φ : S → A) (D : S → S) (c : A)
    (h : ∀ n, φ (D n) = φ n + c) {a : S} (ha : D (D a) = a) (hc : (2 : ℕ) • c ≠ 0) : False :=
  hc (two_nsmul_eq_zero_of_period_two φ D c h ha)

/-- The same statement in the concrete setting the paper uses, `A = ZMod m`. -/
theorem zmod_two_mul_eq_zero_of_period_two {m : ℕ} (φ : S → ZMod m) (D : S → S) (c : ZMod m)
    (h : ∀ n, φ (D n) = φ n + c) {a : S} (ha : D (D a) = a) : 2 * c = 0 := by
  have := two_nsmul_eq_zero_of_period_two φ D c h ha
  simpa [two_nsmul, two_mul] using this

end Erdos307
