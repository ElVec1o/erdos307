import Erdos307.CompleteSums
import Erdos307

/-!
# Non-vacuity witnesses

`#print axioms` cannot see whether a theorem's hypotheses are satisfiable. A theorem with
contradictory hypotheses proves everything, reports the three standard axioms, and passes
`Check.lean` cleanly. One did: `sum_char_twist_inv_eq_zero` carried `∀ g, χ g * χ g = 1` together
with `χ t = 0`, which force `1 = 0`, so the target ring was trivial and the statement proved the sum
equals anything at all. It was caught by adversarial review, not by any check in this repository.

This file closes that hole for the theorems most exposed to it. For each, a **witness**: a concrete
instantiation in which every hypothesis is discharged. If the file compiles, those hypotheses are
satisfiable, so the theorems are not vacuous. That is the exact converse of the failure above, and
it is a proof rather than a heuristic.

Coverage is deliberately partial and the criterion is stated: a theorem is witnessed here if its
hypotheses are numerous or could plausibly conflict, in particular if they mix an equation to `0`
with a unit or invertibility assumption, which is the shape that failed. Theorems whose hypotheses
are a single positivity or membership condition are omitted.

One witness is worth reading on its own account. `two_roots_quadratic` is stated over an arbitrary
field, and over `ℚ` or `ℝ` its hypotheses are **unsatisfiable**: `2s² + 1 = 0` has no real solution.
Read at those fields it is a vacuous theorem. It has content only in characteristic where `-1/2` is
a square, and the witness below is `ZMod 11`, where `s = 4` works since `2·16 + 1 = 33 ≡ 0`.
-/

namespace Erdos307.Vacuity

open Erdos307

/-! Each witness instantiates a theorem at a concrete model and discharges **every** hypothesis.
If it elaborates, those hypotheses are jointly satisfiable. The `True` conclusion is deliberate:
what is being tested is the hypotheses, not the conclusion. -/

example : True := by
  have := sum_char_twist_inv (G := Multiplicative (ZMod 2)) (M := ℚ) 1
    (fun _ => by norm_num) (fun _ => (1 : ℚ)) 1
  trivial

example : True := by
  have := quadratic_inv (G := Multiplicative (ZMod 2)) (M := ℚ) 1 (fun _ => by norm_num) 1
  trivial

/-- **The witness that matters.** Over `ℚ` or `ℝ` the hypothesis `2s² + 1 = 0` is *unsatisfiable*,
so at those fields `two_roots_quadratic` is vacuous. It has content only where `-1/2` is a square:
in `ZMod 11`, `s = 4` gives `2·16 + 1 = 33 ≡ 0`. -/
example : True := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have := two_roots_quadratic (F := ZMod 11) (s₀ := 4) (s := 4) (by decide +revert) (by decide +revert) (by decide +revert)
  trivial

example : True := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have := two_roots (F := ZMod 11) (c := 9) (s₀ := 3) (s := 3) (by decide +revert) (by decide +revert)
  trivial

example : True := by
  have := regime_one_second (ℓ := 7) (B := 3) (D := 0) (N := 3) (α := 5)
    (by decide) (by decide) (by decide)
  trivial

example : True := by
  have := collapse_identity (A := 6) (B := 2) (D := 1) (m := 0) (u := 1) (x := 1) (y := 1)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := frame_cycle (M := 1) (N := 1) (Md := 0) (Nd := 0) (p := 1) (q := 1) (Δ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := frame_solve (M := 1) (N := 1) (Md := 0) (Nd := 0) (p := 1) (q := 1) (Δ := 1)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := eps_eq_zero_of_identity (AP := 1) (AQ := 1) (eP := 0) (eQ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := cycle_bound_max (a := 1) (x := 1) (y := 1) (sa := 1) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := oneprime_mass_bound (sM := 1) (sN := 1) (u := 0) (by norm_num) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := oneprime_mass_identity (M := 1) (N := 1) (Md := 0) (p := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := oneprime_forced (M := 1) (N := 1) (Md := 0) (Nd := 1) (p := 1)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := coprime_loss (l := 2) (e := 4) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := loss_antitone (x := 2) (y := 3) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := regime_one_collapse (ℓ := 7) (A := 3) (B := 3) (N := 3) (D := 0)
    (by decide) (by decide) (by decide)
  trivial

example : True := by
  have := regime_three_count (ℓ := 5) (count := 1) (bdry := 0) (S1 := 0) (S2 := 0) (Sq := -1)
    ⟨rfl, rfl⟩ (Or.inl rfl) (by norm_num)
  trivial

example : True := by
  have := mixed_member_mod16 (k := 1) (kd := 1) (Sk := 1) (b := 3) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := even_member_mod16 (k := 1) (kd := 1) (Sk := 1) (by norm_num) (by norm_num)
  trivial

example : True := by
  have := deg_drop_of_terms (d := 3) (dp := 1) (dterm := 2) (by norm_num) (by norm_num)
  trivial

/-- **The level barrier is not vacuous.** `admissible_extends` and `level_enumeration_terminates`
assume a finite set of primes of mass `> 2`, which is exactly the hypothesis the barrier says needs
`59` primes. The first `59` primes realise it: `∑_{i<59} 1/p_i = N59/P59 = 2.00235… > 2`. The image
of `range 59` under `Nat.nth Nat.Prime` is the witnessing `Finset`, and the sum transfers because
`Nat.nth Nat.Prime` is injective on an infinite predicate. -/
example : True := by
  have hinj : Function.Injective (Nat.nth Nat.Prime) :=
    Nat.nth_injective Nat.infinite_setOf_prime
  have hsum : ∑ p ∈ (Finset.range 59).image (Nat.nth Nat.Prime), (p : ℚ)⁻¹
      = (N59 : ℚ) / (P59 : ℚ) := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    exact sum_first59
  have h2 : (2 : ℚ) < ∑ p ∈ (Finset.range 59).image (Nat.nth Nat.Prime), (p : ℚ)⁻¹ := by
    rw [hsum]; unfold N59 P59; norm_num
  have := admissible_extends
    (U := (Finset.range 59).image (Nat.nth Nat.Prime))
    (fun p hp => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact Nat.prime_nth_prime i) h2 10
  trivial

/-- **A genuine Pythagorean pair.** `tail_finite` carries seven hypotheses including two square
conditions on the same `q`, which is exactly the shape that could conflict silently. The base
`D = 1`, `N = 7` (so `A = 9`, `B = 5`) with `q = 7` realises all of them: `9·7 + 1 = 64 = 8²` and
`5·7 + 1 = 36 = 6²`, with `x + y = 14 = 7·2` and `x - y = 2`. Its conclusion `q ≤ 4N` reads
`7 ≤ 28`, and this is the same base whose Pell orbit is stepped out in `code/tailbound.gp`, where
every later term is composite. -/
example : True := by
  have := tail_finite (D := 1) (N := 7) (q := 7) (m := 2) (c := 2) (x := 8) (y := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  trivial


/-! ### `prop:localcomplete`'s complete sums are not vacuous -/

/-- The hypotheses of `sum_quadraticChar_quadratic` are jointly satisfiable: `F = ZMod 5` has odd
characteristic, and `a = c = d = 1`, `b = 0` gives `a*d = 1 ≠ 0 = b*c`. So the evaluation
`∑_q χ((aq+b)(cq+d)) = -χ(ac)` is asserted about a nonempty set of data. -/
example : True := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hchar : ringChar (ZMod 5) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  have hne : (1 : ZMod 5) * 1 ≠ 0 * 1 := by norm_num
  have := Erdos307.sum_quadraticChar_quadratic (F := ZMod 5) hchar
    (a := 1) (b := 0) (c := 1) (d := 1) one_ne_zero one_ne_zero hne
  trivial

end Erdos307.Vacuity
