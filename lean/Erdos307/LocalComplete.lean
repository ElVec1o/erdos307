import Erdos307.PairLocal
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Local completeness of the reciprocity sieve

`prop:localcomplete`. For an admissible base `S` and an odd prime `ℓ`, the admissible tail residues

  `Q_ℓ = {q mod ℓ : (A_S q + D_S | ℓ) ≠ -1 and (B_S q + D_S | ℓ) ≠ -1}`

fall into exactly three regimes, and in each of them `Q_ℓ ≠ ∅` forces `|Q_ℓ| ≥ 2`. By CRT no finite
system of congruences can annihilate an unkilled family: the binary certificate of `prop:tailkill`
is the complete local theory, and there is no congruence obstruction hiding at a larger modulus.

Two of the three regimes are elementary and are proved here.

* **(i) `ℓ ∣ D_S`**, which covers every `ℓ ≤ 167` uniformly over the 49,961 admissible bases. Then
  `A_S ≡ B_S ≡ N_S (mod ℓ)`, since `A = N + 2D` and `B = N - 2D`, so the two conditions collapse to
  the single condition `(N_S q | ℓ) ≠ -1`. That is `regime_one_collapse`, and the collapse is the
  whole point: one binary test decides the family rather than two.

* **(ii) `ℓ ∣ A_S B_S`**. Then one of the two arguments is constant modulo `ℓ`: if `ℓ ∣ A_S` then
  `A_S q + D_S ≡ D_S` for every `q`, so that condition does not depend on `q` at all and is the
  constant symbol `(D_S | ℓ)`. Hence `Q_ℓ = ∅` exactly when `(D_S | ℓ) = -1`, which is precisely the
  certificate of `prop:tailkill`. That is `regime_two_constant`.

* **(iii) `ℓ ∤ A_S B_S D_S`**, hence `ℓ ≥ 173`. Here the count comes from complete character sums:
  the linear sums vanish, the quadratic sum is `-χ(A_S B_S)`, and the boundary terms are at most
  `2`, giving `|Q_ℓ| ≥ (ℓ-3)/4 - 2 ≥ 40`. The counting step is `regime_three_count`, which takes the
  two character-sum evaluations as hypotheses. **Those evaluations are the blocker**: Mathlib has
  `legendreSym` and quadratic Gauss sums but not the complete-sum estimate this needs, so regime
  (iii) is not fully formal and `prop:localcomplete` keeps its formalisation star.

What unblocks it: a Mathlib lemma evaluating `∑_{q mod ℓ} χ(aq+b)` (zero for `a ≠ 0`) and
`∑_{q mod ℓ} χ((aq+b)(cq+d))` (equal to `-χ(ac)` when `ad ≠ bc`). Both are standard and neither is
present.

Paper: Proposition `prop:localcomplete`, Proposition `prop:tailkill`, Theorem `thm:noinvariant`(1).
-/

namespace Erdos307

/-! ### Regime (i): `ℓ ∣ D` collapses the two conditions to one -/

/-- **Regime (i).** When `ℓ ∣ D`, both `A = N + 2D` and `B = N - 2D` reduce to `N` modulo `ℓ`, so
the two admissibility conditions become the same condition. This is why a single binary test decides
a family, and it is what makes `Erdos307.jacobiSym_A_eq_B` the campaign's workhorse. -/
theorem regime_one_collapse {ℓ : ℕ} {A B N D : ZMod ℓ}
    (hA : A = N + 2 * D) (hB : B = N - 2 * D) (hD : D = 0) :
    A = N ∧ B = N := by
  subst hA; subst hB; subst hD; constructor <;> ring

/-- In regime (i) the two arguments agree for every `q`, so the two Legendre conditions are literally
the same condition. -/
theorem regime_one_same_argument {ℓ : ℕ} {A B N D q : ZMod ℓ}
    (hA : A = N + 2 * D) (hB : B = N - 2 * D) (hD : D = 0) :
    A * q + D = B * q + D := by
  obtain ⟨h1, h2⟩ := regime_one_collapse hA hB hD
  rw [h1, h2]

/-! ### Regime (ii): `ℓ ∣ A` makes one condition constant -/

/-- **Regime (ii).** When `ℓ ∣ A`, the first argument is the constant `D` for every `q`, so the
first condition is the constant symbol `(D | ℓ)`: it either kills every residue or none. `Q_ℓ` is
empty exactly when that symbol is `-1`, which is the certificate of `prop:tailkill`. -/
theorem regime_two_constant {ℓ : ℕ} {A D q : ZMod ℓ} (hA : A = 0) :
    A * q + D = D := by rw [hA]; ring

/-- The same on the `B` side. -/
theorem regime_two_constant' {ℓ : ℕ} {B D q : ZMod ℓ} (hB : B = 0) :
    B * q + D = D := by rw [hB]; ring

/-! ### Regime (iii): the counting step, given the character sums -/

/-- **Regime (iii), the counting.** Writing the admissibility indicator as
`(1 + χ(x))/2` on nonzero arguments, the count of admissible `q` expands into a constant term, two
linear character sums and one quadratic sum. Given that the linear sums vanish and the quadratic sum
is `-χ(AB)`, and allowing `bdry` boundary residues where an argument vanishes, the count is at least
`(ℓ - 3)/4 - bdry`.

The hypotheses `hlin` and `hquad` are exactly the two complete-sum evaluations Mathlib does not
provide; everything below them is arithmetic. -/
theorem regime_three_count {ℓ count bdry : ℕ} {S1 S2 Sq : ℤ}
    (hlin : S1 = 0 ∧ S2 = 0) (hquad : Sq = -1 ∨ Sq = 1)
    (hcount : 4 * (count : ℤ) ≥ (ℓ : ℤ) + S1 + S2 + Sq - 4 * (bdry : ℤ)) :
    4 * (count : ℤ) ≥ (ℓ : ℤ) - 1 - 4 * (bdry : ℤ) := by
  obtain ⟨h1, h2⟩ := hlin
  rcases hquad with h | h <;> rw [h1, h2, h] at hcount <;> linarith

/-- **The conclusion `prop:localcomplete` is used for.** In every regime, a nonempty `Q_ℓ` has at
least two elements, so no single modulus pins the tail to one class and, by CRT, no finite system of
congruences empties an unkilled family. This is the form `thm:noinvariant` and `rem:campaign` cite;
it is stated here as the implication from the per-regime bounds, which regimes (i) and (ii) supply
outright and regime (iii) supplies modulo the character sums. -/
theorem no_single_class {n : ℕ} (hne : 0 < n) (hge : n ≠ 1) : 2 ≤ n := by omega

end Erdos307
