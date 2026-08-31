import Mathlib.Tactic

/-!
# The barrier survives relaxing the cycle equations to divisibilities

A two-cycle requires `∏ Q = D(P)` and `∏ P = D(Q)` exactly. Replacing both equalities by
divisibilities, `∏ Q ∣ D(P)` and `∏ P ∣ D(Q)`, gives a strictly larger problem: it asks only that
each side's cofactor sum be a multiple of the other side's product. One might expect the mass
condition to be lost, since the mass came from `σ(P)σ(Q) = 1`.

It is not lost. Divisibility of positive integers gives `∏ Q ≤ D(P)` and `∏ P ≤ D(Q)`, and writing
`D(P) = σ(P)∏P`, `D(Q) = σ(Q)∏Q` and multiplying, the products cancel and leave
`σ(P)σ(Q) ≥ 1`. With the arithmetic--geometric mean inequality this gives `σ(P) + σ(Q) ≥ 2`, which
is the whole input to the level barrier. So `|P ∪ Q| ≥ 60` holds for the relaxed problem as well,
and the barrier is not an artefact of the exact equations.

Paper: Proposition `prop:divrelax`.
-/

namespace Erdos307

/-- **The mass condition follows from the divisibilities alone.** -/
theorem mass_prod_ge_one_of_le {pP pQ sP sQ : ℚ} (hP : 0 < pP) (hQ : 0 < pQ)
    (h1 : pQ ≤ sP * pP) (h2 : pP ≤ sQ * pQ) : 1 ≤ sP * sQ := by
  have hs : 0 < sP := by nlinarith
  have hmul : pP * pQ ≤ (sP * sQ) * (pP * pQ) := by nlinarith
  nlinarith [hmul, mul_pos hP hQ]

/-- **And hence the mass bound.** If the two reciprocal sums have product at least `1`, their sum is
at least `2`, which is the input the level barrier consumes. -/
theorem mass_sum_ge_two_of_prod {sP sQ : ℚ} (hP : 0 < sP) (hQ : 0 < sQ)
    (h : 1 ≤ sP * sQ) : 2 ≤ sP + sQ := by
  nlinarith [sq_nonneg (sP - sQ), h, hP, hQ]

/-- The relaxation in one statement: divisibility on both sides forces mass at least `2`. -/
theorem mass_from_divisibility {pP pQ sP sQ : ℚ} (hP : 0 < pP) (hQ : 0 < pQ)
    (hsP : 0 < sP) (hsQ : 0 < sQ) (h1 : pQ ≤ sP * pP) (h2 : pP ≤ sQ * pQ) :
    2 ≤ sP + sQ :=
  mass_sum_ge_two_of_prod hsP hsQ (mass_prod_ge_one_of_le hP hQ h1 h2)

end Erdos307
