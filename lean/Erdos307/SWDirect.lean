import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The diagonalisation core of `lem:swdirect`

`lem:swdirect` derives the pretentious distance bound `M ≥ (1 - |ĝ₀|)·L - o(L)`, uniformly for
`r ≤ (log N)^A`, by applying Siegel–Walfisz in each residue class rather than expanding in
characters. Its analytic inputs (Siegel–Walfisz, hence Siegel) are not in Mathlib and are recorded
as the blocker in `COVERAGE.md`. What the analysis actually delivers is a *family* of bounds, one
per `ε > 0`, each with its own ineffective constant; converting that family into a single `o(L)`
statement is a separate, purely arithmetic step, and it is that step which is formalised here.

The paper takes `ε_j = 1/(2j)` and `B_j = 2Aj`, both fixed, so the Siegel–Walfisz constant `C_j` is
a constant for each `j`. The two facts needed are:

* `diagonalisation_step` — the exchange `(1 - 1/(2j))(1-G)L - C ≥ (1-G)L - L/j`, valid as soon as
  `L ≥ 2jC`. The paper states the equivalence `⟺ (L/(2j))(1+G) ≥ C`; both directions are proved.
* `diagonalisation_sufficient` — that `L ≥ 2jC` suffices, given `G ≥ 0` and `C ≥ 0`. This is where
  the threshold `N_j` is enlarged. The hypothesis `C ≥ 0` is not cosmetic: for negative `C` the
  exchange genuinely fails, since `L/(2j)` would then be allowed to be negative and multiplying by
  `1 + G ≥ 1` moves it the wrong way. Siegel–Walfisz supplies a positive constant.
* `diagonalisation_limit` — the passage to the limit: if for every `j ≥ 1` the bound
  `M ≥ (1-G)L - L/j` holds once `L ≥ f j`, then `M ≥ (1-G)L - δ·L` for every `δ > 0`, which is the
  `o(L)` of the statement.

Nothing here uses any property of `M`, `L` or `G` beyond the inequalities, which is the point: the
diagonalisation is independent of the analysis it is applied to, and would serve any family of
`ε`-dependent bounds with ineffective constants.

Paper: Lemma `lem:swdirect` (the *Removing ε* paragraph of its proof).
-/

namespace Erdos307

/-- **The exchange, as an equivalence.** For `j ≥ 1`, dropping the factor `1 - 1/(2j)` in favour of
an additive `L/j` is legitimate exactly when `(L/(2j))(1+G) ≥ C`. -/
theorem diagonalisation_iff {L G C : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    (1 - 1 / (2 * j)) * ((1 - G) * L) - C ≥ (1 - G) * L - L / j ↔ L / (2 * j) * (1 + G) ≥ C := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  constructor <;> intro h <;>
    · field_simp at h ⊢
      nlinarith [h, hjpos]

/-- **The sufficient condition.** With `G ≥ 0` and `L ≥ 2jC`, the exchange goes through: the
threshold `N_j` is enlarged until `L` is this large. -/
theorem diagonalisation_sufficient {L G C : ℝ} {j : ℕ} (hj : 1 ≤ j) (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hL : L ≥ 2 * j * C) : L / (2 * j) * (1 + G) ≥ C := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have h2j : (0 : ℝ) < 2 * j := by linarith
  have hdiv : L / (2 * j) ≥ C := by
    rw [ge_iff_le, le_div_iff₀ h2j]
    nlinarith [hL, mul_comm C (2 * (j : ℝ))]
  nlinarith [hdiv, hG, hC, mul_nonneg (le_trans hC hdiv) hG]

/-- **The exchange itself**, assembled: for `j ≥ 1`, `G ≥ 0` and `L ≥ 2jC`. -/
theorem diagonalisation_step {L G C : ℝ} {j : ℕ} (hj : 1 ≤ j) (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hL : L ≥ 2 * j * C) :
    (1 - 1 / (2 * j)) * ((1 - G) * L) - C ≥ (1 - G) * L - L / j :=
  (diagonalisation_iff hj).mpr (diagonalisation_sufficient hj hG hC hL)

/-- **Passage to the limit.** If for every `j ≥ 1` the bound `M ≥ (1-G)L - L/j` holds once `L` is
past a threshold `f j`, then for every `δ > 0` one has `M ≥ (1-G)L - δL` for all large `L`: this is
the `o(L)` error of `lem:swdirect`. The threshold is `max (f j) 0` with `j` any index exceeding
`1/δ`, which exists by the archimedean property. -/
theorem diagonalisation_limit {M G : ℝ} {f : ℕ → ℝ}
    (h : ∀ j : ℕ, 1 ≤ j → ∀ L : ℝ, L ≥ f j → M ≥ (1 - G) * L - L / j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ j : ℕ, 1 ≤ j ∧ ∀ L : ℝ, 0 ≤ L → L ≥ f j → M ≥ (1 - G) * L - δ * L := by
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / δ)
  refine ⟨max j 1, le_max_right _ _, fun L hL0 hLf => ?_⟩
  have hj1 : 1 ≤ max j 1 := le_max_right _ _
  have hbound := h (max j 1) hj1 L hLf
  have hjpos : (0 : ℝ) < (max j 1 : ℕ) := by exact_mod_cast hj1
  have hle : L / (max j 1 : ℕ) ≤ δ * L := by
    rw [div_le_iff₀ hjpos]
    have : (1 : ℝ) / δ < (max j 1 : ℕ) := by
      refine lt_of_lt_of_le hj ?_
      exact_mod_cast Nat.cast_le.mpr (le_max_left j 1)
    have hd : 1 < δ * (max j 1 : ℕ) := by
      rw [div_lt_iff₀ hδ] at this; linarith [this]
    nlinarith [hL0, hd]
  linarith [hbound, hle]

end Erdos307
