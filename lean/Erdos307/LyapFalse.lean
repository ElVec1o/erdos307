import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Lyapunov criterion fails, for every `λ`

`thm:lyapfalse`. The criterion behind `def:lyap` is

  `(∗)   log σ(n) < λ (σ(n) - σ(n'))`,

asked to hold at every squarefree `n` with `n'` squarefree. It holds at no real `λ`.

The reason is a sign clash, not an estimate. If `σ(n) > 1` then the left side of `(∗)` is positive,
so `(∗)` needs `σ(n) - σ(n')` to have the sign of `λ`. Two witnesses with `σ(n) > 1` and opposite
values of `sign (σ(n) - σ(n'))` therefore exclude every `λ` between them:

* `n₀`, the product of the 68 primes in `[7,373]` other than `307, 317, 359`, has
  `σ(n₀) = 1.0059067…` and `n₀' = 2·3·5·C` with `C` a 141-digit prime, so `σ(n₀') = 31/30` exactly
  and `σ(n₀') > σ(n₀)`. This kills every `λ > 0`.
* `n = 30` has `σ(30) = 31/30 > 1` and `30' = 31`, so `σ(31) = 1/31 < σ(30)`. This kills every
  `λ ≤ 0`.

As in `Erdos307.HalfLyap`, the arithmetic enters only through the values of `σ`, and those are
recorded here as explicit numerals and checked by `norm_num`. That `n₀'` is squarefree with
`σ(n₀') = 31/30` rests on the complete factorisation `n₀' = 2·3·5·C` together with the primality of
`C`, which carries an Atkin-Morain certificate (`data/certs/lyap_refute_cofactor_ecpp.txt`); that step is
outside Lean and is the only input taken on trust, exactly as the coprimality of `n` and `n'` is in
`HalfLyap`.

Trust boundary. `sigmaN0` is the mass of the witness as an explicit rational numeral, and the Lean
development proves the criterion fails for that numeral. It does **not** prove that the numeral is
the mass of the integer `n₀` of the paper: the factorisation of `n₀` and the primality of the
141-digit cofactor are external, resting on the ECPP certificate in
`data/certs/lyap_refute_cofactor_ecpp.txt`. So the refutation is Lean-checked modulo that identification,
which is stated here rather than left implicit.

Paper: Theorem `thm:lyapfalse`, Corollary `cor:halfsharp`.
-/

namespace Erdos307

open Real

/-- If `σ(n) > 1` and `σ(n') > σ(n)`, the criterion `(∗)` fails at `n` for every `λ > 0`: the left
side is positive and the right side negative. -/
theorem criterion_fails_of_pos {s t l : ℝ} (hs : 1 < s) (hst : s < t) (hl : 0 < l) :
    ¬ (Real.log s < l * (s - t)) := by
  have hlog : 0 < Real.log s := Real.log_pos hs
  have hneg : l * (s - t) < 0 := mul_neg_of_pos_of_neg hl (by linarith)
  intro h
  linarith

/-- If `σ(n) > 1` and `σ(n') < σ(n)`, the criterion `(∗)` fails at `n` for every `λ ≤ 0`. -/
theorem criterion_fails_of_nonpos {s t l : ℝ} (hs : 1 < s) (hts : t < s) (hl : l ≤ 0) :
    ¬ (Real.log s < l * (s - t)) := by
  have hlog : 0 < Real.log s := Real.log_pos hs
  have hnonpos : l * (s - t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hl (by linarith)
  intro h
  linarith

/-- **`thm:lyapfalse`, abstract form.** Given one pair `(s₁,t₁)` with `1 < s₁ < t₁` and one pair
`(s₂,t₂)` with `t₂ < s₂` and `1 < s₂`, no real `l` satisfies `(∗)` at both. -/
theorem no_lambda_works {s₁ t₁ s₂ t₂ : ℝ}
    (h₁ : 1 < s₁) (h₁' : s₁ < t₁) (h₂ : 1 < s₂) (h₂' : t₂ < s₂) (l : ℝ) :
    ¬ (Real.log s₁ < l * (s₁ - t₁)) ∨ ¬ (Real.log s₂ < l * (s₂ - t₂)) := by
  by_cases hl : l ≤ 0
  · exact Or.inr (criterion_fails_of_nonpos h₂ h₂' hl)
  · exact Or.inl (criterion_fails_of_pos h₁ h₁' (not_le.mp hl))

/-- `σ(n₀)`, as the exact rational `n₀'/n₀`. Rigidity (`Erdos307.rigidity_coprime`) says this
fraction is already in lowest terms. -/
noncomputable def sigmaN0 : ℝ :=
  (4354493676456078977058863165495370908941600892585379287805606921544072921522551996550023216514253822412944176362060502404014288483030972240430 : ℝ) /
  (4328924019279857013247696090462199271976136469738523984364337896728797474579627479542596604613438696652961348543163359815017036676161358852643 : ℝ)

theorem one_lt_sigmaN0 : 1 < sigmaN0 := by
  unfold sigmaN0; norm_num

/-- `σ(n₀) < σ(n₀') = 31/30`, the inequality that makes the right side of `(∗)` negative. -/
theorem sigmaN0_lt : sigmaN0 < 31 / 30 := by
  unfold sigmaN0; norm_num

/-- **`thm:lyapfalse`.** With `s₁ = σ(n₀)`, `t₁ = σ(n₀') = 31/30` and the pair `(31/30, 1/31)`
coming from `n = 30`, no real `l` satisfies `(∗)` at both points. -/
theorem lyapunov_criterion_false (l : ℝ) :
    ¬ (Real.log sigmaN0 < l * (sigmaN0 - 31 / 30)) ∨
    ¬ (Real.log (31 / 30 : ℝ) < l * ((31 / 30 : ℝ) - 1 / 31)) :=
  no_lambda_works one_lt_sigmaN0 sigmaN0_lt (by norm_num) (by norm_num) l

end Erdos307
