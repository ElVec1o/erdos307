import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Kovič (2012), Proposition 18: the inference step, and what actually follows

Kovič, *The arithmetic derivative and antiderivative*, J. Integer Seq. 15 (2012), Article 12.3.8,
Proposition 18, treats the two-cycle `n' = m`, `m' = n` for squarefree `n = p₁⋯p_r`, `m = q₁⋯q_s`.
The proof opens with two correct pairs of bounds, which after substituting `n' = m` and `m' = n` read

  (A)  r·n/p_r < m < r·n/p₁,      (B)  s·m/q_s < n < s·m/q₁,

and then asserts "Hence: `p₁q_s < rs` and `q₁p_r < rs`". Those two are the load-bearing inequalities:
everything downstream (`p₁ < r`, `q₁ < s`, `2·max{p_r,q_s} < N²/4`, and hence `r + s ≥ 34`, the
conditional `≥ 57` and `≥ 110`, and `max{m,n} ≥ ∏_{i≤17} pᵢ ≈ 1.92·10²¹`) is deduced from them.

They do not follow. Multiplying two inequalities is sound only when the directions match, and

* upper × upper  (`m < r·n/p₁` with `n < s·m/q₁`)  gives  `p₁q₁ < rs`;
* lower × lower  (`r·n/p_r < m` with `s·m/q_s < n`)  gives  `rs < p_r q_s`.

`p₁q_s < rs` pairs an upper bound on `m` (carrying `p₁`) with a lower bound on `n` (carrying `q_s`),
and the directions do not compose. The structural reason it is not recoverable: writing
`σ(n) = n'/n`, the cycle says exactly `σ(n) ∈ (r/p_r, r/p₁)` and `σ(m) = 1/σ(n) ∈ (s/q_s, s/q₁)`,
i.e. `σ(n)` lies in the intersection `(r/p_r, r/p₁) ∩ (q₁/s, q_s/s)`. Nonemptiness of that
intersection is equivalent to the conjunction of the two valid consequences above and to nothing
else, whereas `p₁q_s < rs ⟺ q_s/s < r/p₁` compares the two *upper* endpoints — a relation
nonemptiness never constrains.

This file records three things.

* `kovic_valid` : the two consequences that do follow from (A) and (B).
* `kovic_step_invalid` : the inference `(A) ∧ (B) → p₁q_s < rs` is **not** valid, refuted by an
  explicit model with squarefree disjoint supports (`code/kovic_prop18_audit.gp`).
* `kovic_step_invalid'` : the same for the companion `q₁p_r < rs`.

Scope, stated precisely. What is refuted is the *inference*, not the *statement*: no two-cycle is
known, so no counterexample to `r + s ≥ 34` can be exhibited, and none is claimed. The conclusion is
unproven, not false — and it is in fact true, but as a corollary of the barrier of this note
(`|U| ≥ 60`), which is proved by a different route and does not depend on Proposition 18. The
consequence for the record is that the barrier is the first valid bound of its kind rather than an
improvement on a valid earlier one.

Paper: Theorem `thm:barrier`, Section `sec:prior`.
-/

namespace Erdos307.KovicProp18

/-- What does follow from Kovič's own bounds (A) and (B): `p₁q₁ < rs` and `rs < p_r q_s`. -/
theorem kovic_valid (n m r s p1 pr q1 qs : ℚ)
    (hn : 0 < n) (hm : 0 < m) (hr : 0 < r) (hs : 0 < s)
    (hp1 : 0 < p1) (hpr : 0 < pr) (hq1 : 0 < q1) (hqs : 0 < qs)
    (h1 : r * n / pr < m) (h2 : m < r * n / p1) (h3 : s * m / qs < n) (h4 : n < s * m / q1) :
    p1 * q1 < r * s ∧ r * s < pr * qs := by
  rw [div_lt_iff₀ hpr] at h1
  rw [lt_div_iff₀ hp1] at h2
  rw [div_lt_iff₀ hqs] at h3
  rw [lt_div_iff₀ hq1] at h4
  have hmn : (0 : ℚ) < m * n := mul_pos hm hn
  constructor
  · -- upper x upper : (m·p₁)(n·q₁) < (r·n)(s·m)
    have key : (m * p1) * (n * q1) < (r * n) * (s * m) :=
      mul_lt_mul'' h2 h4 (by positivity) (by positivity)
    have step : (p1 * q1) * (m * n) < (r * s) * (m * n) := by nlinarith [key]
    exact lt_of_mul_lt_mul_right step hmn.le
  · -- lower x lower : (r·n)(s·m) < (m·p_r)(n·q_s)
    have key : (r * n) * (s * m) < (m * pr) * (n * qs) :=
      mul_lt_mul'' h1 h3 (by positivity) (by positivity)
    have step : (r * s) * (m * n) < (pr * qs) * (m * n) := by nlinarith [key]
    exact lt_of_mul_lt_mul_right step hmn.le

/-- The step `(A) ∧ (B) ⟹ p₁q_s < rs` is not a valid inference. The witness is
`n = 2·5·13·37·53·73·79·89·97·101`, `m = 3·7·19·31·43·59·67·71·83·103`: squarefree, disjoint
supports, `r = s = 10`, and all four of Kovič's displayed inequalities hold, yet
`p₁q_s = 206 > 100 = rs`. -/
theorem kovic_step_invalid :
    ¬ (∀ n m r s p1 pr q1 qs : ℚ,
        0 < n → 0 < m → 2 ≤ r → 2 ≤ s → 0 < p1 → p1 < pr → 0 < q1 → q1 < qs →
        r * n / pr < m → m < r * n / p1 → s * m / qs < n → n < s * m / q1 →
        p1 * qs < r * s) := by
  intro h
  have := h 1281899600172230 1276155290481729 10 10 2 101 3 103
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-- The companion step `(A) ∧ (B) ⟹ q₁p_r < rs` fails on the same model: `q₁p_r = 303 > 100`. -/
theorem kovic_step_invalid' :
    ¬ (∀ n m r s p1 pr q1 qs : ℚ,
        0 < n → 0 < m → 2 ≤ r → 2 ≤ s → 0 < p1 → p1 < pr → 0 < q1 → q1 < qs →
        r * n / pr < m → m < r * n / p1 → s * m / qs < n → n < s * m / q1 →
        q1 * pr < r * s) := by
  intro h
  have := h 1281899600172230 1276155290481729 10 10 2 101 3 103
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

end Erdos307.KovicProp18
