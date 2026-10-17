import Mathlib.Tactic

/-!
# The same-side case of the level-61 height and split-balance corollaries

At level `61`, write `U = S ∪ {u, v}`, `S = P₀ ⊔ Q₀`, `M = ∏P₀`, `N = ∏Q₀` with derivatives `M'`, `N'`. The Frame Rule
treats the case where `u` and `v` lie on opposite sides. If both lie on the same side, `a = M u v`, `b = N`, then
`a' = b` and `b' = a` read `M' u v + M (u + v) = N` and `N' = M u v`. Eliminating `u v` gives
`M² (u + v) = M N - M' N' = Δ`, so `Δ > 0` as in the opposite-side case, and `u v = N'/M ≤ N'`.

Paper: Corollary `cor:level61height`, Corollary `cor:splitbalance` (same-side case).
-/

namespace Erdos307

/-- `M² (u + v) = M N - M' N'` for a same-side pair of new primes. -/
theorem same_side_delta {M N M' N' u v : ℤ} (h1 : M' * u * v + M * (u + v) = N)
    (h2 : N' = M * u * v) : M ^ 2 * (u + v) = M * N - M' * N' := by
  subst h2
  linear_combination M * h1

/-- Hence `Δ = M N - M' N' > 0`: the split of the base has `σ(P₀) σ(Q₀) < 1`, exactly as for opposite sides. -/
theorem same_side_delta_pos {M N M' N' u v : ℤ} (hM : M ≠ 0) (huv : 0 < u + v)
    (h1 : M' * u * v + M * (u + v) = N) (h2 : N' = M * u * v) : 0 < M * N - M' * N' := by
  rw [← same_side_delta h1 h2]
  positivity

/-- The product of the two new primes: `u v = N'/M`, so `M u v = N'`. -/
theorem same_side_prod {M N' u v : ℤ} (h2 : N' = M * u * v) : M * (u * v) = N' := by
  rw [h2]; ring

end Erdos307
