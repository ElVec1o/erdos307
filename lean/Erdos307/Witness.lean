import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Field

/-!
# A certified witness for the approximation theorem

`prop:effapprox` exhibits disjoint sets of primes whose reciprocal-sum product approaches `1`.
The record certificate uses eleven ladder rungs and a `2010`-digit prime, whose primality is
established by APR-CL, a method absent from Mathlib. At three rungs the largest prime is
`2348039453`, inside the range `norm_num` certifies, so the statement is carried into Lean at
that depth: every primality, the disjointness and the rational arithmetic are machine-checked.

Paper: Proposition `prop:effapprox`.
-/

namespace Erdos307.Witness

/-- The small side, with reciprocal sum `31/30`. -/
def Qs : List ℕ := [2, 3, 5]

/-- The large side: the primes `7 ≤ p ≤ 271` together with the three ladder rungs
`431`, `66491` and `2348039453`. -/
def Ps : List ℕ :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
   103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
   431, 66491, 2348039453]

/-- The reciprocal sum of a list of primes. -/
def rsum (L : List ℕ) : ℚ := (L.map fun p : ℕ => (1 : ℚ) / (p : ℚ)).sum

theorem Qs_prime : ∀ q ∈ Qs, Nat.Prime q := by
  intro q hq
  fin_cases hq <;> norm_num

theorem Ps_prime : ∀ p ∈ Ps, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

theorem Ps_nodup : Ps.Nodup := by decide

theorem Qs_nodup : Qs.Nodup := by decide

theorem Ps_disjoint_Qs : ∀ p ∈ Ps, p ∉ Qs := by decide

theorem rsum_Qs : rsum Qs = 31 / 30 := by
  simp only [rsum, Qs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

theorem rsum_Ps : rsum Ps =
    687349750703635402094818785106836846239409685895674739557327313441845601663948188035799592093240455393350614697922150088640690 /
    710261409060423250330745274090291253742098878918290864117513250716336037700278700421339080059521754924854761463941156503656497 := by
  simp only [rsum, Ps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

/-- The witness for `prop:effapprox` at three rungs: two disjoint, repetition-free lists of
primes whose reciprocal-sum product lies within `10⁻¹⁷` of `1`. The exact defect is
`-2.1111 × 10⁻¹⁸`. -/
theorem effapprox_witness :
    ∃ P Q : List ℕ, P.Nodup ∧ Q.Nodup ∧ (∀ p ∈ P, Nat.Prime p) ∧ (∀ q ∈ Q, Nat.Prime q) ∧
      (∀ p ∈ P, p ∉ Q) ∧ |rsum P * rsum Q - 1| < 1 / 10 ^ 17 :=
  ⟨Ps, Qs, Ps_nodup, Qs_nodup, Ps_prime, Qs_prime, Ps_disjoint_Qs, by
    rw [rsum_Ps, rsum_Qs, abs_lt]
    constructor <;> norm_num⟩

end Erdos307.Witness
