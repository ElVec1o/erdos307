import Erdos307.Sixty

/-!
# The Frame Rule, and local anatomy

`thm:frame` and `lem:anatomy`.

## The Frame Rule

Let `M, N` be coprime squarefree with derivatives `M', N'`, and `Δ = MN - M'N'`. If

  `p = (MN' + N²)/Δ`  and  `q = (M'N + M²)/Δ`

are integers, both prime, each coprime to `MN`, with `p ≠ q`, then `a = Mp` and `b = Nq` form a
derivative two-cycle, so `(P, Q)` solves \#307. This is the constructive engine of the existence
side: it turns the search for a two-cycle into a search over *frames* `(M, N)` with two simultaneous
primality conditions, which is the shape every construction in the paper takes.

The algebra is exact and is proved here in full. With `p` prime and `p ∤ M`, Leibniz gives
`a' = M'p + M` (`csum_insert_prime`), and likewise `b' = N'q + N`; the cycle conditions `a' = b`,
`b' = a` are then the linear system

  `M'p + M = Nq`,   `N'q + N = Mp`,

whose unique solution is the displayed pair. `frame_cycle` verifies both equations from the two
divisibility hypotheses, and `frame_solve` runs the derivation the other way, showing the formulas
are forced rather than guessed: any `p, q` satisfying the cycle equations satisfy `Δp = MN' + N²`
and `Δq = M'N + M²`.

Nothing here produces a solution. It says exactly what a frame must satisfy, and the primality of
the two quotients is the part no algebra reaches; `prop:untestable` costs that part on the immune
families, and `rem:campaign` kills `93.0%` of the level-60 frames by reciprocity.

## Local anatomy

`lem:anatomy` is the companion statement at a single prime: for squarefree `a` and a prime `q ∤ a`,

  `q ∣ a'  ⟺  ∑_{p ∣ a} p⁻¹ ≡ 0 (mod q)`,

while `q ∣ a` forces `q ∤ a'`. The second half is Rigidity, already available as
`padic_lowers_on_support`; the first is `anatomy_iff` below, and it is what makes the cycle equation
factor, prime by prime, into `ω(a) + ω(b)` local congruences of exactly the shape that governs
amicable-pair heuristics.

The forcing criterion is correct and, as `rem:descent` records, dead as a search tool: the
congruences are independent, so the density of simultaneous solutions is `1/∏Q ≈ 10⁻⁵⁷`. It is alive
only as a construction tool, which is how the Frame Rule uses it.

Paper: Theorem `thm:frame`, Lemma `lem:anatomy`.
-/

namespace Erdos307

open Finset

/-! ### Leibniz for one adjoined prime -/

/-- **Leibniz, slot form.** Adjoining a prime `p` outside the support `S` sends `M = ∏S` to `Mp` and
`M' = csum S` to `M'p + M`. This is the step the Frame Rule and the slot calculus both run on. -/
theorem csum_insert_prime {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) (hp0 : 0 < p) :
    csum (S ∪ {p}) = p * csum S + dprod S := by
  have hdisj : Disjoint S ({p} : Finset ℕ) := by
    simpa [Finset.disjoint_singleton_right] using hp
  rw [csum_union_eq hdisj]
  have h1 : dprod ({p} : Finset ℕ) = p := by simp [dprod]
  have h2 : csum ({p} : Finset ℕ) = 1 := by simp [csum, dprod, Nat.div_self hp0]
  rw [h1, h2, mul_one]

/-- The product side of the same step. -/
theorem dprod_insert_prime {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) :
    dprod (S ∪ {p}) = dprod S * p := by
  have hdisj : Disjoint S ({p} : Finset ℕ) := by
    simpa [Finset.disjoint_singleton_right] using hp
  rw [dprod, Finset.prod_union hdisj]
  simp [dprod]

/-! ### The Frame Rule -/

/-- **`thm:frame`.** If the two frame quotients are integers, that is if `Δp = MN' + N²` and
`Δq = M'N + M²`, then `a = Mp` and `b = Nq` satisfy the cycle equations `a' = b` and `b' = a`.

Both are exact identities in `ℤ`, given `Δ = MN - M'N'`; no positivity, primality or coprimality is
used at this step. Those hypotheses are what make `a` and `b` squarefree with the stated derivatives,
which is the content of `csum_insert_prime`. -/
theorem frame_cycle {M N Md Nd p q Δ : ℤ}
    (hΔ : Δ = M * N - Md * Nd)
    (hp : Δ * p = M * Nd + N ^ 2)
    (hq : Δ * q = Md * N + M ^ 2)
    (hΔ0 : Δ ≠ 0) :
    Md * p + M = N * q ∧ Nd * q + N = M * p := by
  constructor
  · have h : Δ * (Md * p + M) = Δ * (N * q) := by
      rw [show Δ * (Md * p + M) = Md * (Δ * p) + Δ * M by ring, hp,
          show Δ * (N * q) = N * (Δ * q) by ring, hq, hΔ]
      ring
    exact mul_left_cancel₀ hΔ0 h
  · have h : Δ * (Nd * q + N) = Δ * (M * p) := by
      rw [show Δ * (Nd * q + N) = Nd * (Δ * q) + Δ * N by ring, hq,
          show Δ * (M * p) = M * (Δ * p) by ring, hp, hΔ]
      ring
    exact mul_left_cancel₀ hΔ0 h

/-- **The formulas are forced, not guessed.** Conversely, any `p, q` satisfying the two cycle
equations satisfy `Δp = MN' + N²` and `Δq = M'N + M²`. So the Frame Rule is an equivalence: a frame
admits a two-cycle exactly when its two quotients are integers, and then they are these. -/
theorem frame_solve {M N Md Nd p q Δ : ℤ}
    (hΔ : Δ = M * N - Md * Nd)
    (h1 : Md * p + M = N * q) (h2 : Nd * q + N = M * p) :
    Δ * p = M * Nd + N ^ 2 ∧ Δ * q = Md * N + M ^ 2 := by
  subst hΔ
  constructor
  · linear_combination -Nd * h1 - N * h2
  · linear_combination -M * h1 - Md * h2

/-! ### Local anatomy -/

/-- **`lem:anatomy`, the second half.** If `q` divides `a` then `q` does not divide `a'`. This is
Rigidity, and it is why the forcing criterion has content only off the support. -/
theorem anatomy_on_support {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℕ} (hq : q ∈ S) :
    ¬ q ∣ csum S := by
  intro hdvd
  have hg : Nat.gcd (csum S) (dprod S) = 1 := rigidity_coprime S hS
  have hqd : q ∣ dprod S := Finset.dvd_prod_of_mem _ hq
  have h1 : q ∣ 1 := by rw [← hg]; exact Nat.dvd_gcd hdvd hqd
  exact absurd (Nat.eq_one_of_dvd_one h1) (hS q hq).one_lt.ne'

/-- `a' = a · ∑_{p ∣ a} 1/p` read modulo `q`. For `q` prime not dividing `a = ∏S`, every `p ∈ S` is
a unit modulo `q`, so the cofactor `a/p` is `a · p⁻¹` there and the sum defining `a'` factors. -/
theorem csum_eq_mul_recipSum {S : Finset ℕ} {q : ℕ} [Fact q.Prime] (hq : ¬ q ∣ dprod S) :
    ((csum S : ℕ) : ZMod q)
      = ((dprod S : ℕ) : ZMod q) * ∑ p ∈ S, ((p : ℕ) : ZMod q)⁻¹ := by
  simp only [csum, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hdvd : p ∣ dprod S := Finset.dvd_prod_of_mem _ hp
  have hqp : ¬ q ∣ p := fun h => hq (h.trans hdvd)
  have hpu : ((p : ℕ) : ZMod q) ≠ 0 := fun h => hqp ((ZMod.natCast_eq_zero_iff p q).mp h)
  rw [eq_mul_inv_iff_mul_eq₀ hpu, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]

/-- **`lem:anatomy`, the forcing criterion.** For `q` a prime not dividing `a = ∏S`,

  `q ∣ a'  ⟺  ∑_{p ∈ S} p⁻¹ ≡ 0 (mod q)`.

The mechanism is `a' = a · ∑_{p ∣ a} 1/p`: modulo `q` the factor `a` is a unit, so it cancels. This
is what makes the cycle equation factor, prime by prime, into `ω(a) + ω(b)` local congruences. -/
theorem anatomy_iff {S : Finset ℕ} {q : ℕ} [Fact q.Prime] (hq : ¬ q ∣ dprod S) :
    q ∣ csum S ↔ (∑ p ∈ S, ((p : ℕ) : ZMod q)⁻¹) = 0 := by
  rw [← ZMod.natCast_eq_zero_iff (csum S) q, csum_eq_mul_recipSum hq]
  have hDu : ((dprod S : ℕ) : ZMod q) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff _ q).mp h)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hDu
    · exact h0
  · intro h; rw [h, mul_zero]

end Erdos307
