import Erdos307.Frame
import Erdos307.Pythagorean

/-!
# Normal forms: no free slot, one prime, the slot calculus, and two local filters

`prop:nofreeslot`, `prop:oneprime`, `prop:slot`, `cor:qr`, `prop:noconj`.

These are the statements that pin down how much freedom the existence route actually has. The answer
is: one parameter, then one primality condition.

* **`prop:nofreeslot`.** If `σ(P)σ(Q) = 1` then `b = a'` and `a = b'` *exactly*, so `Q` is
  determined by `P`: it is the set of prime factors of `a'`. The equation content is
  `solution_structure`; what is added here is the determinacy, `Q_determined`, which is what makes
  `cor:noslack` true, that no relaxation lets two primes of `Q` be chosen freely.

* **`prop:oneprime`.** The problem has a one-prime normal form: a solution exists iff there are
  squarefree `M, N` with `MN - M'N' = M²` and `p := N'/M` prime not dividing `M`. Then
  `N = M + M'p` is forced (`oneprime_forced`) and `a = Mp`, `b = N` is a cycle
  (`oneprime_cycle`). The problem splits into an *exactness* layer, a Diophantine equation, and a
  single *primality* layer, one prime value of a determined quantity. Part (b), that the exactness
  layer alone carries the full barrier, is `oneprime_mass_identity` together with
  `oneprime_mass_bound`: the identity `(σ(M) + 1/p)σ(N) = 1` holds for every witness, prime or not,
  so AM-GM gives `σ(M) + σ(N) ≥ 2 - 1/p` whether or not `p` is prime.

* **`prop:slot`.** The slot calculus, `N' + 2N = rE₀ + N₀` and `N' - 2N = r(N₀' - 2N₀) + N₀` for
  `N = N₀r`. Two ring identities from Leibniz, and the engine underneath `prop:strata`,
  `prop:liveslot` and the census: a plus-hit is exactly `r = (s² - N₀)/E₀`, so the whole layer is a
  congruence `s² ≡ N₀ (mod E₀)` rather than a search.

* **`cor:qr`.** Every `ℓ ∈ P ∪ Q` has `(N/ℓ ∣ ℓ) = +1`. Since `ℓ` divides exactly one of `a, b`, it
  does not divide `a + b`, and `N/ℓ ≡ N' + 2N = (a+b)²` is a nonzero square. The filter is
  split-free, which is its one advantage over Bado's linear congruence; squaring is lossy, so Bado's
  is strictly stronger.

* **`prop:noconj`.** Reducing a Leibniz derivative modulo one of its own primes kills every term but
  one, so the result is a unit times a nonzero cofactor. `dvd_sum_erase_iff` is that mechanism in
  general form, and it is the same mechanism that proves Rigidity and `lem:anatomy`; isolating it
  once makes all three instances one lemma.

Paper: Proposition `prop:nofreeslot`, Corollary `cor:noslack`, Proposition `prop:oneprime`,
Proposition `prop:slot`, Corollary `cor:qr`, Proposition `prop:noconj`.
-/

namespace Erdos307

open Finset

/-! ### `prop:noconj`: reduction modulo one prime of the support -/

/-- **The mechanism behind Rigidity, `lem:anatomy` and `prop:noconj` alike.** If `π` divides every
term of a sum but one, and not that one, it does not divide the sum.

For `prop:noconj`: reducing `D(a) = ∑ᵢ uᵢ(a/πᵢ)` modulo a prime `π = π_j` of the support kills every
term but the one at `j`, leaving `u_π(a/π)`, a unit times a cofactor `π` does not divide. So no two
prime factors of a twisted cycle are conjugate, and a twisted cycle's support is never
conjugation-stable. -/
theorem dvd_sum_erase_iff {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → R) (π : R) {j : ι} (hj : j ∈ s)
    (hother : ∀ i ∈ s.erase j, π ∣ g i) (hjj : ¬ π ∣ g j) :
    ¬ π ∣ ∑ i ∈ s, g i := by
  intro h
  refine hjj ?_
  have hsplit : ∑ i ∈ s, g i = g j + ∑ i ∈ s.erase j, g i := (Finset.add_sum_erase s g hj).symm
  have hrest : π ∣ ∑ i ∈ s.erase j, g i := Finset.dvd_sum hother
  have hgj : g j = (∑ i ∈ s, g i) - ∑ i ∈ s.erase j, g i := by rw [hsplit]; ring
  rw [hgj]
  exact dvd_sub h hrest

/-! ### `prop:nofreeslot`: the route carries one parameter -/

/-- **`prop:nofreeslot`.** `Q` is determined by `P`: given the cycle equation `a' = b`, the set `Q`
is exactly the set of prime factors of `a'`. So the existence route has one parameter, the set `P`,
and `cor:noslack` follows: there is no relaxation in which two primes of `Q` are free. -/
theorem Q_determined {P Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (h1 : csum P = dprod Q) :
    Q = (csum P).primeFactors := by
  rw [h1, dprod]
  exact (Nat.primeFactors_prod hQ).symm

/-! ### `prop:oneprime`: the one-prime normal form -/

/-- **`prop:oneprime`(a), the forced shape.** The exactness equation `MN - M'N' = M²` together with
`N' = Mp` forces `N = M + M'p`. -/
theorem oneprime_forced {M N Md Nd p : ℤ} (hM0 : M ≠ 0)
    (heq : M * N - Md * Nd = M ^ 2) (hp : Nd = M * p) :
    N = M + Md * p := by
  have h : M * (N - (M + Md * p)) = 0 := by rw [hp] at heq; linear_combination heq
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hM0
  · linarith

/-- **`prop:oneprime`(a), the cycle.** With `N = M + M'p` and `N' = Mp`, the pair `a = Mp`, `b = N`
satisfies `a' = M'p + M = N = b` and `b' = N' = Mp = a`. Coprimality and `a ≠ b` are automatic and
are not needed for the two equations. -/
theorem oneprime_cycle {M N Md Nd p : ℤ}
    (hN : N = M + Md * p) (hp : Nd = M * p) :
    Md * p + M = N ∧ Nd = M * p := ⟨by rw [hN]; ring, hp⟩

/-- **`prop:oneprime`(b), the identity.** `(σ(M) + 1/p)·σ(N) = 1` holds for *every* witness, whether
or not `p` is prime, since `σ(M) = M'/M`, `σ(N) = N'/N = Mp/N` and `N = M'p + M`. This is why the
exactness layer alone carries the full barrier. -/
theorem oneprime_mass_identity {M N Md p : ℚ} (hM0 : M ≠ 0) (hp0 : p ≠ 0) (hN0 : N ≠ 0)
    (hN : N = M + Md * p) :
    (Md / M + 1 / p) * ((M * p) / N) = 1 := by
  subst hN
  field_simp
  ring

/-- **`prop:oneprime`(b), the bound.** Hence by AM-GM `σ(M) + σ(N) ≥ 2 - 1/p`, so a relaxed witness,
one whose `p` is composite, is subject to the same mass barrier as a genuine solution. -/
theorem oneprime_mass_bound {sM sN u : ℝ} (hsM : 0 < sM + u) (hsN : 0 < sN)
    (h : (sM + u) * sN = 1) : 2 - u ≤ sM + sN := by
  have := two_le_sum_of_mul_eq_one hsM hsN h
  linarith

/-! ### `prop:slot`: the slot calculus -/

/-- **`prop:slot`.** For `N = N₀r` with `N' = N₀'r + N₀` (Leibniz), the two discriminant layers are
`N' + 2N = rE₀ + N₀` and `N' - 2N = r(N₀' - 2N₀) + N₀`, where `E₀ = N₀' + 2N₀`. Two ring identities,
and the engine underneath the whole plus-layer analysis. -/
theorem slot_layers (N0 N0d r : ℤ) :
    (N0d * r + N0) + 2 * (N0 * r) = r * (N0d + 2 * N0) + N0 ∧
    (N0d * r + N0) - 2 * (N0 * r) = r * (N0d - 2 * N0) + N0 := by
  constructor <;> ring

/-- **The slot recovery.** A plus-hit is exactly `r = (s² - N₀)/E₀`: the layer is a congruence
`s² ≡ N₀ (mod E₀)`, not a search. This is what `prop:strata`, `prop:liveslot` and the census all
run on. -/
theorem slot_recovery {N0 E0 r s : ℤ} (hE0 : E0 ≠ 0) (h : r * E0 + N0 = s ^ 2) :
    r = (s ^ 2 - N0) / E0 := by
  have : r * E0 = s ^ 2 - N0 := by linarith
  rw [← this, Int.mul_ediv_cancel _ hE0]

/-! ### `cor:qr`: the quadratic-residue filter -/

/-- **`cor:qr`.** For `ℓ ∈ P ∪ Q`, the cofactor `N/ℓ` is a nonzero quadratic residue modulo `ℓ`.
Since `P` and `Q` are disjoint, `ℓ` divides exactly one of `a, b`, so `ℓ ∤ a + b`; combined with
`N/ℓ ≡ N' + 2N = (a+b)²` this makes `N/ℓ` a nonzero square.

The filter is *split-free*: the residue is computable from the candidate union alone, with no
knowledge of the `P` / `Q` partition. That is its one advantage over Bado's linear congruence, which
is strictly stronger since squaring loses the sign. -/
theorem qr_filter {ℓ : ℕ} [Fact ℓ.Prime] {a b c : ZMod ℓ}
    (ha : a = 0) (hb : b ≠ 0) (hc : c = (a + b) ^ 2) :
    c ≠ 0 ∧ IsSquare c := by
  subst ha; subst hc
  refine ⟨by simpa using pow_ne_zero 2 hb, ?_⟩
  exact ⟨0 + b, by ring⟩

end Erdos307
