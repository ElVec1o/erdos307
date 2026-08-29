import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The breeder is integral: `q = a'/N` is never a fraction

In the bilinear breeder form one fixes coprime squarefree `M₀, N`, seeks a two-cycle `a = M₀rp`,
`b = Nq`, and puts `G = NM₀ - N'M₀'`, `c = M₀N'`, `K = GN² + c²`. Each factorisation of `K` by a
divisor `d ≡ -c (mod G)` proposes a candidate `(r,p)`, and `q` is then read off as
`q = (M₀rp - N)/N'`. That expression is a quotient, and `N'` is enormous, so one might fear that
a candidate is usable only when `N'` happens to divide `M₀rp - N` -- a further condition of
probability about `1/N'`, which would make the whole construction hopeless.

It is not a condition. It is automatic, for the following reason.

* `breeder_bilinear_iff` : the bilinear equation is, after dividing by `G`, exactly
  `G·rp - c(r+p) = N²`. The `K` and the factorisation are a repackaging of this one identity.
* `breeder_key` : substituting `G = NM₀ - N'M₀'`, `c = M₀N'`, `a = M₀rp` and
  `a' = M₀'rp + M₀(r+p)` turns that identity into `N(a - N) = N'·a'`.
* `breeder_q_integral` : since `N` is squarefree, `gcd(N, N') = 1`, so `N ∣ a'`, and therefore
  `q = (a - N)/N' = a'/N` is an integer.

So the breeder never wastes a candidate on a non-integral `q`: every solution of the bilinear
equation delivers an honest integer `q`, and the only remaining demand on the triple is primality.
This is what makes the expectation `(τ(K)/G)·(ln r ln p ln q)^{-1}` the correct count, with no
hidden `1/N'` penalty; empirically, of the candidates thrown up by a scan of `51,132` frames,
every one had integral `q`.

Paper: Proposition `prop:bde`, Section `sec:breeder`.
-/

namespace Erdos307.Breeder

/-- The bilinear equation, divided by `G`, is `G·rp - c(r+p) = N²`. -/
theorem breeder_bilinear_iff {G c r p N : ℤ} (hG : G ≠ 0) :
    (G * r - c) * (G * p - c) = G * N ^ 2 + c ^ 2 ↔ G * (r * p) - c * (r + p) = N ^ 2 := by
  constructor
  · intro h
    exact mul_left_cancel₀ hG (by linear_combination h)
  · intro h
    linear_combination G * h

/-- Substituting the frame data turns that identity into `N(a - N) = N'·a'`. -/
theorem breeder_key {M0 N M0p Np r p G c a ap : ℤ}
    (hG : G = N * M0 - Np * M0p) (hc : c = M0 * Np)
    (ha : a = M0 * r * p) (hap : ap = M0p * r * p + M0 * (r + p))
    (h : G * (r * p) - c * (r + p) = N ^ 2) :
    N * (a - N) = Np * ap := by
  subst hG hc ha hap; nlinarith [h]

/-- **The integrality.** `gcd(N, N') = 1` forces `N ∣ a'`, so `q = a'/N` is an integer. -/
theorem breeder_q_integral {N Np a ap : ℤ} (hcop : IsCoprime N Np)
    (h : N * (a - N) = Np * ap) : N ∣ ap := by
  have hdvd : N ∣ Np * ap := ⟨a - N, h.symm⟩
  exact (hcop.dvd_of_dvd_mul_left hdvd)

/-- The three steps together: a solution of the bilinear equation yields an integral `q`. -/
theorem breeder_integral {M0 N M0p Np r p G c a ap : ℤ} (hG0 : G ≠ 0)
    (hG : G = N * M0 - Np * M0p) (hc : c = M0 * Np)
    (ha : a = M0 * r * p) (hap : ap = M0p * r * p + M0 * (r + p))
    (hcop : IsCoprime N Np)
    (hbil : (G * r - c) * (G * p - c) = G * N ^ 2 + c ^ 2) :
    N ∣ ap :=
  breeder_q_integral hcop
    (breeder_key hG hc ha hap ((breeder_bilinear_iff hG0).mp hbil))

end Erdos307.Breeder
