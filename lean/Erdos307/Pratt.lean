import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-!
# Pratt certificates

`lucas_primality` certifies `p` prime from a witness `a` of order `p - 1`. To use it on a concrete
number one needs every prime factor of `p - 1`; `pratt` takes them as an explicit list with
multiplicity whose product is `p - 1`, so the "every prime divisor" quantifier reduces to list
membership. The two power conditions stay in `ZMod p`, where `reduce_mod_char` evaluates them by
binary exponentiation without forming `a ^ (p - 1)`: `norm_num`'s `Nat.mod` extension does not
yet do this, which is why the conditions are not stated on `ℕ`.

Paper: used by Proposition `prop:ppninherit`.
-/

namespace Erdos307

theorem pratt (p a : ℕ) (L : List ℕ) (hL : ∀ q ∈ L, q.Prime) (hprod : L.prod = p - 1)
    (hpow : (a : ZMod p) ^ (p - 1) = 1) (hdiv : ∀ q ∈ L, (a : ZMod p) ^ ((p - 1) / q) ≠ 1) :
    p.Prime := by
  refine lucas_primality p (a : ZMod p) hpow ?_
  intro q hq hqd
  apply hdiv q
  rw [← hprod] at hqd
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp hqd
  rwa [(Nat.prime_dvd_prime_iff_eq hq (hL r hr)).mp hqr]

end Erdos307
