import Erdos307.Sixty

/-!
# From level 60 to the barrier 61

`erdos307_sixty` gives `|P ∪ Q| ≥ 60`. If no solution has exactly `60` primes, the barrier rises to `61`.
The hypothesis is the content of Proposition `prop:level60closed`: the pair sector is empty by
`prop:pairclosed`, and the single-tail sector by the computations recorded there. This file proves only the
assembly step, which is independent of how level `60` is decided.

Paper: Proposition `prop:level60closed`.
-/

namespace Erdos307

theorem erdos307_sixtyone_of_level60
    (hL : ∀ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ q ∈ Q, q.Prime) →
      (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1 → (P ∪ Q).card ≠ 60)
    {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) :
    61 ≤ (P ∪ Q).card := by
  have h60 := erdos307_sixty hP hQ heq
  have hne := hL P Q hP hQ heq
  omega

end Erdos307
