import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The average pair bound

`thm:pairavg` bounds `∑_{r ∈ R} P(D,r)` where `P(D,r)` counts pairs `(d,d')` with
`σ_r(d) ≡ σ_r(d')`, equivalently `r ∣ F(d,d')`. Its proof is a double count: exchange the order of
summation, note that the diagonal has `F = 0` and is therefore divisible by every `r`, and bound the
off-diagonal contribution by the divisor function, using that `F` is nonzero off the diagonal.

That last input is `lem:sigmainj`, already formalised in `Erdos307.Injective`. This file formalises
the counting skeleton, which is where the theorem's content lies; the arithmetic input enters only
through the hypothesis `hdiag`.

Paper: Theorem `thm:pairavg`.
-/

namespace Erdos307

open Finset

/-- For `F ≠ 0`, the elements of a finset dividing `F` are among the divisors of `F`. -/
theorem card_filter_dvd_le {F : ℕ} (hF : F ≠ 0) (R : Finset ℕ) :
    (R.filter (· ∣ F)).card ≤ F.divisors.card := by
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_filter] at hr
  exact Nat.mem_divisors.mpr ⟨hr.2, hF⟩

/-- Double counting: summing a divisibility count over the moduli equals summing over the pairs. -/
theorem sum_filter_comm (R : Finset ℕ) (S : Finset (ℕ × ℕ)) (F : ℕ × ℕ → ℕ) :
    ∑ r ∈ R, (S.filter (fun x => r ∣ F x)).card
      = ∑ x ∈ S, (R.filter (fun r => r ∣ F x)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- **The average pair bound.** With `F` vanishing exactly on the diagonal, the total divisibility
count splits into `|R|` per diagonal pair plus a divisor-function term off the diagonal. This is the
skeleton of `thm:pairavg`; the arithmetic content of the paper's proof is the hypothesis `hdiag`,
supplied there by `lem:sigmainj`. -/
theorem pairavg_bound (R : Finset ℕ) (S : Finset (ℕ × ℕ)) (F : ℕ × ℕ → ℕ)
    (hdiag : ∀ x ∈ S, F x = 0 ↔ x.1 = x.2) :
    ∑ r ∈ R, (S.filter (fun x => r ∣ F x)).card
      ≤ (S.filter (fun x => x.1 = x.2)).card * R.card
        + ∑ x ∈ S.filter (fun x => x.1 ≠ x.2), (F x).divisors.card := by
  rw [sum_filter_comm, ← Finset.sum_filter_add_sum_filter_not S (fun x => x.1 = x.2)]
  apply add_le_add
  · have hdi : ∀ x ∈ S.filter (fun x => x.1 = x.2),
        (R.filter (fun r => r ∣ F x)).card = R.card := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have h0 : F x = 0 := (hdiag x hx.1).mpr hx.2
      congr 1
      apply Finset.filter_true_of_mem
      intro r _
      rw [h0]
      exact dvd_zero r
    rw [Finset.sum_congr rfl hdi, Finset.sum_const]
    simp
  · apply Finset.sum_le_sum
    intro x hx
    rw [Finset.mem_filter] at hx
    exact card_filter_dvd_le (fun h => hx.2 ((hdiag x hx.1).mp h)) R

end Erdos307
