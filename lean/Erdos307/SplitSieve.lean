import Erdos307.Frame

/-!
# The split sieve for single-tail families

A level-60 single-tail family is `S ∪ {q}` with `S` a base of primes and `q ∉ S` the tail prime.
Split the tail prime off the side that carries it: `a = dprod (T ∪ {q})`, `b = dprod (S \ T)` for
`T ⊆ S`. Leibniz at `q` (`csum_insert_prime`) turns the two cycle equations into

* `(i)  dprod (S \ T) = q * csum T + dprod T`   (from `a' = b`),
* `(ii) csum (S \ T) = dprod T * q`             (from `b' = a`), whence `dprod T ∣ csum (S \ T)`,

and eliminating `q` between them gives the `q`-free criterion

  `dprod T ^ 2 + csum T * csum (S \ T) = dprod S`.

Condition (ii) is the sieve. By the anatomy lemma it is a congruence `∑_{p ∈ S \ T} p⁻¹ ≡ 0 (mod r)`
at every `r ∈ T`, costing a factor `1 / r` each, so `∏_{p ∈ S} (1 + 1/p)` splits survive out of
`2 ^ |S|`. It needs no primality or factorisation of `A_S = csum S + 2 * dprod S`, so it reaches the
families that `prop:immunedecide` (which needs `A_S` prime) cannot.

`csum_odd_card` is the parity law behind the observed constraint `2 ∈ T → |T| odd`.

Paper: Proposition `prop:splitsieve`. Computation: `code/split_sieve.rs`.
-/

namespace Erdos307

variable {S T : Finset ℕ} {q : ℕ}

/-- The two halves of a split multiply to the base. -/
theorem dprod_split (hT : T ⊆ S) : dprod T * dprod (S \ T) = dprod S := by
  rw [dprod, dprod, dprod, ← Finset.prod_union (Finset.disjoint_sdiff)]
  rw [Finset.union_sdiff_of_subset hT]

/-- **SS1 / split equation (i).** The `a' = b` half, with the tail prime split off. -/
theorem split_fst (hq : q ∉ T) (hq0 : 0 < q)
    (hab : csum (T ∪ {q}) = dprod (S \ T)) :
    dprod (S \ T) = q * csum T + dprod T := by
  rw [← hab, csum_insert_prime hq hq0]

/-- **SS2 / split equation (ii), the sieve.** The `b' = a` half forces `dprod T ∣ csum (S \ T)`. -/
theorem split_snd (hq : q ∉ T)
    (hba : csum (S \ T) = dprod (T ∪ {q})) :
    dprod T ∣ csum (S \ T) := by
  rw [hba, dprod_insert_prime hq]
  exact Dvd.intro q rfl

/-- **The `q`-free criterion.** Eliminating `q` between (i) and (ii). This is the statement the Rust
sieve tests: no reference to the tail prime survives. Stated over `ℕ` with no subtraction, so
nothing is hidden in truncation. -/
theorem split_criterion (hT : T ⊆ S) (hq : q ∉ T) (hq0 : 0 < q)
    (hab : csum (T ∪ {q}) = dprod (S \ T)) (hba : csum (S \ T) = dprod (T ∪ {q})) :
    dprod T ^ 2 + csum T * csum (S \ T) = dprod S := by
  have hi : dprod (S \ T) = q * csum T + dprod T := split_fst hq hq0 hab
  have hii : csum (S \ T) = dprod T * q := by rw [hba, dprod_insert_prime hq]
  have h := dprod_split hT
  rw [hi] at h
  rw [hii, ← h]
  ring

/-- **Contrapositive, the form the computation uses.** If no split of the base satisfies the
criterion, the family carries no two-cycle for any tail prime. -/
theorem no_cycle_of_no_split (hT : T ⊆ S) (hq : q ∉ T) (hq0 : 0 < q)
    (h : dprod T ^ 2 + csum T * csum (S \ T) ≠ dprod S) :
    ¬ (csum (T ∪ {q}) = dprod (S \ T) ∧ csum (S \ T) = dprod (T ∪ {q})) := by
  rintro ⟨h1, h2⟩
  exact h (split_criterion hT hq hq0 h1 h2)

/-- **SS3 / the parity law.** For a finset of odd numbers, the cofactor sum has the parity of the
cardinality: every cofactor is a product of odd numbers, hence odd. With `2 ∈ T` the complement
`S \ T` is all odd, so `2 ∣ csum (S \ T)` forces `|S \ T|` even. -/
theorem csum_odd_card {X : Finset ℕ} (hX : ∀ p ∈ X, Odd p) :
    csum X % 2 = X.card % 2 := by
  have hodd : ∀ p ∈ X, (dprod X / p) % 2 = 1 := by
    intro p hp
    have hp0 : 0 < p := (hX p hp).pos
    rw [dprod_div X hp hp0]
    have : Odd (∏ q ∈ X.erase p, q) :=
      Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
        (fun q hq => hX q (Finset.mem_of_mem_erase hq))
    exact Nat.odd_iff.mp this
  unfold csum
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl hodd]
  simp [Finset.sum_const]

end Erdos307
