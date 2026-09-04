import Erdos307.Frame
import Erdos307.Extremal

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

variable {S T M : Finset ℕ} {q : ℕ}

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

/-- **SS8.** Condition (ii) is not an extra hypothesis: it is the mod-`α` shadow of the criterion.
Reducing the criterion modulo `dprod T` kills `dprod T ^ 2` and `dprod S`, leaving
`dprod T ∣ csum T * csum (S \ T)`, and rigidity (`gcd (csum T) (dprod T) = 1`) strips the first
factor. This is why the divisibility is the right first filter for the computation. -/
theorem split_snd_of_criterion (hT : T ⊆ S) (hprime : ∀ p ∈ T, p.Prime)
    (hcrit : dprod T ^ 2 + csum T * csum (S \ T) = dprod S) :
    dprod T ∣ csum (S \ T) := by
  have hdS : dprod T ∣ dprod S := Dvd.intro _ (dprod_split hT)
  have hmul : dprod T ∣ csum T * csum (S \ T) := by
    have h2 : dprod T ∣ dprod T ^ 2 := dvd_pow_self _ two_ne_zero
    have hsum : dprod T ∣ dprod T ^ 2 + csum T * csum (S \ T) := hcrit ▸ hdS
    exact (Nat.dvd_add_right h2).mp hsum
  exact (Nat.Coprime.dvd_of_dvd_mul_left ((rigidity_coprime T hprime).symm) hmul)


/-! ### The mixed pair-sector case: no sieve, but a finite range -/

/-- **SS9, arithmetic core.** If two reciprocals together exceed `c`, then `c * p < 2` for the
smaller prime `p`. Division-free, which is the form the enumeration uses: it bounds the smaller
tail prime of the mixed pair-sector case, where no divisibility sieve is available. -/
theorem recip_sum_bound {p q : ℕ} {c : ℚ} (hp : 0 < p) (hpq : p ≤ q)
    (h : c < (p : ℚ)⁻¹ + (q : ℚ)⁻¹) : c * (p : ℚ) < 2 := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℚ) < q := lt_of_lt_of_le hp0 (by exact_mod_cast hpq)
  have e1 : (p : ℚ) * (p : ℚ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hp0)
  have e2 : (p : ℚ) * (q : ℚ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hq0).mpr (by exact_mod_cast hpq)
  calc c * (p : ℚ) = (p : ℚ) * c := by ring
    _ < (p : ℚ) * ((p : ℚ)⁻¹ + (q : ℚ)⁻¹) := mul_lt_mul_of_pos_left h hp0
    _ = (p : ℚ) * (p : ℚ)⁻¹ + (p : ℚ) * (q : ℚ)⁻¹ := by ring
    _ ≤ 1 + 1 := by rw [e1]; linarith
    _ = 2 := by norm_num

/-- **SS9.** For a pair family `U = W ∪ {p, q}` with `|W| = 58` and total mass above `2`, the two
tail reciprocals must make up the deficit `2 - ∑_{r ∈ W} 1/r`, which is positive because 58 primes
never reach mass `2` (`recipSum58_lt_two`, via `recipSum_le_first_primes`). Hence the mixed case,
which admits no sieve, is confined to a finite range of the smaller tail prime. -/
theorem pair_tail_deficit {W : Finset ℕ} (hW : ∀ r ∈ W, r.Prime) (hcard : W.card = 58)
    {p q : ℕ} (hmass : 2 < (∑ r ∈ W, (r : ℚ)⁻¹) + (p : ℚ)⁻¹ + (q : ℚ)⁻¹) :
    2 - (∑ i ∈ Finset.range 58, ((Nat.nth Nat.Prime i : ℚ))⁻¹) < (p : ℚ)⁻¹ + (q : ℚ)⁻¹ := by
  have hbound := recipSum_le_first_primes hW
  rw [hcard] at hbound
  linarith

/-! ### Arbitrary tail multiplier: arity one and the pair sector at once -/

/-- **SS7, the general criterion.** Let the tail be any finite set `M` of primes disjoint from `T`,
so `a = dprod (T ∪ M)` and `b = dprod (S \ T)`. Leibniz on the union and eliminating the tail gives

  `dprod T ^ 2 * csum M + csum T * csum (S \ T) = dprod S`,

which is `split_criterion` when `M = {q}` (`csum M = 1`) and the pair-sector criterion when
`M = {p, q}` (`csum M = p + q`). The sieve `dprod T ∣ csum (S \ T)` below carries no assumption on
`M` at all, which is what lets it reach the pair sector: the arity enters only through `csum M`. -/
theorem split_criterion_gen (hT : T ⊆ S) (hTM : Disjoint T M)
    (hab : csum (T ∪ M) = dprod (S \ T)) (hba : csum (S \ T) = dprod (T ∪ M)) :
    dprod T ^ 2 * csum M + csum T * csum (S \ T) = dprod S := by
  have hleib : csum (T ∪ M) = dprod M * csum T + dprod T * csum M := csum_union_eq hTM
  have hbaM : csum (S \ T) = dprod T * dprod M := by
    rw [hba, dprod, dprod, dprod, Finset.prod_union hTM]
  have h := dprod_split hT
  rw [← hab, hleib] at h
  rw [hbaM]
  rw [← h]
  ring

/-- **SS7, the sieve, arity-independent.** `∂b = a` forces `dprod T ∣ csum (S \ T)` whatever the
tail multiplier is. This is the step that the arity-one weapon of `prop:immunedecide` cannot
generalise, and it is why the sieve applies to the pair sector. -/
theorem split_snd_gen (hTM : Disjoint T M) (hba : csum (S \ T) = dprod (T ∪ M)) :
    dprod T ∣ csum (S \ T) := by
  rw [hba, dprod, dprod, Finset.prod_union hTM]
  exact Dvd.intro _ rfl

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
