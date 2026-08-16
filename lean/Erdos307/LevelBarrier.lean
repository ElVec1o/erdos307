import Erdos307.Numeral
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The level-by-level exclusion program stops at 60, and cannot be continued

`prop:close59` proves `|P ∪ Q| ≥ 60` by enumerating the **49,961** admissible 59-element prime
supports (those with `∑ 1/p > 2`) and excluding each one. `prop:tailkill` and the tail search of
`prop:tailbound` then handle level 60 by adjoining one further prime to each of those 49,961 bases.
The obvious continuation is level 61: enumerate the admissible 60-element supports and repeat.

**That continuation does not exist.** The enumeration at level 59 is finite for one reason only:
`∑_{i<59} 1/p_i = N59/P59 = 2.00235… > 2` *barely*, so demanding mass `> 2` from exactly 59 primes
forces them to be nearly the smallest 59. The moment a 60th prime is allowed, the first 59 already
carry the mass on their own and the 60th is completely unconstrained: **any** prime whatsoever
extends them to an admissible 60-set. So there are infinitely many admissible supports at every
level `≥ 60`, and level-by-level enumeration terminates at the level already done.

The content is `admissible_extends`: admissibility is monotone under adjoining a prime, and the
prime may be taken larger than any bound. Everything else is bookkeeping on top of it.

This is a **no-go**, and it is the reason the tail search of `prop:tailbound`, however far it is
pushed, bears on level 60 alone. Any further progress on #307 must be non-enumerative: it cannot
proceed by exhausting supports one level at a time.

Paper: Proposition `prop:levelbarrier`, Proposition `prop:close59`, Proposition `prop:tailkill`,
Proposition `prop:tailbound`, Remark `rem:whatisleft`.
-/

namespace Erdos307

open Finset

/-- **Admissibility is monotone, and unboundedly so.** Given any finite set `U` of primes with
`∑_{p ∈ U} 1/p > 2` and any bound `B`, there is a prime `q > B` outside `U` for which `insert q U`
is again a set of primes, of one greater cardinality, still with mass `> 2`.

The mass condition can therefore never constrain the largest prime once it is met, which is exactly
what makes the level-59 enumeration finite and every later one infinite. -/
theorem admissible_extends {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime)
    (h2 : (2 : ℚ) < ∑ p ∈ U, (p : ℚ)⁻¹) (B : ℕ) :
    ∃ q : ℕ, q.Prime ∧ B < q ∧ q ∉ U ∧
      (∀ p ∈ insert q U, p.Prime) ∧
      (insert q U).card = U.card + 1 ∧
      (2 : ℚ) < ∑ p ∈ insert q U, (p : ℚ)⁻¹ := by
  -- a prime beyond both `B` and everything already in `U`
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (max (B + 1) (U.sup id + 1))
  have hqB : B < q := lt_of_lt_of_le (Nat.lt_succ_self B) (le_trans (le_max_left _ _) hqge)
  have hqU : q ∉ U := by
    intro hmem
    have : q ≤ U.sup id := Finset.le_sup (f := id) hmem
    have : U.sup id + 1 ≤ q := le_trans (le_max_right _ _) hqge
    omega
  refine ⟨q, hq, hqB, hqU, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · exact h ▸ hq
    · exact hU p h
  · exact Finset.card_insert_of_notMem hqU
  · rw [Finset.sum_insert hqU]
    have hqpos : (0 : ℚ) < (q : ℚ)⁻¹ := by
      have : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq.pos
      positivity
    linarith

/-- **The level barrier.** Iterating `admissible_extends`: from any admissible set one reaches
admissible sets of every larger cardinality, each containing a prime beyond any prescribed bound.

So for every `n` past the first admissible level the supports of size `n` are infinite in number,
and the enumeration that closes level 59 has no successor. -/
theorem admissible_of_card_add {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime)
    (h2 : (2 : ℚ) < ∑ p ∈ U, (p : ℚ)⁻¹) (k B : ℕ) :
    ∃ V : Finset ℕ, (∀ p ∈ V, p.Prime) ∧ V.card = U.card + k ∧
      (2 : ℚ) < ∑ p ∈ V, (p : ℚ)⁻¹ ∧ (0 < k → ∃ q ∈ V, B < q) := by
  induction k with
  | zero => exact ⟨U, hU, by simp, h2, by omega⟩
  | succ k ih =>
    obtain ⟨V, hV, hcard, hmass, _⟩ := ih
    obtain ⟨q, hq, hqB, hqV, hins, hcins, hmins⟩ := admissible_extends hV hmass B
    exact ⟨insert q V, hins, by rw [hcins, hcard]; omega, hmins,
      fun _ => ⟨q, Finset.mem_insert_self q V, hqB⟩⟩

/-- **What this costs the programme, stated as the conjunction so the two halves cannot drift.**
Level 59 is finite and was enumerated; every level above it is not, for the single reason that a
set already carrying mass `> 2` absorbs an arbitrarily large prime and keeps it.

The left conjunct is the extension step; the right records that the resulting supports realise every
cardinality above the starting one. Together: enumeration by level cannot pass the level already
closed, so further progress on #307 must be non-enumerative. -/
theorem level_enumeration_terminates {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime)
    (h2 : (2 : ℚ) < ∑ p ∈ U, (p : ℚ)⁻¹) :
    (∀ B : ℕ, ∃ q : ℕ, q.Prime ∧ B < q ∧ q ∉ U ∧
        (2 : ℚ) < ∑ p ∈ insert q U, (p : ℚ)⁻¹)
    ∧ (∀ k B : ℕ, ∃ V : Finset ℕ, (∀ p ∈ V, p.Prime) ∧ V.card = U.card + k ∧
        (2 : ℚ) < ∑ p ∈ V, (p : ℚ)⁻¹ ∧ (0 < k → ∃ q ∈ V, B < q)) := by
  refine ⟨fun B => ?_, fun k B => admissible_of_card_add hU h2 k B⟩
  obtain ⟨q, hq, hqB, hqU, _, _, hmass⟩ := admissible_extends hU h2 B
  exact ⟨q, hq, hqB, hqU, hmass⟩

end Erdos307
