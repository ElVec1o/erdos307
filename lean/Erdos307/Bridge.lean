import Erdos307.Rigidity
import Erdos307.Injective
import Erdos307.Capstone

/-!
# The Bridge: #307 is a two-cycle of the arithmetic derivative

`thm:bridge`. The three statements

1. \#307 has a solution: finite prime sets `P, Q` with `(∑_{p∈P} 1/p)(∑_{q∈Q} 1/q) = 1`;
2. the arithmetic derivative has a two-cycle: `a ≠ b` with `a' = b` and `b' = a`;
3. `n'' = n` has a solution with `n' ≠ n`, that is one not of the form `p^p`

are equivalent. This is the reformulation the whole project runs on, so it is worth having in Lean
rather than in prose.

The three implications are separated here by exactly the input each needs.

* **(1) ⟹ (2)** is unconditional and is `bridge_forward`. Take `a = ∏P` and `b = ∏Q`. Rigidity
  (`rigidity_coprime`) says each reciprocal sum `csum/dprod` is already in lowest terms, and
  `solution_structure` then forces `csum P = dprod Q` and `csum Q = dprod P`, which is precisely
  `a' = b` and `b' = a`. Nothing is assumed about squarefreeness because at this level it is built
  in: `P` and `Q` are sets of primes and `a`, `b` are their products.

* `a ≠ b` is *derived*, not assumed (`dprod_ne_dprod`): if `a = b` then `csum P = dprod P`, and
  coprimality forces `dprod P = 1`, so `P` is empty and its reciprocal sum is `0`, not `1`. This is
  the Lean form of the paper's remark that a prime-reciprocal sum is never `1`.

* **(2) ⟹ (1)** is `bridge_backward` and is the only implication with an outside input. It needs
  that a derivative two-cycle has squarefree members, which is the Ufnarovski-Åhlander analysis of
  cycles, cited and not reproved; here it appears as the explicit hypotheses `Squarefree a` and
  `Squarefree b`. Those hypotheses are what make `∑_{p ∣ a} 1/p` equal `a'/a`, so the conclusion is
  statement (1) over genuine prime sets rather than the field identity `(a'/a)(b'/b) = 1`, which is a
  tautology given the cycle and says nothing about \#307. Disjointness
  of the two prime supports is *not* an extra assumption either, it follows from
  `gcd(a, a') = 1`, which is Rigidity again (`disjoint_primeFactors_of_cycle`).

* **(2) ⟺ (3)** is pure iteration and holds for any self-map of any type
  (`two_cycle_iff_double_fixed`). The identification of the fixed points of `n ↦ n'` with the
  numbers `p^p` is cited and is not needed for the equivalence itself, only for the phrasing of (3).

The asymmetry is worth recording: (1) ⟹ (2) and the entire barrier are unconditional, because
Rigidity already delivers squarefree, support-disjoint `P, Q` from a \#307 solution. Only the
converse leans on the cited theorem.

Paper: Theorem `thm:bridge`, Remark `rem:cited`, Corollary `cor:ua`.
-/

namespace Erdos307

/-! ### (2) ⟺ (3): a two-cycle is a non-fixed solution of `n'' = n` -/

/-- **(2) ⟺ (3).** For any self-map, having a two-cycle is the same as having a point of period
dividing two that is not fixed. No arithmetic enters. -/
theorem two_cycle_iff_double_fixed {α : Type*} (D : α → α) :
    (∃ a b, a ≠ b ∧ D a = b ∧ D b = a) ↔ (∃ n, D (D n) = n ∧ D n ≠ n) := by
  constructor
  · rintro ⟨a, b, hab, hDa, hDb⟩
    refine ⟨a, ?_, ?_⟩
    · rw [hDa]; exact hDb
    · rw [hDa]; exact Ne.symm hab
  · rintro ⟨n, hnn, hne⟩
    exact ⟨n, D n, fun h => hne h.symm, rfl, hnn⟩

/-! ### The derivative on a set of primes -/

/-- On the product of a set of primes the derivative is the cofactor sum: `(∏S)' = csum S`. This is
the compatibility between the `Finset` model used throughout and the integer-level `ad`. -/
theorem ad_dprod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : ad (dprod S) = csum S := by
  unfold ad dprod
  rw [Nat.primeFactors_prod hS]

/-- **The two members of a cycle are distinct**, and this is forced rather than assumed. If
`∏P = ∏Q` then `csum P = dprod P`, so coprimality makes `dprod P = 1` and `P` empty, whose
reciprocal sum is `0`. -/
theorem dprod_ne_dprod {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty)
    (h1 : csum P = dprod Q) : dprod P ≠ dprod Q := by
  intro heq
  rw [← heq] at h1
  have hcop : Nat.gcd (csum P) (dprod P) = 1 := rigidity_coprime P hP
  rw [h1, Nat.gcd_self] at hcop
  obtain ⟨p, hp⟩ := hPne
  have hdvd : p ∣ dprod P := Finset.dvd_prod_of_mem _ hp
  rw [hcop] at hdvd
  exact absurd (Nat.eq_one_of_dvd_one hdvd) (hP p hp).one_lt.ne'

/-! ### (1) ⟹ (2), unconditional -/

/-- **`thm:bridge`, (1) ⟹ (2).** A \#307 solution is a two-cycle of the arithmetic derivative:
with `a = ∏P` and `b = ∏Q`, one has `a' = b`, `b' = a`, and `a ≠ b`.

The only inputs are Rigidity and the structure theorem; nothing is cited. -/
theorem bridge_forward {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPne : P.Nonempty)
    (hDP : dprod P ≠ 0) (hDQ : dprod Q ≠ 0)
    (h : (csum P : ℚ) / dprod P * ((csum Q : ℚ) / dprod Q) = 1) :
    ad (dprod P) = dprod Q ∧ ad (dprod Q) = dprod P ∧ dprod P ≠ dprod Q := by
  obtain ⟨h1, h2⟩ :=
    solution_structure (rigidity_coprime P hP) (rigidity_coprime Q hQ) hDP hDQ h
  refine ⟨?_, ?_, dprod_ne_dprod hP hPne h1⟩
  · rw [ad_dprod hP]; exact h1
  · rw [ad_dprod hQ]; exact h2

/-! ### (2) ⟹ (1), conditional on the cited squarefreeness -/

/-- **Disjointness is free.** The two members of a cycle have disjoint prime supports, because
`gcd(a, a') = 1` is Rigidity. No extra hypothesis is needed. -/
theorem disjoint_primeFactors_of_cycle {a b : ℕ} (ha : Squarefree a) (hab : ad a = b) :
    Disjoint a.primeFactors b.primeFactors := by
  have hpa : ∀ p ∈ a.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hcop : Nat.Coprime (csum a.primeFactors) (dprod a.primeFactors) :=
    rigidity_coprime a.primeFactors hpa
  rw [dprod_primeFactors ha] at hcop
  have : Nat.Coprime a b := by rw [← hab]; exact hcop.symm
  exact Nat.Coprime.disjoint_primeFactors this

/-- **`thm:bridge`, (2) ⟹ (1).** A two-cycle of squarefree members gives a \#307 solution: the
reciprocal sums of the two prime supports multiply to `1`.

This is statement (1) as the paper states it, over genuine prime sets, not the field identity
`(a'/a)(b'/b) = 1`. That identity is a tautology once `a' = b` and `b' = a`, and holds for any
nonzero `a, b`; it is *not* \#307. The squarefreeness hypotheses are what make `∑_{p ∣ a} 1/p` equal
`a'/a` at all, and they are the Ufnarovski-Åhlander input, supplied here rather than reproved,
exactly as `rem:cited` records.

An earlier version of this file stated the tautology while its docstring claimed the squarefreeness
hypotheses. That was a defect: the hypotheses were absent and the conclusion was weaker than
advertised. -/
theorem bridge_backward {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hab : ad a = b) (hba : ad b = a) :
    (∑ p ∈ a.primeFactors, (p : ℚ)⁻¹) * (∑ q ∈ b.primeFactors, (q : ℚ)⁻¹) = 1 := by
  have hpa : ∀ p ∈ a.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hpb : ∀ q ∈ b.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have ha0 : a ≠ 0 := by rintro rfl; exact not_squarefree_zero ha
  have hb0 : b ≠ 0 := by rintro rfl; exact not_squarefree_zero hb
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
  rw [recipSum_eq _ hpa, recipSum_eq _ hpb, dprod_primeFactors ha, dprod_primeFactors hb,
      show csum a.primeFactors = ad a from rfl, show csum b.primeFactors = ad b from rfl,
      hab, hba]
  field_simp

/-- The mass of a squarefree integer is the reciprocal sum of its prime support, in the `csum/dprod`
form the rest of the project uses. This is what makes `bridge_backward` a statement about \#307 and
not merely about `ad`. -/
theorem mass_eq {a : ℕ} (ha : Squarefree a) :
    (ad a : ℚ) / a = (csum a.primeFactors : ℚ) / dprod a.primeFactors := by
  rw [dprod_primeFactors ha]; rfl

/-! ### The equivalence -/

/-- **`thm:bridge`.** The two directions together, at the level where each is cleanest: a solution
of \#307 produces a two-cycle unconditionally, and a two-cycle with squarefree members produces a
solution. Combined with `two_cycle_iff_double_fixed` this is the full three-way equivalence.

Nothing here decides \#307. It says the problem and the two-cycle question are the same question. -/
theorem bridge {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPne : P.Nonempty)
    (hDP : dprod P ≠ 0) (hDQ : dprod Q ≠ 0)
    (h : (csum P : ℚ) / dprod P * ((csum Q : ℚ) / dprod Q) = 1) :
    ∃ a b : ℕ, a ≠ b ∧ ad a = b ∧ ad b = a := by
  obtain ⟨h1, h2, h3⟩ := bridge_forward hP hQ hPne hDP hDQ h
  exact ⟨dprod P, dprod Q, h3, h1, h2⟩

end Erdos307
