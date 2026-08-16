import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Positivity

/-!
# Divisor-sum upper bounds, elementarily

`prop:plusthin` (atom A6) reduces the semiprime plus-layer count to `∑_{s ≤ Y} τ(2s² + 1)` in
`PlusThin.lean`, and then cites Dirichlet's asymptotics

  `∑_{u ≤ Z} τ(u) ∼ Z log Z`,   `∑_{u ≤ Z} τ(u)/u ∼ ½(log Z)²`

to reach `O(√X (log X)²)`. Mathlib has neither, and A6 has carried that as its recorded blocker.

**The asymptotics are not what a thinness statement needs.** A density-zero conclusion consumes only
the *upper* halves, and those are elementary double counting with no analysis in them at all. Both
are proved here, stated with the harmonic sum `H_Z = ∑_{d ≤ Z} 1/d` in place of `log Z`, which
removes the last analytic ingredient:

  `∑_{u ≤ Z} τ(u)/u ≤ H_Z²`     (`sum_tau_div_le_harmonic_sq`)
  `∑_{u ≤ Z} τ(u)   ≤ Z · H_Z²`  (`sum_tau_le_mul_harmonic_sq`)

and `prop:plusthin` consumes exactly these two, as `Y·∑τ(u)/u + ∑τ(u)`.

The proof of each is the same one line of counting: `τ(u)` is the number of pairs `(d, m)` with
`dm = u`, so summing over `u ≤ Z` is summing over pairs with `dm ≤ Z`, and that set of pairs sits
inside the full square `[1,Z] × [1,Z]`, where the sum factors.

`H_Z ≤ 1 + log Z` recovers the usual shape when wanted, but nothing here needs it, and keeping the
statements harmonic is what makes them formal rather than cited.

**Why the upper halves suffice.** `prop:plusthin` concludes `O(√X (log X)²)`, an upper bound, and an
upper bound needs only upper bounds on its inputs. Citing the asymptotic `∼` was citing more than the
argument uses. The lower halves and the constant `½` are needed only for a matching *lower* bound,
which `prop:plusthin` does not assert.

What this does **not** do: it does not finish A6. The divisor sums are no longer the blocker, but the
assembly around them is not formalised either, namely the range count
`#{s ≤ Y : u ∣ 2s²+1} ≤ (roots mod u)·(Y/u + 1)`, the bound `roots ≤ 2^ω(u) ≤ τ(u)` by CRT from
`two_roots_quadratic`, and `H_Z ≤ 1 + log Z` if the statement is wanted with logarithms. A6 keeps its
star, with that assembly as the recorded blocker in place of the divisor sums.

Paper: Proposition `prop:plusthin`, Proposition `prop:plus`.
-/

namespace Erdos307

open Finset

/-- The pairs `(d, m)` with `dm = u`, for `u` ranging over `[1, Z]`, all sit inside the square
`[1, Z] × [1, Z]`: each coordinate divides `u ≤ Z` and is at least `1`. -/
theorem divisorsAntidiagonal_subset_square {Z u : ℕ} (hu : u ∈ Icc 1 Z) :
    u.divisorsAntidiagonal ⊆ Icc 1 Z ×ˢ Icc 1 Z := by
  intro p hp
  rw [Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨hmul, hne⟩ := hp
  rw [mem_Icc] at hu
  have h1 : 1 ≤ p.1 := by
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h, zero_mul] at hmul; omega
    · exact h
  have h2 : 1 ≤ p.2 := by
    rcases Nat.eq_zero_or_pos p.2 with h | h
    · rw [h, mul_zero] at hmul; omega
    · exact h
  refine mem_product.mpr ⟨mem_Icc.mpr ⟨h1, ?_⟩, mem_Icc.mpr ⟨h2, ?_⟩⟩
  · calc p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right _ h2
      _ = u := hmul
      _ ≤ Z := hu.2
  · calc p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left _ h1
      _ = u := hmul
      _ ≤ Z := hu.2

/-- The antidiagonals of distinct `u` are disjoint: a pair determines its product. -/
theorem divisorsAntidiagonal_pairwiseDisjoint (Z : ℕ) :
    ((Icc 1 Z : Finset ℕ) : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
  intro a _ b _ hab
  simp only [Function.onFun, disjoint_left]
  intro p hpa hpb
  rw [Nat.mem_divisorsAntidiagonal] at hpa hpb
  exact hab (hpa.1 ▸ hpb.1 ▸ rfl)

/-- `τ(u)/u` is the antidiagonal sum of `1/(dm)`: on the antidiagonal `dm = u`, so every term is
`1/u` and there are `τ(u)` of them. -/
theorem tau_div_eq_antidiagonal_sum {u : ℕ} (hu : u ≠ 0) :
    (u.divisors.card : ℚ) / u = ∑ p ∈ u.divisorsAntidiagonal, (1 : ℚ) / (p.1 * p.2) := by
  rw [Nat.sum_divisorsAntidiagonal (fun d m => (1 : ℚ) / (d * m))]
  rw [Finset.sum_congr rfl (fun d hd => ?_), Finset.sum_const, nsmul_eq_mul]
  · rw [div_eq_mul_inv, mul_comm]
  · have hd' : (d : ℚ) * ((u / d : ℕ) : ℚ) = (u : ℚ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    rw [hd', one_div]

/-- **The reciprocal-weighted bound.** `∑_{u ≤ Z} τ(u)/u ≤ H_Z²`, where `H_Z = ∑_{d ≤ Z} 1/d`.

This is the upper half of Dirichlet's `∑_{u≤Z} τ(u)/u ∼ ½(log Z)²`, and it is what a density-zero
conclusion actually consumes. Pure counting: the pairs `(d,m)` with `dm ≤ Z` inject into the square
`[1,Z] × [1,Z]`, on which the sum factors as a product of harmonic sums. -/
theorem sum_tau_div_le_harmonic_sq (Z : ℕ) :
    ∑ u ∈ Icc 1 Z, (u.divisors.card : ℚ) / u ≤ (∑ d ∈ Icc 1 Z, (1 : ℚ) / d) ^ 2 := by
  have hterm : ∀ u ∈ Icc 1 Z, (u.divisors.card : ℚ) / u
      = ∑ p ∈ u.divisorsAntidiagonal, (1 : ℚ) / (p.1 * p.2) := by
    intro u hu
    rw [mem_Icc] at hu
    exact tau_div_eq_antidiagonal_sum (by omega)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_biUnion (divisorsAntidiagonal_pairwiseDisjoint Z)]
  have hsub : (Icc 1 Z).biUnion Nat.divisorsAntidiagonal ⊆ Icc 1 Z ×ˢ Icc 1 Z := by
    intro p hp
    obtain ⟨u, hu, hpu⟩ := Finset.mem_biUnion.mp hp
    exact divisorsAntidiagonal_subset_square hu hpu
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (le_of_eq ?_)
  · intro p _ _
    positivity
  · rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl ?_
    intro p _
    exact (one_div_mul_one_div _ _).symm

/-- **The unweighted bound.** `∑_{u ≤ Z} τ(u) ≤ Z · H_Z²`.

Weaker than Dirichlet's `Z log Z` by one harmonic factor, and free: every `u` in range satisfies
`u ≤ Z`, so `τ(u) = (τ(u)/u)·u ≤ Z·(τ(u)/u)`, and `sum_tau_div_le_harmonic_sq` finishes it.

The loss costs nothing where it is used. `prop:plusthin` combines the two sums as
`Y·∑τ(u)/u + ∑τ(u)`, and with `Z ≍ Y` both terms are `O(Y·H²)`, which is the `√X (log X)²` shape it
reports. A sharper `Z·H_Z` would need the per-`d` count `⌊Z/d⌋`, a different argument, and would not
change the stated rate. -/
theorem sum_tau_le_mul_harmonic_sq (Z : ℕ) :
    ∑ u ∈ Icc 1 Z, (u.divisors.card : ℚ) ≤ (Z : ℚ) * (∑ d ∈ Icc 1 Z, (1 : ℚ) / d) ^ 2 := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_tau_div_le_harmonic_sq Z) (by positivity))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro u hu
  rw [mem_Icc] at hu
  have hu0 : (0 : ℚ) < u := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hu.1
  have huZ : (u : ℚ) ≤ Z := by exact_mod_cast hu.2
  rw [mul_div_assoc']
  rw [le_div_iff₀ hu0]
  have hnn : (0 : ℚ) ≤ (u.divisors.card : ℚ) := by positivity
  calc (u.divisors.card : ℚ) * u ≤ (u.divisors.card : ℚ) * Z :=
        mul_le_mul_of_nonneg_left huZ hnn
    _ = (Z : ℚ) * (u.divisors.card : ℚ) := mul_comm _ _

/-! ### The logarithmic form

Mathlib's `harmonic_le_one_add_log` converts the harmonic statements above into the shape the paper
prints, `H_Z ≤ 1 + log Z`, at no cost. This is what makes the formal content match the printed claim
rather than merely implying it. -/

/-- `∑_{d ≤ Z} 1/d` is Mathlib's `harmonic Z`. -/
theorem harmonic_eq_sum_one_div (Z : ℕ) : (∑ d ∈ Icc 1 Z, (1 : ℚ) / d) = harmonic Z := by
  rw [harmonic_eq_sum_Icc]
  exact Finset.sum_congr rfl (fun d _ => one_div _)

/-- **The printed form.** `∑_{u ≤ Z} τ(u)/u ≤ (1 + log Z)²`, over `ℝ`.

The `(log Z)²` that `prop:plusthin` reports, with an explicit constant and no asymptotic. Obtained
from `sum_tau_div_le_harmonic_sq` by `harmonic_le_one_add_log`; the harmonic statement is the one
with content, and this is its translation. -/
theorem sum_tau_div_le_log_sq (Z : ℕ) :
    ∑ u ∈ Icc 1 Z, ((u.divisors.card : ℝ)) / u ≤ (1 + Real.log Z) ^ 2 := by
  have hQ := sum_tau_div_le_harmonic_sq Z
  rw [harmonic_eq_sum_one_div] at hQ
  have hcast : ∑ u ∈ Icc 1 Z, ((u.divisors.card : ℝ)) / u
      ≤ ((harmonic Z : ℚ) : ℝ) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hQ
    push_cast at this ⊢
    exact this
  refine hcast.trans ?_
  have h0 : (0 : ℝ) ≤ ((harmonic Z : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ harmonic Z := by
      rw [harmonic_eq_sum_Icc]; positivity
    exact_mod_cast this
  exact pow_le_pow_left₀ h0 (harmonic_le_one_add_log Z) 2

/-! ### Counting a range by residue classes

The second input `prop:plusthin` needs beyond the divisor sums: if the admissible `s` lie in `R`
residue classes modulo `u`, then a range of length `Y+1` contains at most `R·(Y/u + 1)` of them.
Elementary, and the proof is the obvious injection. -/

/-- **Range count by residue classes.** The `s ≤ Y` whose residue mod `u` lies in `R` number at most
`|R|·(Y/u + 1)`.

The map `s ↦ (s % u, s / u)` is injective, since `s = u·(s/u) + s%u` recovers `s`, and it lands in
`R ×ˢ [0, Y/u]`. Applied with `R` the roots of `2s² + 1 ≡ 0 (mod u)`, this is the step that turns
the divisor sum of `count_le_divisor_sum` into a count over `s`. -/
theorem count_in_residue_classes (Y u : ℕ) (hu : 0 < u) (R : Finset ℕ) :
    (((Finset.range (Y + 1)).filter (fun s => s % u ∈ R)).card) ≤ R.card * (Y / u + 1) := by
  classical
  have hcard : (R ×ˢ Finset.range (Y / u + 1)).card = R.card * (Y / u + 1) := by
    rw [Finset.card_product, Finset.card_range]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun s => (s % u, s / u)) ?_ ?_
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hs
    refine Finset.mem_product.mpr ⟨hs.2, Finset.mem_range.mpr ?_⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  · intro a ha b hb hab
    have h1 : a % u = b % u := congrArg Prod.fst hab
    have h2 : a / u = b / u := congrArg Prod.snd hab
    calc a = u * (a / u) + a % u := (Nat.div_add_mod a u).symm
      _ = u * (b / u) + b % u := by rw [h1, h2]
      _ = b := Nat.div_add_mod b u

/-! ### Toward the last gap in A6

`prop:plusthin` needs `|R_u| ≤ τ(u)`, where `R_u` is the set of roots of `2s² + 1 ≡ 0` modulo `u`.
The standard route is `|R_u| ≤ 2^ω(u) ≤ τ(u)`, and the second inequality is elementary. It is proved
here; the first is not, and what it needs is recorded below. -/

/-- **`2^ω(u) ≤ τ(u)`.** Each prime of `u` occurs to exponent at least `1`, so each factor `e_p + 1`
of `τ(u) = ∏ (e_p + 1)` is at least `2`.

This is the half of A6's remaining lemma that needs no new theory.

**The other half is not here, and Mathlib does not supply it.** What remains is `|R_u| ≤ 2^ω(u)`,
which is CRT multiplicativity of a root count: writing `u = ∏ p^e`, the equivalence
`ZMod (mn) ≃+* ZMod m × ZMod n` for coprime `m, n` carries `R_{mn}` bijectively to `R_m × R_n`
because `2s² + 1` has integer coefficients and so commutes with the ring map; and at each odd prime
power `|R_{p^e}| ≤ 2`, since `x² = y²` with `x, y` units forces `p^e ∣ x - y` or `p^e ∣ x + y`
(`p` cannot divide both, as `p` is odd and `x` is a unit). Mathlib packages neither the transport of
a root set through `ZMod.chineseRemainder` nor any bound on square roots in `ZMod n`, so this is a
build from scratch and is the single outstanding gap in A6. -/
theorem two_pow_omega_le_tau {u : ℕ} (hu : u ≠ 0) :
    2 ^ u.primeFactors.card ≤ u.divisors.card := by
  rw [Nat.card_divisors hu]
  calc 2 ^ u.primeFactors.card
      = ∏ _p ∈ u.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ u.primeFactors, (u.factorization p + 1) := by
        refine Finset.prod_le_prod' ?_
        intro p hp
        have : 1 ≤ u.factorization p := (Nat.Prime.factorization_pos_of_dvd
          (Nat.prime_of_mem_primeFactors hp) hu (Nat.dvd_of_mem_primeFactors hp))
        omega

end Erdos307
