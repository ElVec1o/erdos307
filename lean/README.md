# Lean 4 formalization

Machine-checked formalization (Lean `v4.30.0`, mathlib `v4.30.0`) of the rigidity and barrier
results for Erdős #307. The top-level theorem `erdos307_barrier_closed` is **complete and
hypothesis-free**: any solution to #307 has both prime products `≥ 2×10⁵⁶`.

## Build

```bash
lake exe cache get      # fetch the prebuilt mathlib oleans
lake build              # builds the Erdos307 library
lake env lean Check.lean   # prints the axiom dependencies of every theorem
```

## Axiom footprint

`#print axioms` shows two tiers:

- The **mathematical** theorems depend only on the three standard mathlib axioms `propext`,
  `Classical.choice`, `Quot.sound` — **no `sorryAx`**.
- The **numeral bridge** (`np0…np59`, that the first 60 primes are `2,3,…,281`) and everything
  downstream of it additionally use `native_decide` (axiom `…_native.native_decide.ax_1_1`), i.e.
  they trust the compiler's evaluation of a finite primality computation. This is quarantined to
  the numeral lemmas; it is the only non-logical input to the closed barrier.

## Contents

For a finite set `S` of distinct primes: `dprod S = ∏_{p∈S} p` and
`csum S = ∑_{p∈S} (dprod S)/p` (the cofactor sum = numerator of `∑ 1/p` in lowest terms).

| Theorem | Statement | Axioms |
|---|---|---|
| `rigidity_coprime` | `gcd(csum S, dprod S) = 1` — `∑ 1/p` is in lowest terms | 3 |
| `solution_structure` | `(N_P/D_P)(N_Q/D_Q)=1` ⇒ `N_P=D_Q ∧ N_Q=D_P` | 3 |
| `reciprocal_sum_gt_two` | strict AM–GM `s·t=1, s≠1 ⇒ s+t>2` | 3 |
| `barrier_numeric`, `barrier_algebraic`, `barrier` | `D_P² ≥ 4×10¹¹²` given the ratio bound | 3 |
| `erdos307_barrier` | the barrier over genuine prime sets, given extremality `hRatio` | 3 |
| `nth_prime_le_orderEmb` | the `i`-th element of a prime set is `≥` the `i`-th prime | 3 |
| `prod_first_primes_le`, `recipSum_le_first_primes` | smallest-primes extremality | 3 |
| `hRatio_of_extremal` | reduces `hRatio` to the smallest-prime ratio fact | 3 |
| `np0 … np59`, `prod_first59_nat`, `sum_first59/58` | the first 60 primes & their `∏`/`∑ 1/p` | +native |
| `base_case`, `hmono_all`, `card_ge_59` | base/induction/`\|P∪Q\|≥59` | +native |
| **`erdos307_barrier_closed`** | **no hypotheses**: prime sets `P,Q`, `Q≠∅`, `(∑1/p)(∑1/q)=1` ⇒ `(∏P)² ≥ 4×10¹¹²` | +native |
| `dfs_sound` | completeness of the pruned close59 search (pruning proven sound) | 3 |
| **`erdos307_sixty`** | **no hypotheses**: any solution has `\|P∪Q\| ≥ 60` — Prop. close59 fully formalised | +native |

This formally verifies the **barrier** (a lower bound on any solution) and the **closing of the
59-prime level**; Erdős #307 itself — whether a solution *exists* — remains open. The constant is
the round `2×10⁵⁶`; the note's sharper `2.09×10⁵⁶` (from `Π₅₉` exactly) is a constant tightening,
and `erdos307_sixty` pushes the level to `≥ 60` (whence `min > 3.50×10⁵⁷` on paper).

## Files
- `Erdos307/Rigidity.lean` — `rigidity_coprime`, `solution_structure` (T1, T2).
- `Erdos307/Barrier.lean` — strict AM–GM, the exact 59-thresholds, the abstract barrier (T3, T4).
- `Erdos307/Capstone.lean` — `erdos307_barrier` over genuine prime sets.
- `Erdos307/Extremal.lean` — smallest-primes extremality (`nth_prime_le_orderEmb` and corollaries)
  and the reduction `hRatio_of_extremal`.
- `Erdos307/Numeral.lean` — the first-60-primes numeral bridge (the only `native_decide` use).
- `Erdos307/Closed.lean` — the `k`-induction, the `|P∪Q|≥59` bound, and `erdos307_barrier_closed`.
- `Erdos307/Sixty.lean` — Prop. close59: the verified pruned search (`dfs` + `dfs_sound`), the
  Pythagorean plus-square, the forced-primes/element bounds, and `erdos307_sixty`.
- `Check.lean` — `#print axioms` for every theorem.
