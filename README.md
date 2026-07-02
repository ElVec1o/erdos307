# On the equation n″ = n and Erdős Problem #307

**Author:** Vico Bonfioli — <vico@anvilstack.com>

This repository accompanies the note *"On the equation n″ = n and a problem of Erdős and Barbeau on
products of prime-reciprocal sums."* It contains the paper, a Lean 4 formalization of the rigidity and
barrier results, and the computational scripts and enumerators behind every numerical claim.

> **A candid note on AI assistance.** This work was carried out by the author with substantial
> assistance from Anthropic's Claude, which contributed to the derivations, the exact and heuristic
> computations, the Lean 4 formalization, and the drafting — and was also used to stress-test and
> attempt to refute each claim. Every statement, proof, attribution, and line of the final text was
> reviewed by the author, who is responsible for the contents.

## The problem

Erdős #307 (Barbeau, 1976): do there exist finite sets of distinct primes `P, Q` with
`(Σ_{p∈P} 1/p)(Σ_{q∈Q} 1/q) = 1`? **It is open** — a single example would settle it. The note proves no
new existence/non-existence result; it determines the *structure* of the problem: where its difficulty
lives, what provably cannot resolve it, and where the same phenomenon does and does not occur.

## The bridge

A solution exists **iff** the arithmetic derivative `n ↦ n′` has a 2-cycle `a′ = b, b′ = a` with
`a ≠ b` — equivalently, iff `n″ = n` has a solution that is not a fixed point `pᵖ`. This ties #307 to
the Ufnarovski–Åhlander / Kovič `n″ = n` literature in both directions.

## What the paper establishes

- **Rigidity.** `Σ 1/p` is automatically in lowest terms, forcing `N_P = D_Q`, `N_Q = D_P`,
  `P ∩ Q = ∅` (Lean-formalized).
- **Barrier.** Any solution has `|P ∪ Q| ≥ 59` and `min(∏P, ∏Q) ≥ 2.09 × 10⁵⁶`, improving the best
  published `n″ = n` bound by ~47 orders of magnitude — so all direct search is void. **This barrier is
  fully machine-checked in Lean 4** (`erdos307_barrier_closed`, no extremality hypothesis); the only
  non-logical input is a verified evaluation of the first 59 primes. A finite verification over the
  complete list of 49,961 admissible 59-prime supports then **closes the 59-prime level** (v1.1,
  Prop. close59): any solution in fact has `|P ∪ Q| ≥ 60` and `min(∏P, ∏Q) > 3.50 × 10⁵⁷`
  (computer-verified by two independent exact-integer programs, `code/close59.py` and
  `hunt/close59.rs`; the Lean formalization covers the `≥ 59` statement).
- **The wall, named.** The obstruction is the *orderability of ℚ* (Artin–Schreier formal reality):
  twisted derivative 2-cycles **do** exist over `ℤ[i], ℤ[√−2], ℤ[ω], ℤ[√2]` (all verified exactly), and
  a one-line classification shows ℚ is the only number field where the barrier operates. Over `𝔽_q[t]`
  the derivative has **no** cycles at all (degree theorem), so the obstruction over `ℤ` is purely
  archimedean.
- **Position in the Egyptian-fraction landscape.** Expanding the product, #307 is the *rank-one*
  (rectangular `P×Q`) restriction of the Erdős–Graham problem of writing `1` as a sum of reciprocals of
  semiprimes — a problem that is *solved* in the unrestricted case (Johnson 1978, Watanabe 2020). The
  difficulty is isolated to the rank-one constraint, which forces the ≥59-prime barrier; and the
  rigidity `N(r) ≤ 1` (each rational is an exact prime-reciprocal sum for at most one prime set)
  precisely starves the circle-method machinery that solves the unrestricted problem.
- **Classical layer.** The lines `n′ = n ± 1` are the Giuga numbers and primary pseudoperfect numbers;
  #307's sub-barrier "ghosts" are the pronic Giuga numbers; a settled case of the
  Grau–Oller-Marcén–Sadornil μ-Sondow conjecture; a Hecke/CM bridge to `y² = x³ − x`.
- **No-go and density results.** The difficulty is provably non-local (everywhere locally soluble),
  abc-comfortable, non-genus, non-polynomial, and not reducible to a standard prime-density conjecture;
  an Erdős–Wintner density theorem; S-unit finiteness per support.

The heuristics weakly favour existence at astronomically inaccessible height; **no proof either way is
claimed.**

## Layout

```
paper/   erdos307.tex, erdos307.pdf   — the note (32 pp; self-contained bibliography)
lean/    Lean 4 (mathlib v4.30.0) formalization of the rigidity and barrier results
code/    Python (sympy/numpy) scripts behind every numerical claim — see code/README.md
hunt/    Rust enumerators for derivative cycles over ℤ and the number rings, with the verified
         certificates cited in the note — see hunt/README.md
```

## Building

- **Paper:** `cd paper && pdflatex erdos307.tex` twice (for cross-references). No BibTeX run needed.
- **Lean:** `cd lean && lake exe cache get && lake build` (Lean / mathlib `v4.30.0`). Then
  `lake env lean Check.lean` prints the axiom dependencies of every theorem — the mathematical results
  depend only on `propext, Classical.choice, Quot.sound` (no `sorryAx`); the first-59-primes evaluation
  additionally uses `native_decide`.
- **Code:** Python 3 with `sympy` and `numpy`; each script is standalone (`python3 <name>.py`).
- **Hunt:** `rustc -O -o NAME NAME.rs` then run; each program self-tests and prints progress.

## Status and citation

Erdős #307 remains open. This note contributes the bridge, the machine-checked barrier, the structural
classification of the obstruction, and the precise location of the problem against solved neighbours.
Please cite the note when referring to these results.
