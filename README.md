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
  fully machine-checked in Lean 4** (`erdos307_barrier_closed`, no extremality hypothesis, and no
  `native_decide`: the numeral bridge is kernel-checked). A finite verification over the complete
  list of 49,961 admissible 59-prime supports then **proves** `|P ∪ Q| ≥ 60`
  (Prop. close59). The *statement* `|P ∪ Q| ≥ 60` is not ours: it appears on the problem page
  ([erdosproblems.com/307](https://www.erdosproblems.com/307)), which asserts it from "P, Q disjoint
  and ∑1/p ≥ 2". That implication does not hold as displayed, since the first 59 prime reciprocals
  already sum to 2.00235, so those hypotheses give Rosen's `≥ 59`; reaching 60 needs the 49,961
  supports excluded one at a time. We claim the proof, not the statement. Any solution also has
  `min(∏P, ∏Q) > 3.50 × 10⁵⁷` and `min(∏P, ∏Q) > 3.50 × 10⁵⁷`
  — verified by two independent exact-integer programs (`code/close59.py`, `hunt/close59.rs`) **and
  machine-checked in Lean 4** (`erdos307_sixty`: the search's completeness is proved, not assumed;
  the enumeration's single `dfs_run` step is the project's one `native_decide` use). The product
  bounds `Π₆₀ > 2.46 × 10¹¹⁵` and `min(∏P,∏Q) > 3.5053 × 10⁵⁷` are proved in the paper, not in Lean:
  `erdos307_sixty` proves `|P ∪ Q| ≥ 60` only. The coprime variant with `1 ∉ P∪Q` inherits the
  full `≥ 60` bound (Cor. coprime60).
- **The wall, named.** The obstruction is the *orderability of ℚ* (Artin–Schreier formal reality):
  twisted derivative 2-cycles **do** exist over `ℤ[i], ℤ[√−2], ℤ[ω], ℤ[√2]` (all verified exactly).
  An earlier claim that ℚ is the only number field where the barrier operates is **false** and has
  been withdrawn: in `ℚ(√17, √33)` the prime 2 splits completely, giving four ideals of norm 2, mass
  exactly 2 and product 16 against ℚ's `10^112.9` (see `prop:fieldoptimal`). Over `𝔽_q[t]`
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

- **A Lyapunov criterion for the negative direction, and its refutation.** `δ(n) = log n + σ(n)/2`
  strictly decreases whenever `σ(n·n') < 2`, giving an elementary Lyapunov re-proof of the barrier
  that kills cycles of *every* length (`thm:halflyap`, Lean-verified, no `native_decide`). Above mass
  2 the criterion is **false**: no real `λ` makes `log σ(n) < λ(σ(n) − σ(n'))` hold throughout. The
  witness is `n₀` = the product of the 68 primes in `[7,373]` other than `307, 317, 359`, for which
  `n₀' = 2·3·5·C` with `C` a 141-digit prime (ECPP certificate), so `σ(n₀') = 31/30 > σ(n₀) > 1` and
  both sides of the inequality have the wrong sign (`thm:lyapfalse`, Lean-verified). The hypothesis
  `σ(n·n') < 2` is therefore not an artefact of the method but exactly sharp. Consequently
  `n₀'' > n₀`: the ratio `r = σ(n)σ(n')`, whose value `1` *is* a solution, takes values on both sides
  of `1`, so no inequality on `r` can settle #307.

- **Both Pythagorean layers have density zero, unconditionally.** The minus layer `m′ − 2m = d²` is
  exactly the set where the arithmetic derivative takes square values, so Heath-Brown's *square sieve*
  applies once the symbol is factorised as `((m′−2m)/r) = (m/r)·((σ_r(m)−2)/r)` — verified
  exhaustively, 54,514,790 checks, 0 violations. Halász then supplies the cancellation, because
  `u ↦ e_r(t/u)` is not multiplicative and the pretentious distance is governed by a Salié sum. This
  gives `thm:a9`, and keeping the sieve parameter a function of `N` upgrades it to an explicit rate,
  `≪ N log log N / (log N)^{1/4}` (`cor:a9rate`).
- **The 34 immune families are now unconditional.** Their primality was graded `[C]` because
  Baillie-PSW is rigorous only in its *composite* verdicts. APR-CL proves all 68 integers prime, and
  `certs/immune_ecpp.txt` archives **independently checkable ECPP certificates** for every one
  (68 verified, 0 invalid). The structural half is formal: `Erdos307.jacobiSym_A_eq_B` proves
  `(D_S|A_S) = (D_S|B_S)` in Lean 4 on the three standard axioms, with no `native_decide`.
- **Four independent blocks on the existence route**, no two the same obstruction: the construction
  has zero free slots (`∏Q = a′` exactly); no purely algebraic argument can work (it would refute
  `thm:ff`); the immune families cannot be tested (225-digit class group, or a 10⁻¹¹² hit rate); and
  a large family of sequences does not help, since the union stays logarithmically thin.

**On the heuristics.** The usual statement that heuristics weakly favour existence is weaker than it
looks. The expected count is `f(1)·log X` with `f` the density of `σ(a)σ(a′)` at 1, and that constant
**cannot be measured**: the barrier places the entire region `σ(a)σ(a′) ≥ 1` above `10^112.9`, while
the largest value observed below `10⁷` is `0.5535`. Unlike Bateman–Horn or Hardy–Littlewood, this
heuristic has no empirical support and cannot acquire any. **No proof either way is claimed.**

## Layout

```
paper/   erdos307.tex, erdos307.pdf   — the note (91 pp; self-contained bibliography)
lean/    Lean 4 (mathlib v4.30.0) formalization of the rigidity and barrier results
code/    Rust and PARI/GP programs behind every numerical claim (a few legacy Python) — see code/README.md
certs/   independently checkable ECPP primality certificates: the immune families, and the
         141-digit cofactor behind the refutation of the Lyapunov criterion
hunt/    Rust enumerators for derivative cycles over ℤ and the number rings, with the verified
         certificates cited in the note — see hunt/README.md
```

## Building

- **Paper:** `cd paper && pdflatex erdos307.tex` twice (for cross-references). No BibTeX run needed.
- **Lean:** `cd lean && lake exe cache get && lake build` (Lean / mathlib `v4.30.0`). Then
  `lake env lean Check.lean` prints the axiom dependencies of 317 declarations across all 38 modules
  — everything depends only on `propext, Classical.choice, Quot.sound` (no `sorryAx`), with exactly
  one exception: `erdos307_sixty`, which additionally carries the `native_decide` axiom of `dfs_run`.
- **Code:** Rust (`rustc -O -o NAME NAME.rs`) for the heavy computations, PARI/GP (`gp -q -f NAME.gp`)
  for primality and class-group work, and a few legacy Python 3 scripts (`sympy`, `numpy`).
### Repository provenance

Commits before v1.2 carry the author string `Vico Bonfioli` rather than `ElVec1o` (25 commits), and
three of them (`6a936b7`, `c41efee`, `3e9920d`, the v1.0 and v1.1 releases) carry
`Co-Authored-By:` trailers naming an AI assistant. The project's convention is `ElVec1o` with no AI
attribution, and the git config and every commit from v1.2 onward comply.

This history is **deliberately not rewritten.** Doing so would change every commit hash from
`6a936b7` forward, invalidating all 13 release tags, every existing clone, and any externally cited
SHA. The cost is real and outward-facing; the benefit is cosmetic compliance with a convention that
is already met going forward. Recording the discrepancy is the honest resolution.

- **Consistency:** `bash code/check_consistency.sh` recomputes every cross-file number (page count,
  coverage totals, `native_decide` site count, `sorry` count, orphan census, Lean anchor coverage)
  from the artifact and exits nonzero on any mismatch. Three external audits found drift of exactly
  this kind; the script exists so a fourth does not have to. It also compiles
  `lean/Vacuity.lean`, which discharges every hypothesis of the most exposed theorems at concrete
  models: `#print axioms` cannot see unsatisfiable hypotheses, and a theorem with contradictory
  ones passes the axiom check cleanly while proving nothing. One did, and was caught by adversarial
  review rather than by any check here.
- **Certificates:** `certs/lyap_refute_cofactor_ecpp.txt` is machine-readable and verifies under
  PARI with `primecertisvalid(read("certs/lyap_refute_cofactor_ecpp.txt"))`.
  `certs/immune_ecpp.txt` is a human-readable `primecertexport` dump and **cannot** be consumed that
  way; earlier versions of this README and of the file's own header said otherwise, which was wrong.
  Verify it with `gp -q -f code/immune_cert_verify.gp`, which re-proves all 68 subjects by ECPP in
  about 1.3 s. Last run: 68/68 prime, 0 failures.
- **Hunt:** `rustc -O -o NAME NAME.rs` then run; each program self-tests and prints progress.

## Status and citation

Erdős #307 remains open. This note contributes the bridge, the machine-checked barrier, the structural
classification of the obstruction, and the precise location of the problem against solved neighbours.
Please cite the note when referring to these results.
