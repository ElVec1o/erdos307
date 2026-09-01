# On the equation n″ = n and Erdős Problem #307

**Author:** Vico Bonfioli — <vicobonfioli@gmail.com>

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20684626.svg)](https://doi.org/10.5281/zenodo.20684626)

Archived on Zenodo at every release. The concept DOI
[10.5281/zenodo.20684626](https://doi.org/10.5281/zenodo.20684626) always resolves to the
latest version; each release also carries its own version DOI.

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

- **#307 is Ufnarovski–Åhlander's Conjecture 4.** Ufnarovski & Åhlander (2003, *J. Integer Seq.* **6**,
  Art. 03.3.4) prove a period-two point of `n ↦ n′` has squarefree members with disjoint supports, and
  state the resulting equation — `(Σ 1/pᵢ)(Σ 1/qⱼ) = 1` has no solution in distinct primes — as their
  Conjecture 4. That is Erdős #307, in the derivative literature, in 2003. It is generally credited to
  2019. Priority for the reformulation belongs to 2003; what 2019 adds is *naming* it as #307. So #307
  has been open in a second literature, under another name, for over twenty years, and the barrier
  below is a bound on Conjecture 4.

- **An erratum in the standard reference.** Kovič (2012, *J. Integer Seq.* **15**, Art. 12.3.8),
  Prop. 18 claims `r + s ≥ 34` and `max{m,n} ≥ 1.92 × 10²¹` for two-cycles. The proof multiplies an
  *upper* bound on `m` against a *lower* bound on `n`; the directions don't compose. Its own bounds
  yield exactly `p₁q₁ < rs < p_r q_s`, from which no cardinality bound follows. Explicit model in
  [`code/kovic_prop18_audit.gp`](code/kovic_prop18_audit.gp), machine-checked in
  [`lean/Erdos307/KovicProp18.lean`](lean/Erdos307/KovicProp18.lean). The *inference* is refuted, not
  the *statement* — which is true, but as a corollary of the barrier below. Consequence: `|P ∪ Q| ≥ 60`
  appears to be the **first** valid cardinality bound for arithmetic-derivative two-cycles.

- **Rigidity.** `Σ 1/p` is automatically in lowest terms, forcing `N_P = D_Q`, `N_Q = D_P`,
  `P ∩ Q = ∅` (Lean-formalized).
- **Barrier.** Any solution has `|P ∪ Q| ≥ 59` and `min(∏P, ∏Q) ≥ 2.09 × 10⁵⁶`, for **both**
  members, unconditionally — improving the strongest valid unconditional `n″ = n` bound in the
  literature (Kovič 2012's computer search, `x > 10⁴`) by ~52 orders of magnitude, and the
  conditional Kovič Prop. 17 (`3.23 × 10⁹`, when the smaller member is odd) by ~47. So all direct
  search is void. **This barrier is
  fully machine-checked in Lean 4** (`erdos307_barrier_closed`, no extremality hypothesis, and no
  `native_decide`: the numeral bridge is kernel-checked). A finite verification over the complete
  list of 49,961 admissible 59-prime supports then **proves** `|P ∪ Q| ≥ 60`
  (Prop. close59). The *statement* `|P ∪ Q| ≥ 60` is not ours: it appears on the problem page
  ([erdosproblems.com/307](https://www.erdosproblems.com/307)), which asserts it from "P, Q disjoint
  and ∑1/p ≥ 2". That implication does not hold as displayed, since the first 59 prime reciprocals
  already sum to 2.00235, so those hypotheses give Rosen's `≥ 59`; reaching 60 needs the 49,961
  supports excluded one at a time. We claim the proof, not the statement. Any solution also has
  `min(∏P, ∏Q) > 3.50 × 10⁵⁷`
  — verified by two independent exact-integer programs (`code/close59.py`, `hunt/close59.rs`) **and
  machine-checked in Lean 4** (`erdos307_sixty`: the search's completeness is proved, not assumed;
  the enumeration's `dfs_run` step runs under the kernel's own `decide`, with no `native_decide`).
  The product
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

- **Both Pythagorean layers have density zero on the squarefree stratum, with a rate.** The minus
  layer `m′ − 2m = d²` is exactly the set where the arithmetic derivative takes square values, so a
  square sieve applies once the symbol is factorised as `((m′−2m)/r) = (m/r)·((σ_r(m)−2)/r)` —
  verified exhaustively, 54,514,790 checks, 0 violations. The sieve closes at
  `P = log log N / (log log log N)^{1+ε}`, where two uniform estimates are available:
  `lem:charcancelunif` for the character sums (uniform for odd squarefree
  `r ≤ (log log N)² / (log log log N)^{2+ε}`) and `lem:deficit` for the local deficits. That is
  `prop:condrate`, which gives `thm:a9` with the rate
  `≪ N (log log log N)^{2+ε} / log log N`. The squarefree restriction is not
  cosmetic — every tool is squarefree-only, and the unrestricted statement is **not** proved.
  The far stronger `≪ N (log log N)^{1/2+δ} / (log N)^{1/4}` (`cor:a9rate`) also holds. It needs the
  pretentious distance uniformly at moduli `r ≤ (log N)^{1/2} log log N`, where the coefficient mass `√φ(r)`
  swamps `log log N` — so `lem:swdirect` estimates the distance *without expanding in characters*,
  applying Siegel–Walfisz to the residue classes directly and paying a factor `r` against
  `exp(-c√log x)` instead of `√r` against a bound on `log L`. That is free up to any fixed power of
  `log N`. The `√φ(r)` wall was a cost of the expansion, not of the arithmetic.
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

## Upstream

The barrier is carried in Google DeepMind's
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) as
[`FormalConjectures/ErdosProblems/307.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/307.lean),
where `erdos_307.barrier` is tagged `@[category research solved]` and carries
`formal_proof using lean4` pointing at this repository at a pinned commit.
[PR #5236](https://github.com/google-deepmind/formal-conjectures/pull/5236) offers the strengthened
cardinality bound upstream.

That upstream copy is a snapshot of an earlier state of this work: it states `59 ≤ #(P ∪ Q)` and
`4·10¹¹² ≤ (∏P)²`, i.e. `∏P ≥ 2.09×10⁵⁶`. The results here are now stronger — `|P ∪ Q| ≥ 60`
(`prop:close59`, `erdos307_sixty`) and `min(∏P, ∏Q) > 3.50×10⁵⁷` — so the pinned statement should be
read as the version that was current when it was merged, not as the present state.

The problem page ([erdosproblems.com/307](https://www.erdosproblems.com/307)) still asserts
`|P ∪ Q| ≥ 60` from "P, Q disjoint and ∑1/p ≥ 2". As of 2026-09-01 that justification is unchanged
on the page; why it does not hold as displayed is set out in the introduction of the paper, and the
bound itself is proved here by a different route.

## Layout

```
paper/   erdos307-core.pdf       — the paper (32 pp; the results)
         erdos307-companion.pdf  — the companion (99 pp; explorations, closures, the square sieve and the density theorem)
         erdos307.tex            — the single source both are generated from
lean/    Lean 4 (mathlib v4.30.0) formalization of the rigidity and barrier results
code/    Rust and PARI/GP programs behind every numerical claim (a few legacy Python) — see code/README.md
certs/   independently checkable ECPP primality certificates: the immune families, and the
         141-digit cofactor behind the refutation of the Lyapunov criterion
hunt/    Rust enumerators for derivative cycles over ℤ and the number rings, with the verified
         certificates cited in the note — see hunt/README.md
```

## Building

- **Paper:** `cd paper && python3 ../code/split_paper.py` then build companion, core, companion,
  core with `pdflatex` (twice each, for the `xr` cross-references). No BibTeX run needed. The two
  documents are derived from `erdos307.tex`, never hand-edited, so they cannot drift.
- **Lean:** `cd lean && lake exe cache get && lake build` (Lean / mathlib `v4.30.0`). Then
  `lake env lean Check.lean` prints the axiom dependencies of 395 declarations across all 54 modules
  — everything depends only on `propext, Classical.choice, Quot.sound` (no `sorryAx`), with exactly
  no exceptions: there is no `native_decide` anywhere in the development.
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
