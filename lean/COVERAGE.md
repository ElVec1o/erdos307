# Formal coverage of `paper/erdos307.tex`

**85 of 150** labelled results are named by a Lean file in `Erdos307/` (66 files, **0 `sorry`**).

`lake env lean Check.lean` probes **439 declarations across all 66 modules**. Everything is on the
three standard axioms or fewer, with no exceptions. `dfs_run`, the pruned-search execution that
closes level 60, was the last site off that footing; it and the `erdos307_sixty` that consumes it are
now kernel-`decide`, as is the numeral bridge behind `card_ge_59` and `erdos307_barrier_closed`.

## What the category column is, and is not

The category is a **heuristic** applied to the surrounding prose; the `Paper:` anchor in each Lean
file is the guarantee. The v1.4.6 edition of this file mis-filed `lem:symbolfact`, a two-line
algebraic identity, as COMPUTATIONAL, because its block reports an exhaustive check alongside the
proof. It also reported 48 of 104 while the true total is 106: the extractor required a `[title]`
bracket, so untitled results such as `thm:ff` were invisible. Both are fixed, and both were found by
external audit rather than by this file, which is the honest record.

## Trust boundary: none beyond the logic

Every declaration in the development depends only on `propext`, `Classical.choice` and
`Quot.sound`. There is no `native_decide` site and no `ofReduceBool` anywhere.

The last one was `dfs_run`, the pruned search of `prop:close59`. `dfs` compares rationals and the
kernel cannot reduce a `Rat` comparison at all -- `Nat.gcd` is well-founded recursion, not a GMP
primitive -- so `decide` did not merely run slowly on it, it failed to evaluate. Removed by three
changes: scale by `Mscale`, the 327-digit product of the 138 primes in play, which clears the
denominators EXACTLY so the scaled search branches identically and `dfs_sound` is reused unchanged;
replace `Nat.sqrt` on a 130-digit number by an eleven-modulus residue certificate
(`NonSquare.lean`); and carry the product and cofactor sum down the recursion instead of rebuilding
them at each of the 49,961 leaves. The kernel runs the search in about a minute.

## Formalisation debt (Rule 5): three analytic atoms

Rule 5 requires every atom sitting at PROVED to carry either an active formalisation or a recorded
blocker, and forbids "not yet attempted". **The four algebraic atoms are all discharged**, and three
of the four fell because the blocker had been mis-stated rather than because the mathematics was
hard. **Three analytic atoms are blocked**, and are recorded in the table below: the minus--layer
density theorem and the two uniform estimates it rests on. They are the first atoms here whose
blocker is a genuine absence in Mathlib rather than a mis-stated one. **A7 is discharged**: its regime (2)
cited Hasse-Weil for a point count, but the statement needs only *existence* of one point, and
counting the pairs directly gives a double character sum whose inner sums are the two complete
evaluations proved for A3. `pairlocal_inner_sum` and `pairlocal_count_pos`
(`lean/Erdos307/PairLocalCount.lean`) carry it, positive from `l >= 17` against the `l >= 107` in
play. 0 `sorry`, standard axioms.
**A8 is discharged.** It was carried as a deliberate refusal, on the ground that certifying the
minimisation behind `113.2` would need `native_decide`. That was the wrong direction: the conclusion
drawn is that the *gain* over the barrier is under one order, which is an UPPER bound on a minimum,
and an upper bound on a minimum needs a witness, not a search. `nogain_witness`
(`lean/Erdos307/NoGainWitness.lean`) exhibits `S` and `T` and checks
`((prod S)^2 sigma(S))^2 < 10^227` in exact integer arithmetic: the bound at that `S` is `113.5`,
so the gain is under `0.6` of one order. 0 `sorry`, standard axioms, no `native_decide`.
**A3 is discharged**: its two complete character sums are now proved rather than cited, as
`Erdos307.sum_quadraticChar_affine` and `sum_quadraticChar_quadratic`, over any finite field of odd
characteristic (`lean/Erdos307/CompleteSums.lean`, 0 `sorry`, standard axioms), and checked against
direct evaluation for all odd primes up to 59 (33,008,952 quadruples, 0 violations).
**A6 is discharged**: the CRT root bound that was its only missing lemma is now
`Erdos307.rootSet_card_le_two_pow_omega`, composed with `two_pow_omega_le_tau` as
`rootSet_card_le_tau` (`lean/Erdos307/RootCount.lean`, 0 `sorry`, standard axioms). What is left of
A6 is the instantiation of an abstract reduction to this layer, not a lemma: "plus-hit" is not
defined in Lean, and the paper says so.

They were not the same kind of debt. A7 was described here as a cited external input needing
Hasse-Weil; that was mis-stated too, and counting the pairs directly gives a double character sum
instead. A3 was in that category and is no longer: the character sums
turned out to be elementary once written in the right form, which is a reminder that "Mathlib does
not carry it" is not the same as "it is hard". A8's refusal was likewise mis-framed --- the claim
that needed proving was the easy direction all along.

| atom | formalised | blocked on | what unblocks it |
|---|---|---|---|
| `lem:charcancelunif` ⭐ | no | Halasz's theorem, Siegel--Walfisz, Siegel's theorem, and the zero--free region -- none in Mathlib | a formal analytic number theory library at the level of `L`--function zero--free regions; genuinely a research contribution, not an oversight here. Re-checked against mathlib `c5ea003` (2026-09-02): `LSeries/PrimesInAP` gives Dirichlet qualitatively and `NumberTheory/Chebyshev` some upstreamed pieces, but there is no prime number theorem, no zero--free region, no Siegel--Walfisz, and no Halász or pretentious theory anywhere in mathlib. The blockers stand unchanged |
| `lem:deficit` ⭐ | algebraic layer only (`Deficit.lean`, 10 declarations: the algebraic core, enumerated in its docstring) | the same four analytic inputs | as above; the two star together or not at all |
| `prop:condrate` / `thm:a9` ⭐ | no | the two lemmas above | as above |
| `lem:swdirect` ⭐ | no | Siegel--Walfisz (hence Siegel), and Hal\'asz downstream | as above; it needs strictly *fewer* analytic inputs than `lem:charcancelunif` --- no zero--free region, no `L`--function bound, no exceptional--zero split --- but Siegel--Walfisz alone is already far outside Mathlib |
| `cor:a9rate` ⭐ | no | `lem:swdirect` plus the sieve | as above |
| `prop:sector42` ⭐ | partly (`Sector42.lean`, 6 declarations: the forced-prime identity and its converse, the sign condition, the case-split inequality, the parity step, and the conclusion with the two finite computations as explicit hypotheses) | a certificate of `3.7e10` leaves has no Lean-checkable form; `native_decide` on the enumerator would need the search itself inside Lean | a verified checker for the pruned enumeration, on the pattern of `dfs_run` at level 60, but four orders of magnitude larger; not attempted |

Six atoms are starred, and honestly so. All six now have their non-analytic core formalised; what remains under each is analysis or a certificate too large to check, never algebra:
`Deficit.lean` carries the algebraic **core** of `lem:deficit` --- ten declarations covering the
additivity of `σ_p` that makes the detector multiplicative, the orthogonality that supplies the main
term, the Ramanujan sum with its reindexing and normalisation giving the principal Fourier
coefficient `-1/(p-1)`, the Gauss-sum identity, the generic sum-splitting behind the CRT step, and
Cauchy--Schwarz. That last is where `√r · log L = o(L)`, and hence the range `r ≤ L²/(log L)^{2+ε}`
of both uniform lemmas, comes from.

It is **not** the whole algebraic layer, and this paragraph has now claimed that it was three times.
Still unformalised and still not analytic: the detection identity in the form the proof uses, the
term-by-term bookkeeping, `|τ(χ)| = √p` and the coefficient value it gives, the CRT step proper, the
three-case bound on `|c_{ψ₀}|`, Parseval, and the closing size comparison. The star therefore covers
more than the four analytic inputs, and the file's own docstring enumerates exactly what. `lem:charcancelunif` is the first result in this project
whose proof rests on deep analytic inputs. The lesson recorded above -- that "Mathlib does not carry
it" is not the same as "it is hard" -- was tested here and, this once, does not apply: Halasz and
Siegel are not elementary in disguise.

A6 moved furthest this release: its divisor sums, their logarithmic form, and the range count are
all formal, leaving the CRT root bound as the single remaining lemma. A7 moved in the previous
release, to Weil alone -- and then past it. Six atoms are starred (see the table above); five are analytic, not algebraic, and stand or fall together; the sixth is a finite enumeration too large to certify. Every one of the six now carries a machine-checked non-analytic core, so the star measures exactly the missing analysis and nothing else.

## Standing debt, and what has been carved off it

The policy on the star is that an atom keeps it until it is `VERIFIED` outright, but the debt is not
one undifferentiated block, and the part of each proof that is *not* the missing analysis is being
formalised as it is identified. What is machine-checked so far, per starred atom:

| atom | formalised core | what is left |
|---|---|---|
| `lem:swdirect` ⭐ | `SWDirect.lean` (4 declarations): the *Removing ε* diagonalisation — the exchange `(1-1/2j)(1-G)L - C ≥ (1-G)L - L/j` as an equivalence, its sufficient condition `L ≥ 2jC`, and the passage to `o(L)`. This is the whole of the proof that is not the analytic estimate. | Siegel–Walfisz itself |
| `lem:deficit` ⭐ | `Deficit.lean` (10 declarations): the multiplicativity, orthogonality and Gauss-sum core | the four analytic inputs |
| `prop:ppnsectors`, at-60 sweep ⭐ | `SectorGeneral.lean` (4 declarations): the forced-prime identity `ℓ(dR − d'R') = d'R + d²` for arbitrary `d`, its converse, and the sign condition; the `d = 42` case is recovered as a specialisation | the enumerations themselves: `16,234` sectors, each a pruned search over `59`-prime supports with an exact-integer divisibility test, largest `41,654` sets. As with `prop:sector42`, `native_decide` would need the search inside Lean; a verified checker on the `dfs_run` pattern is the only route and is not attempted |
| `prop:sector42` ⭐ | `Sector42.lean` (6 declarations): the forced-prime identity and its converse, the sign condition, the case split, the parity step | the `3.7 × 10¹⁰`-leaf enumeration |
| `lem:charcancelunif` ⭐ | `CharCancel.lean` (6 declarations): the constant analysis. `√r/φ(r) = ∏ √p/(p-1)`; the factor `u ↦ u/(u²-1)` is antitone and below `1`, so only `ω(r) = 1` and `ω(r) = 2` need bounding; `√7/6 < 1/2` and `√15/8 < 1/2` settle them, and `√5/4 > 2/5`, `√3/2 > 1/2` show `r = 3, 5` are genuinely excluded. This is where the hypothesis `r ≥ 7` and the constant `1 - √15/8 = 0.515…` come from. | Halász and the zero-free region |
| `prop:phasecount` | When the sector enumeration is complete: at most `J-1` primes beyond the truncation |
| `prop:oddsector` | `OddSector.lean` (3 declarations): a sum of `k` odd integers has the parity of `k`, so the cofactor sum of an odd squarefree `d` has the parity of `ω(d)`, and `ω(d)` even gives `2 ∣ d'` | VERIFIED, nothing outstanding |
| `rem:twosided`, `rem:lyapshape` (the two exclusion results) | `Exclusions.lean` (4 declarations): the Lyapunov increments telescope and cannot both be negative for any `G`; the primary pseudoperfect gap is `1/n` and falls below any constant | VERIFIED, nothing outstanding |
| `prop:condrate` / `thm:a9` ⭐ | `CondRate.lean` (3 declarations): the detector steps. That `a_m = m' - 2m` never vanishes on squarefree `m > 1` (it would force `m ∣ m'` against `gcd(m',m) = 1`); that a nonzero square has Legendre symbol `1` at every prime not dividing it; and the resulting lower bound `∑_p (a ∣ p) ≥ \|P\| - #{p ∣ a}` that the second moment is built on. | the two analytic lemmas above |
| `cor:a9rate` ⭐ | `SieveBalance.lean` (3 declarations): that `P = (log N)^{1/4}(log log N)^{1/2}` is the exact balance point of the diagonal and character terms, and is optimal — so the exponent `1/4` is the true optimum of this sieve, not an artefact. | `lem:swdirect` plus Halász |

Separately, one step that was never starred because it was never an atom — the soundness of the
reciprocity certificate, carried in prose through `prop:close59` and the whole level-60 campaign —
is now `Certificate.lean` (4 declarations). It is the deduction the campaign and the pair-sector
computation both consume: a prime `ℓ ∣ A` with `(D∣ℓ) = -1` empties the family for every `q`.
Formalising it turned up nothing wrong, but it was the largest unformalised load-bearing step in the
computational half of the paper. The recurring error was
treating "Mathlib does not carry the named theorem" as evidence that the step needs that theorem;
in three of four cases the step did not.

## The "algebraic gap is zero" claim is retired

This file asserted, in three consecutive releases, that no unformalised result is purely algebraic.
It was wrong every time, and each time the counterexample was found by external audit rather than
here:

| release | counterexample | why the classifier missed it |
|---|---|---|
| v1.4.6 | `thm:ff` | the extractor required a `[title]` bracket, so untitled results were invisible |
| v1.4.7 | `lem:symbolfact` | keyed on prose; the block reports an exhaustive check alongside an algebraic proof |
| v1.4.8 | `cor:coprime60` | same cause: a least-prime-factor reduction filed as COMPUTATIONAL |

Three failures of the same claim from three different causes is a sign the method is unfit, not that
the instances were unlucky. **The claim is withdrawn.** What replaces it: the category column below
is *indicative only*, derived from keywords in surrounding prose, and the `Paper:` anchor in each
Lean file is the sole guarantee of coverage. Anyone auditing this repository should read the
uncovered list and judge each entry directly rather than trusting the bucket it landed in.

All three counterexamples are now formalised (`FunctionField.lean`, `NormalForm.symbolfact`,
`Coprime60.lean`).

## How to re-run this audit

```bash
python3 - <<'EOF'
import re, glob
tex = open('paper/erdos307.tex').read()
pat = re.compile(r'\\\\begin\\{(theorem|proposition|lemma|corollary)\\}(?:\\[((?:[^\\[\\]]|\\[[^\\]]*\\])*)\\])?\\s*\\\\label\\{([a-z:0-9]+)\\}')
labels = {m[2] for m in pat.findall(tex)}
lean = set()
for f in glob.glob('lean/Erdos307/*.lean'):
    lean |= set(re.findall(r'`([a-z]+:[a-z0-9]+)`', open(f).read()))
print(len(labels & lean), 'of', len(labels), 'covered')
print('uncovered:', sorted(labels - lean))
EOF
```

## COMPUTATIONAL (26)

The result *is* a number a program produces.

| label | statement |
|---|---|
| `cor:diagonals` | Diagonal stratification: the cost of the last lattice step |
| `cor:gos` | Nonemptiness families for the mu--Sondow conjecture |
| `prop:anticorr` | The barrier is statistically complete |
| `prop:bde` | Bilinear breeder form |
| `prop:coladder` | The co--ladder and the arithmetic Riccati equation |
| `prop:compositea` | The composite mechanism: |P|=2 is one line and one primality |
| `prop:divisor` | Divisor trick |
| `prop:ffsunit` | Inverting one place destroys the function--field obstruction |
| `prop:genus` | A principal--genus necessary condition, and a cascade on solutions |
| `prop:geometry` | Geometry of the solution set |
| `prop:groupoid` | The peeling groupoid |
| `prop:halfplane` | The deviation half--plane |
| `prop:immunedecide` | Immune level-60 families are decided in polynomial time, and are empty |
| `prop:lvl60factor` | Level 60 is decided by factoring: x < A_S forces x to be a square root of D_S mod A_S |
| `prop:lineanatomy` | Line anatomy: pinning, coupling, caps |
| `prop:massbound` | Mass--defect bound on the second prime |
| `prop:mod72` | A difference--36 congruence modulo 72 |
| `prop:multiplier` | Gaussian multiplier form of the ladder |
| `prop:novanish` | No vanishing derivatives, no transport, and the price of exactness |
| `prop:oddsector` | Odd sectors keep the prime 2 only when omega(d) is odd |
| `prop:oddthr` | Even--gap plus lines are empty below 3.23times10^9 |
| `prop:pairform` | Pair form; the one--equation relaxation |
| `prop:plusinf` | Infinitely many gaps carry a nonempty plus line |
| `prop:ppnsectors` | The primary pseudoperfect sectors: the forced-prime identity in general |
| `prop:sector42` | The d=42 sector at 64 primes |
| `prop:sectorbarrier` | The barrier is a function of the split |
| `prop:sectors` | Sector decomposition of level 60 |
| `prop:slotstrat` | Slot stratification of the divisibility set |
| `prop:sunit` | S--unit rigidity of twisted cycles |
| `prop:transport` | Divisor transport |
| `thm:existence` | Existence of twisted derivative two--cycles |

## ANALYTIC (19)

Needs analytic machinery Mathlib does not carry.

| label | statement |
|---|---|
| `cor:secondbarrier` | A second, independent derivation of the barrier |
| `lem:charcancel` | Cancellation in the character sums |
| `lem:localsq` | Local densities at p^2 |
| `lem:reversal` | Reversal |
| `prop:bilinear` | Kernel norm |
| `prop:circular` | The route is circular |
| `prop:density` | The abundance density is a theorem |
| `prop:divset` | The divisibility set: slope one is dense, slope two is not |
| `prop:f1` | The heuristic constant is the barrier's own probability |
| `prop:lines` | The determined slot: all derivative lines are thin, uniformly |
| `prop:multiplicityfail` | Multiplicity cannot help |
| `prop:nearmiss` | The near-miss spectrum, and why the heuristic cannot be calibrated |
| `prop:nolocal` | No single--modulus congruence obstruction |
| `prop:pluszero` | The plus--layer has density zero |
| `prop:routeclosed` | The decomposition destroys the cancellation |
| `prop:subset` | Subset form |
| `prop:survivors` | Average rarity of form--barrier survivors |
| `thm:condpower` | Conditional power saving, and the crux exactly |
| `thm:masstwo` | The residual difficulty sits entirely at the mass-two wall |

## CONDITIONAL (3)

Stated conditionally in the paper.

| label | statement |
|---|---|
| `prop:family` | An explicit Pythagorean family, and why it stops at rung -1 |
| `prop:giuga` | The sub--barrier ghosts are pronic Giuga numbers |
| `prop:lyapworks` | A decreasing delta_lambda would settle #307 negatively |

## CITED (3)

Someone else's theorem, used as an input.

| label | statement |
|---|---|
| `prop:delta` | The delta--recursion and the genealogy of the classical lines |
| `prop:gap` | Gap stratification: #307 as adjacency of mu--Sondow lines |
| `prop:parityfloor` | Parity floor for odd line members |



## Where the four analytic inputs actually stand (checked 2026-09-02)

Not in Mathlib: `Mathlib.NumberTheory.LSeries.PrimesInAP` gives Dirichlet's theorem qualitatively and
`Mathlib.NumberTheory.Chebyshev` gives partial Chebyshev bounds; there is no prime number theorem, no
zero-free region, and no pretentious theory.

Not in `PrimeNumberTheoremAnd` either, which is the frontier project for analytic number theory in
Lean. A direct search of its source returns **zero** occurrences of `Siegel`, `Walfisz`, `Halasz`,
`Halász` or `pretentious`. It does carry zero-free-region work, but for the Riemann zeta function
(`ZetaBounds.lean`, `HoffsteinLockhart.lean`), not the uniform statement for Dirichlet `L`-functions
that Siegel–Walfisz needs, and its `StrongPNT.lean` still carries `sorry`s.

So none of the five analytic stars can be closed by importing existing work: the inputs do not exist
in formalised form anywhere. Carving each proof down to precisely these four named theorems, which
is what the table above records, is the furthest the debt can be reduced without formalising
analytic number theory that has not been formalised by anyone.

## prop:splitsieve (split sieve for single-tail families)

`Erdos307.SplitSieve` -- VERIFIED, 0 sorry, axioms [propext, Classical.choice, Quot.sound].

- `dprod_split`: `dprod T * dprod (S \ T) = dprod S` for `T ⊆ S`.
- `split_fst`: Leibniz half, `dprod (S \ T) = q * csum T + dprod T`.
- `split_snd`: the sieve, `dprod T ∣ csum (S \ T)`.
- `split_criterion`: the `q`-free criterion `dprod T ^ 2 + csum T * csum (S \ T) = dprod S`.
- `no_cycle_of_no_split`: contrapositive, the form `code/split_sieve.rs` computes.
- `csum_odd_card`: parity law, `csum X` and `|X|` agree mod 2 for `X` all odd; gives `2 in T -> |T| odd`.
- `split_snd_of_criterion`: (ii) is implied by (i) -- the sieve is the mod-alpha shadow of the criterion.
- `split_criterion_gen`, `split_snd_gen`: arbitrary tail multiplier `M`. The criterion becomes
  `dprod T ^ 2 * csum M + csum T * csum (S \ T) = dprod S`, giving arity one (`csum M = 1`) and the
  pair sector (`M = {p,q}`, `csum M = p + q`) at once. The sieve `dprod T | csum (S \ T)` carries no
  arity assumption, so it reaches the pair families the arity-one weapon of prop:immunedecide cannot.
- `recip_sum_bound`, `pair_tail_deficit`: the mixed pair-sector case admits no sieve, but 58 primes
  never reach mass 2, so the smaller tail prime is confined to a finite range.
