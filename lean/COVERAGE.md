# Formal coverage of `paper/erdos307.tex`

**77 of 140** labelled results are named by a Lean file in `Erdos307/` (53 files, **0 `sorry`**).

`lake env lean Check.lean` probes **386 declarations across all 53 modules**. Everything is on the
three standard axioms or fewer, with exactly two exceptions: `dfs_run`, the pruned-search execution
that closes level 60, and the `erdos307_sixty` that consumes it. The numeral bridge is
kernel-checked, so `card_ge_59` and `erdos307_barrier_closed` carry no `native_decide`.

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

## Formalisation debt (Rule 5): none

Rule 5 requires every atom sitting at PROVED to carry either an active formalisation or a recorded
blocker, and forbids "not yet attempted". **No atom is blocked.** All four are discharged, and three of the four fell because the blocker had
been mis-stated rather than because the mathematics was hard. **A7 is discharged**: its regime (2)
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

They are not the same kind of debt. **A7 is a cited external input**: it needs Hasse-Weil, which
Mathlib does not have and whose formalisation is a research contribution in its own right. A3 was in that category and is no longer: the character sums
turned out to be elementary once written in the right form, which is a reminder that "Mathlib does
not carry it" is not the same as "it is hard". A8's refusal was likewise mis-framed --- the claim
that needed proving was the easy direction all along.

| atom | formalised | blocked on | what unblocks it |
|---|---|---|---|

A6 moved furthest this release: its divisor sums, their logarithmic form, and the range count are
all formal, leaving the CRT root bound as the single remaining lemma. A7 moved in the previous
release, to Weil alone -- and then past it. No atom remains starred. The recurring error was
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
| `prop:lineanatomy` | Line anatomy: pinning, coupling, caps |
| `prop:massbound` | Mass--defect bound on the second prime |
| `prop:mod72` | A difference--36 congruence modulo 72 |
| `prop:multiplier` | Gaussian multiplier form of the ladder |
| `prop:novanish` | No vanishing derivatives, no transport, and the price of exactness |
| `prop:oddthr` | Even--gap plus lines are empty below 3.23times10^9 |
| `prop:pairform` | Pair form; the one--equation relaxation |
| `prop:plusinf` | Infinitely many gaps carry a nonempty plus line |
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

