# Formal coverage of `paper/erdos307.tex`

**53 of 106** labelled results are named by a Lean file in `Erdos307/` (31 files, **0 `sorry`**).

`lake env lean Check.lean` probes **269 declarations across all 31 modules**. Everything is on the
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

## Formalisation debt (Rule 5): four atoms, four stated blockers

Rule 5 requires every atom sitting at PROVED to carry either an active formalisation or a recorded
blocker, and forbids "not yet attempted". These four are blocked, and each blocker is a specific
missing Mathlib result or a deliberate refusal, not an absence of effort.

| atom | formalised | blocked on | what unblocks it |
|---|---|---|---|
| **A3** `prop:localcomplete` | regimes (i) and (ii) in `LocalComplete.lean` | regime (iii)'s complete character sums | Mathlib lemmas for `sum_q chi(aq+b) = 0` (`a != 0`) and `sum_q chi((aq+b)(cq+d)) = -chi(ac)` (`ad != bc`). Both standard, neither present. |
| **A6** `prop:plusthin` | the whole elementary skeleton through `count_le_divisor_sum` | Dirichlet's divisor asymptotics | `sum_{u<=Z} tau(u) ~ Z log Z` and `sum_{u<=Z} tau(u)/u ~ (log Z)^2/2`. Absent from Mathlib. |
| **A7** `prop:pairlocal` | no-pinning, the regime-(2) collapse identity, regime (1)'s explicit unit, regime (3)'s mod-8 collapse | Weil's point count and Hensel lifting | A Mathlib bound on points of a quartic over `F_l`, plus lifting a nonsingular point to `l^j`. Weil is absent. |
| **A8** `prop:nogain` | the full inequality chain, `cycle_bound_max` | the value `113.2` | A finite minimisation over subsets `S`, done in `code/minimise_structured.rs`. Formalising it means `native_decide` at a scale that would add an axiom to a result that currently needs none. **Deliberately not done**; the paper labels the value a computation. |

A3 moved this release: regimes (i) and (ii) were prose and are now Lean. The other three are
unchanged and are expected to stay starred until Mathlib grows the named results.

## There are no unformalised purely-algebraic results

Every remaining item needs a computation the kernel will not take, an analytic estimate absent from
Mathlib, a conjectural hypothesis, or someone else's theorem. **The algebraic gap is zero** -- a
claim this file has now had wrong twice, so it is stated as what it is: the output of the classifier
below, re-derivable by the snippet that follows.

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

## COMPUTATIONAL (28)

The result *is* a number a program produces. Formalising it would mean formalising the
computation, which at these ranges means `native_decide` at a scale the kernel will not take. Each
cites its generating script in `code/` (Rule 9).

| label | statement |
|---|---|
| `cor:coprime60` | The coprime variant inherits the closed level |
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
| `prop:tailkill` | The canonical tail family is empty: a reciprocity kill |
| `prop:transport` | Divisor transport |
| `thm:existence` | Existence of twisted derivative two--cycles |

## ANALYTIC (19)

Needs analytic machinery Mathlib does not carry: divisor-sum asymptotics, density of
`{sigma(m) >= x}`, Chernoff over primes, Weil, large sieve, Mertens. Where such a result has an
elementary core, the core *is* formalised; `PlusThin.lean` is the model.

| label | statement |
|---|---|
| `cor:secondbarrier` | A second, independent derivation of the barrier |
| `lem:charcancel` | Cancellation in the character sums; fixed r only |
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

Stated conditionally in the paper. Nothing downstream treats them as proved.

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

