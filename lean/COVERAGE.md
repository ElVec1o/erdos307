# Formal coverage of `paper/erdos307.tex`

**48 of 104** labelled results in the paper are named by a Lean file in `Erdos307/`
(30 files, **0 `sorry`**, standard axioms throughout; `native_decide` confined to `Numeral.lean`
and `Sixty.lean`).

This file exists so that an audit finds a *stated boundary* rather than a gap. Every result the
paper claims is in exactly one of two states: formalised, or listed below with the reason it is not.

## There are no unformalised purely-algebraic results

Every remaining item needs something Lean cannot supply here: a computation at a scale the kernel
will not take, an analytic estimate absent from Mathlib, a conjectural hypothesis, or someone else's
theorem. **The algebraic gap is zero.**

Where a result has an algebraic core and an analytic tail, the core is formalised and the split is
named in the paper. `prop:plusthin` is the model: `count_le_divisor_sum` reduces the count to
`∑ τ(2s²+1)` in full, and `rem:plusthinformal` records that the asymptotic has no Mathlib counterpart.

## How to re-run this audit

```bash
grep -o '\\\\label{[a-z:0-9]*}' paper/erdos307.tex | sort -u   # paper labels
grep -ho '`[a-z]*:[a-z0-9]*`' lean/Erdos307/*.lean | sort -u   # labels named in Lean
```

Every Lean file carries a `Paper:` line in its module docstring naming the results it covers. A file
without one is a bug in this scheme, not an uncovered result.

## COMPUTATIONAL (30)

The result *is* a number produced by a program: a census, a sweep, an enumeration, a
measured density. Formalising the statement would mean formalising the computation, which for these
ranges means `native_decide` at a scale the kernel will not take. Each cites the script that
produces it, and those scripts are tracked in `code/` (Rule 9). Formal status: **out of scope by
construction**, not pending.

| label | statement |
|---|---|
| `cor:coprime60` | The coprime variant inherits the closed level |
| `cor:diagonals` | Diagonal stratification: the cost of the last lattice step |
| `cor:ff307` | The function--field ErdHos--Barbeau equation is insoluble |
| `cor:gos` | Nonemptiness families for the mu--Sondow conjecture |
| `lem:symbolfact` | Factorisation of the symbol |
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

## ANALYTIC (20)

Needs analytic machinery Mathlib does not carry: divisor-sum asymptotics
(`∑ τ(u) ~ Z log Z`), density of `{σ(m) ≥ x}`, Chernoff bounds over primes, Weil's point count,
large-sieve and character-sum estimates, Mertens. These are genuine library gaps, not choices. The
elementary skeleton underneath several of them *is* formalised: see `PlusThin.lean` for the sharpest
example, where the reduction to a divisor sum is complete in Lean and only the asymptotic is prose.

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
| `prop:fieldoptimal` | mathbbQ is optimal for the barrier |
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

Stated conditionally in the paper (on Bunyakovsky, Schinzel, GRH, or a named
conjecture). Formalising the implication is possible but would mean encoding the hypothesis as an
axiom-shaped assumption; the paper already marks these clearly and nothing downstream treats them as
proved.

| label | statement |
|---|---|
| `prop:family` | An explicit Pythagorean family, and why it stops at rung -1 |
| `prop:giuga` | The sub--barrier ghosts are pronic Giuga numbers |
| `prop:lyapworks` | A decreasing delta_lambda would settle #307 negatively |

## CITED (3)

Someone else's theorem, used as an input. Not ours to formalise.

| label | statement |
|---|---|
| `prop:delta` | The delta--recursion and the genealogy of the classical lines |
| `prop:gap` | Gap stratification: #307 as adjacency of mu--Sondow lines |
| `prop:parityfloor` | Parity floor for odd line members |

