# Computational scripts

Rust and PARI/GP, with a few legacy Python scripts from the earliest sessions. Every script is
standalone. All *verdicts* use exact integer/rational arithmetic; floating point is used only for
pre-screening, and where a float appears in a printed constant the exact form is given beside it.
Runtimes are approximate (a laptop).

This table documents the scripts the paper cites by name. `code/` (including the `hunt/` subdirectory, moved there from the repository root so that the layout matches the canonical one) holds 262 tracked files in total;
the remainder are supporting Rust and GP sources reachable from those, or superseded working
scripts, and are not individually documented here.

| Script | What it computes | Expected output | Time |
|---|---|---|---|
| `barrier.py` | The quantitative barrier (exact rationals). | `m0 = 59`; `min(∏P,∏Q) = D_P ≥ ~2.093×10⁵⁶`. | ~5 s |
| `tailkill.py` | Prop. tailkill: Jacobi-symbol kill of level-60 tail families (no factoring). | canonical family EMPTY; `31219`/`49961` bases killed, identity `(D|A)=(D|B)` universal. | ~10 s |
| `full_classify.py` | Definitive kill/immune/pending classification: fully factors the cofactors `survivor_kill.rs` leaves open (splitting the +1 (−1,−1) semiprimes the Jacobi symbol hides) and applies the per-prime Legendre kill. | reads `open_cofactors.txt`; validated: real kills recovered (e.g. base#11 prime 9376059154260675757). | fast |
| `close59.py` | Prop. close59: the complete list of 59-prime supports with `Σ1/p > 2`, each hit with the both-squares test (exact integers). | `49961` supports, `0` pass ⇒ `\|P∪Q\| ≥ 60`. | ~5 s |
| `exhaustive_search.py` | All prime sets `P` with `Σ1/p>1`, `∏P ≤ 10⁸`; forces `Q` and tests. | `1,075,419` sets, **0** solutions. | ~40 s |
| `bridge_equivalence.py` | Verifies `a′ = Σ a/p` for squarefree `a`, `gcd(a,a′)=1`, and #307 ⇔ 2-cycle. | three `True`s. | ~1 s |
| `parity_dichotomy.py` | The all-odd barrier and the parity identity `b′ ≡ ω(b) (mod 2)`. | `≥ 1412` odd primes, `min ~ 10²⁵¹⁹`; `True`. | ~2 s |
| `frame_rule.py` | Symbolic + numeric check of the Frame Rule (Rules 1 and 2). | `a′−b = 0`, `b′−a = 0`; no violations. | ~3 s |
| `divisor_trick.py` | The Euler-style divisor-trick identity + a small-frame sweep. | identity `True` (300/300); 0 cycles below the barrier. | ~1 s |
| `residue_census.py` | One-correction construction: residue census of `m = (−CB) mod g` + sweep above `r*`. | residue median `log₁₀(m/g) ≈ −0.31`; 0 solutions. | ≤ 12 min |
| `abundance_density_sieve.py` | Density of prime-abundant `n`, and exhaustive `n″=n` sieve to `2×10⁷`. | density `0.0420`; **no** `n″=n` with `n′≠n`. | ~30 s |
| `conditional_mass.py` | Conditional mass `M(a′)` vs required `1/s`, and the local congruence lemma. | `b=a′` squarefree 95%; `Pr[M ≥ 1/s] = 0/40920`; lemma `True`. | ~20 s |
| `heuristic_ledger.py` | Expected 2-cycles per frame; the `Δ₀ = M₀N(1−s_M·s_N)` circularity. | `Σ E < 1` over 223k frames; circularity identity `True`. | ~35 s |
| `function_field.py` | Arithmetic derivative over `𝔽_q[t]`: degree-drop ⇒ no cycles/fixed points. | degree-drop `True`, 0 fixed points, 0 cycles over `𝔽₂`(≤7)/`𝔽₃`(≤5)/`𝔽₅`(≤4). | ~10 s |
| `density_and_kcycles.py` | Erdős–Wintner density `δ`; k-cycle thresholds `m_k`; scale-corrected ledger. | `δ=0.0420`; `m₂=59`, `m₃=361139`; `log₁₀E<0` at all scales. | ~4 min |
| `gaussian_cycles.py` | Verifies the sixteen twisted derivative 2-cycles over `ℤ[i]` exactly (integer arithmetic). | all sixteen `b′ = a` closures confirmed; smallest at norm 16642/13725. | ~1 s |

## Notes
- `residue_census.py` anneals partitions of the first 72 primes; exact values vary slightly run to
  run, but the residue census (median ≈ −0.31, matching the uniform heuristic) is stable.
- `sympy.isprime` is proven-deterministic well above the scales used here.

## PARI/GP scripts (the Lyapunov refutation)

Run with `gp -q -f <name>.gp` (PARI/GP 2.17). All verdicts are exact rational or exact integer
arithmetic; floating point appears only in printed summaries.

| Script | What it computes | Expected output | Time |
|---|---|---|---|
| `lyap_refute.gp` | Searches for a counterexample to the Lyapunov criterion: forces `{2,3,5}` into `n'` via `w \| n' ⟺ Σ_{p\|n} p⁻¹ ≡ 0 (mod w)`, keeps `1 < σ(n) < 31/30`, and requires `n'` to factor completely. | witness `n` = primes in `[7,373]` less `{307,317,359}`. | ~2 min |
| `lyap_refute_verify.gp` | Independent exact verification of that witness: squarefreeness of `n` and `n'`, `gcd(n,n')=1`, `σ(n)=n'/n`, `σ(n)>1`, `σ(n')>σ(n)`, and `n''>n`. | all `YES`; `σ(n')=31/30`, `r=n''/n=1.03944`. | ~10 s |
| `ecpp_cofactor.gp` | Atkin–Morain certificate for the 141-digit cofactor `C = n'/30`, with `C` derived from the witness rather than transcribed. | `primecertisvalid: 1`, cert `N` equals `C`. | ~1 s |
| `rho_witness.gp` | Smallest fully factored witness with `σ(n)>1` and `σ(n')/σ(n)` above the threshold `1−1/(eU)`. | `n` = primes in `[5,163]`, ratio `0.787115`. | ~1 min |
| `rho_verify.gp` | Exact verification of that witness and of the resulting bound `1/(e(1−ρ)) ≥ 1.7281` against `U ≤ 1.250828`. | route refuted. | ~5 s |
| `nearmiss_construct.gp` | Drives the near-miss quantity `r(a)=σ(a)σ(a')` by construction rather than sweeping; every `r` printed is a rigorous lower bound. | `r ≥ 1.30` at 1694 digits. | ~3 min |

`region_shape.rs` (Rust, `rustc -O -o region_shape region_shape.rs`) measures the achievable region
`{(σ(n),σ(n'))}` over squarefree `n ≤ N` with `n'` squarefree: reproduces `max r = 0.5535` and the
danger-window maxima `0.548`, `0.484` of the near-miss and Lyapunov sections.
| `uniform_min_sweep.gp` | The minimum of `1 − √r/φ(r)` over odd squarefree `r ≥ 7` (`lem:charcancelunif`). | `0.515877` at `r = 15`; `c₃ = 0.133975`, `c₅ = 0.440983`. | ~1 s |
| `deficit_check.gp` | The finite-`X` deficit of `rem:charcancelsharp` at `r = 5`, under the correct normalisation (both sums over **all** `p ≤ X`). | `0.1399, 0.1401, 0.1402, 0.1402`; growth `0.440887 → c₅`. | ~30 s |
| `deficit_numeric.gp` | `lem:deficit` measured: density of `σ_p(m) ≡ 2` over squarefree `m ≤ 2×10⁶`, one prime and two. | ratios in `[0.988, 1.023]` and `[0.997, 1.057]`. | ~2 min |
| `wall_check.gp` | The wall that blocked `cor:a9rate` in the character-expansion route, before `lem:swdirect` removed it: `√r log L / L` at `r ≍ (log N)^{1/2}`. | `1.12, 6.24, 130.5, 1.9×10⁶` at `L = 5, 14, 28, 69`. | ~1 s |
| `inverse_phase_check.gp` | The inverse-phase prime sum of `rem:a9ceiling`: drift at fixed `p`, and `max_s|S|` against `√p`. | drift matches `−1/(p−1)`; `max_s|S| ≈ 1.0–1.35` flat while `√p` grows `3.6 → 44.8`. | ~4 min |
| `a9rate_consequences.sh` | Every place in the paper, README and this file that needed revisiting when `cor:a9rate` stopped being conjectural; kept because the same sweep is what any future label change needs. Paragraph-oriented, so a phrase split across a line break cannot hide. | 21 paragraphs flagged, each tagged with which pattern fired. | ~1 s |
| `sector_window.gp` | `prop:barthreshold` read as a sector bound: the window for `σ(a)` at each `\|U\|`, and `min K` for a few sectors `d`. | `\|U\|≤60 → [0.9260,1.0799]`; `d=2 → K=1413`. | ~20 s |
| `alpha_is_d.gp` | That the largest-prime reduction `a=qd, b=e` is `prop:tailbound`'s parametrisation at `α=d, β=e`: both defining relations vanish symbolically. | two `0`s. | ~1 s |
| `sector_general.gp` | That Bado's primary-pseudoperfect apparatus is general with `d-1 → d'`: the sector identity `de − d'e' = d²`, the defect recurrence, its terminal value, and the mass identity, symbolically. | four `0`s. | ~1 s |
| `sector_dprime.gp` | The sector barrier sharpened by the `d'`-exclusion, and its minimum over sectors. | min `= 60`, at `d = 15470` and others. | ~3 min |
| `sector42_znam_violations.gp` | The per-prime Znám conditions `∏_{s≠r} s ≡ −d²/d' (mod r)` in the `d=42` sector, tested on Bado's certifying maximiser. | violated at `r = 5, 13, 17, 19, 23`. | ~1 s |
| `sector42_znam_dp.rs` | Bado's residue dynamic programme with the Znám conditions at `5, 11, 13` adjoined (`rustc -O`). | `M_64`: `1.03032 → 1.02853`, still `≥ 42/41`. | ~6 s |
| `sector42_k64.gp` | Exact rational facts behind `prop:sector42`: at most two primes `> 1229` in a `64`-set, the phase windows, the terminal formula as an identity. | `S_61 + 3/1231 < 42/41` (margin `1.09e-5`); `0`. | ~1 s |
| `sector42_k64.rs` | `prop:sector42`: exhaustive, exact enumeration deciding `ω(e) = 64` in the `d = 42` sector; phase 1 (`≤ 1` prime `> 1229`), phase 2 (two). Dependency-free; checkpointed; `rustc -O`. | phase 1: `36,901,596,763` sets, `0`; phase 2: `166,213` sets, min `δ = 1.539e-6`, `0`. | 22 min / 5 s |
| `sector_kexclude.rs` | `prop:ppnsectors`: decides `ω(e) = k` in ANY sector `d` by the generalised forced-prime identity (`rustc -O`). Regression: reproduces the `d=42`, `k=64` phase-2 figures exactly. | `d=42,k=62`: `175`, `0`; `d=47058,k=54`: `41,654`, `0`; `d=2214502422,k=70`: `11,646`, `0`. | < 1 s each |
| `split_sieve.rs` | The split sieve for level-60 single-tail families: enumerates subsets `T` of the base with `|T| <= kmax`, applies the congruences of `prop:splitsieve` (ii), and runs the exact `q`-free criterion on every survivor. Progress, ETA, atomic checkpoints, resume. |
| `gen_bases.rs` | Generates the level-60 base list `bases.txt` that `split_sieve.rs` consumes: the 39 forced primes below 167 plus 20 from `(167, 787]`, kept when `T(S) > 2`. Pruning is on `f64` with a conservative slack, every surviving leaf is then tested exactly as `csum S > 2 * dprod S`, and the two Jacobi symbols `(D|A)`, `(D|B)` are computed in 512-bit integer arithmetic. 49,961 bases, 18,742 with both symbols not `-1`. Replaces a sympy script; the reproduction path is now Python-free. |
| `pair_bases.rs` | Enumerates the pair sector of level 60 (`prop:sectors`(ii)): 60-supports with `0 < T(U) - 2 < 1/max U`, equivalently `T(W u {p}) < 2` and `T(W u {q}) < 2`, which escape every single-tail family. The prune is `max W * (2 - T(W)) < 2`; `f64` bounds the branch, every leaf is tested exactly in 512-bit integers. 2,365,416 bases. `--split` re-keys each `(W, q)` as a 59-prime arity-one base in `split_sieve.rs` format (paper line: each pair support is an arity-one tail family with the largest element as tail); `--shard K/M` streams every M-th base so the 4 GB listing never has to exist. |
| `open_filter.rs` | Reduces the level-60 single-tail bases to those still open, reading a base list on stdin and applying the certificate of `prop:tailkill` directly: a prime `l` dividing `A_S` or `B_S` with `(D_S|l) = -1` empties the family for every tail prime. Trial division to `10^6`, Legendre by Euler's criterion, 512-bit integers. Of the 18,742 Jacobi survivors it kills 11,029 and keeps **7,713**, reproducing the count quoted in the paper from the certificate alone, with no factoring output. The residue to the 3,444 open families is the Pollard-rho stage, which this does not run, so the output is a superset. |
| `sector_at60.gp` | The sectors whose mass floor is exactly `\|P∪Q\| = 60`, with run parameters. | `250` at primes `≤ 47`/`ω ≤ 8`, all phase-1 decidable. | ~4 min |
| `sector_at60_list.rs` | Emits the at-60 sectors with run parameters at any prime and `ω` cap; the `47`/`8` family is a proper subset of the `59`/`10` one. | `250` and `1,533`; sweep clears all `1,533`, `0` survivors. | ~2 min + ~40 min sweep |
| `sector_floorlist.rs` | Emits sectors of a prescribed mass floor, with run parameters; used for the out-of-sample test of `conj:floorgap`. | target `60` at `47`/`8` gives `250` (regression); floors `61`–`68` give `271,132,168,120,140,118,123,86`. | ~1 min |
| `sector_minfloor.rs` | The minimum mass floor over sectors. | `60`, at `d = 2·3·7·23·41`, over `109,293` sectors. | ~2 min |
| `plushit_omega.rs` | Odd plus-hits with their `ω` and `t = #{p ≡ 3 mod 4}`; the evidence for `conj:plusomega`. | `137` below `10^6` (regression vs the b-file); `598` to `2×10^7`, `ω` even in all, `(ω,t) ∈ {(2,0),(4,1),(6,4)}`. | ~3 min |
| `plushit_inverted.rs` | `ω=2` plus-hits by inverting the search through `2(v′+2v)+1 = (2p+1)(2q+1)` and sieving `2r²+1` in `r`; cost `O(√N)` rather than `O(N)`. | reproduces the `1,787` below `3×10^8` exactly; `243,129` to `10^13` in 80 s, `0` violations of `p ≡ q ≡ 1 mod 4`. | 0.2 s at `3e8`, 80 s at `1e13` |
| `sector_at60_count.rs` | Counts the sectors whose mass floor is exactly `|P u Q| = 60`, for a prime cap and an `omega` cap. Factors `d'` completely (Pollard rho + Miller–Rabin); refuses if `d'` exceeds `2^64`. | `250` at `B=47, w<=8`; `1,533` at `59,10`; `16,234` at `71,12` — all three paper counts. | secs to ~1 h |
| `sector_phasecount.gp` | Prices every rung of the sector ladder (`prop:phasecount`): how many phases each `omega(e)` needs at a given truncation. | `d=2214502422`, `k=72` needs 2 phases; `d=42`, `k=66` needs 4. | ~1 min |
| `sector_kexclude.gp` | The generalised identity `ℓ(dR − d'R') = d'R + d²`, symbolic and exact-rational. | `0` symbolically; `0` violations at each sector. | ~2 s |
| `sector_size.rs` | How many prime sets the sector enumerator would test, by a counting DP over binned mass (`rustc -O`); calibrated on the real `k=64` run. | predicts `3.49e10` vs `3.69e10` actual; `k=66` needs `8.0e15` (~16 years). | ~1 min |
| `pairsector_count.rs` | The level-60 pair sector enumerated exactly: 59-subsets of the primes `< 1588` with `T(R) ∈ (2 − 1/max R, 2]` (`rustc -O`). | `18,234,653` bases, largest `max(R) = 1583`; stable over prune margins `0`–`1e-6`. | ~2 s |
| `pairsector_kill.rs` | The reciprocity certificate over level-60 bases (`rug`/GMP for the Jacobi symbol). Campaign mode is the regression. | campaign: `49,961`/`31,219`/`18,742`, matching the paper; pair: `18,234,653` bases, `10,457,149` killed (57.3%). | 50 s |
| `pairsector_factor.rs` | Trial-division stage over the pair-sector survivors: an odd-multiplicity `ℓ \| A` or `B` with `(D\|ℓ) = −1`. | to `10^6`: `4,580,243` of `7,777,504` killed; `3,197,261` open. | ~10 min |
| `pairsector_basefreq.rs` | Per-prime frequency over all pair-sector bases (the null), to test the survivor profile against. | `18,234,653` bases; profile monotonic in `p`. | ~1 min |
| `pairsector_verify.rs` | Integrity check on a survivor file: duplicate-free subset of its input, so a resume overlap can never drop an unkilled family. | rho output `3,013,379` open, clean subset of `3,197,261`. | ~10 s |
| `immune_decide.gp` | Decides the `34` level-60 immune families outright (`prop:immunedecide`): `A_S` prime gives two candidate tail primes by Tonelli–Shanks. Self-contained. | all `34` EMPTY [P]. | ~20 min |
| `lvl60check.gp` | Verifies every arithmetic claim of `prop:lvl60factor` over all `49,961` admissible level-60 bases, enumerated from scratch. | `A` odd, `gcd(A,D)=1`, `114` digits, `sigma` in `(2, 2.00235]`, `max x/A = 0.569815 < 1`. | ~6 min |
| `batchgcd.gp` | Bernstein batch GCD over the hard cofactors of `A_S` across the level-60 residual: do any two share a factor? | `2` of `6,972`, both 7-digit. The residual is pairwise coprime at the wall. | ~7 min |
| `pairsector_parity.gp` | That `T(R) ≠ 2` for an odd-size squarefree base, so the tail is always bounded. | `N` odd in `30,000`/`30,000`. | ~5 s |
| `pairsector_countdp.rs` | Independent binned counting DP corroborating the above (`rustc -O`). | `1.8e7` at bin `3e-7`. | ~20 s |
| `sigma_gap.gp` | How close `σ(a)` comes to `1`, both sides, by the greedy Sylvester construction. | `1 − σ = 7.8e-592`, `σ − 1 = 4.6e-591` at `ω = 12`. | ~2 s |
| `sector_tight.gp` | The sectors where the `d'`-bound is tight. An earlier version filtered to `σ(d) < 1` and undercounted; corrected. | `877` sectors with `\|U\| ≤ 61` from primes `≤ 47` (`475` of them with `σ(d) > 1`); min `60`. | ~10 min |

| `reproduce.sh` | Single entry point (Rule 9): regenerates everything the paper cites. | see the script. | ~12 min |
| `close59_minus.rs` | Independent confirmation of `prop:close59` via the minus square `(a−b)² = N′−2N`, split-free by CRT; the paper's own verification uses the plus square. | `49,961` supports, `0` perfect squares, 1.8 s. | ~2 s |
| `install_hooks.sh` | Installs the tracked git hooks into `.git/hooks`. | `installed .git/hooks/pre-commit`. | instant |
| `hooks/pre-commit` | Refuses any commit that leaves the repo inconsistent (Rule 11). Exists because a shell chain runs `git commit` regardless of the gate's exit status, and did: `v1.46.0` was pushed with a stale PDF. Bypass with `--no-verify`. | refuses a deliberately broken README. | ~2 min per commit |
