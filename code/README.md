# Computational scripts

Python 3 with `sympy` and `numpy`. Every script is standalone (`python3 <name>.py`). All *verdicts*
use exact integer/rational arithmetic; floating point is used only for pre-screening. Runtimes are
approximate (a laptop).

| Script | What it computes | Expected output | Time |
|---|---|---|---|
| `barrier.py` | The quantitative barrier (exact rationals). | `m0 = 59`; `min(∏P,∏Q) = D_P ≥ ~2.093×10⁵⁶`. | ~5 s |
| `tailkill.py` | Prop. tailkill: Jacobi-symbol kill of level-60 tail families (no factoring). | canonical family EMPTY; `31219`/`49961` bases killed, identity `(D|A)=(D|B)` universal. | ~10 s |
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
