# Rust enumerators — derivative cycles over ℤ and the number rings

Self-contained Rust programs (no dependencies; `rustc -O -o NAME NAME.rs`) behind the computational
claims of the note that go beyond the Python scripts. Each prints live progress with ETA, runs a
startup self-test, and writes exact certificates to its `*_hits.txt`. All reported hits were
re-verified independently in Python before entering the paper.

| Program | Question | Headline result |
|---|---|---|
| `gos_hunt.rs` | Members of the µ-Sondow lines µ = −145, +673 (the two open instances of Grau–Oller-Marcén–Sadornil Conj. 1(ii)). | none with prime-factor cofactor ≤ 10¹¹; both instances remain open, frontier moved 10¹⁰ → 10¹¹. |
| `gauss_hunt.rs` | Derivative 2-cycles over `ℤ[i]` (Mode 1 standard; Mode 2 unit-twisted). | 16 twisted cycles ≤ norm 2×10⁷ (smallest 16642/13725); canonical system empty to norm 2×10⁹. |
| `stable_hunt.rs` | Conjugation-stable Gaussian cycles, via the descended `ℤ`-operator `D(m)`. | none to m ≤ 10⁹ (Gaussian norm 10¹⁸); the descent target stays open. |
| `ladder_hunt.rs <1\|2\|3>` | Cycles over `ℤ[i]` / `ℤ[√−2]` / `ℤ[ω]` — the unit-group ladder. | populations 56 / 14 / 278 ≤ norm 2×10⁷; the phase law, plus the anti-holomorphic cycle. |
| `real_hunt.rs` | Cycles over `ℤ[√2]` — the real-quadratic (infinite-unit) rung. | 30,204 cycles ≤ 2×10⁷ (vs 14/56/278 imaginary); minimal cycle at norms (46,49); the fully rational pair D(3707)=1547, D(1547)=3707; canonical empty to 2×10⁹. |
| `tail_sweep.rs` | Level-60 tail family `U = first-59 ∪ {q}`: sweeps `q ≡ 5 (mod 8)` (other classes proven impossible mod 8 at startup) for the both-squares condition; resumable with autosave. | no tail solution with q ≤ 10¹² (now subsumed by Prop. tailkill: the family is empty for every q). |
| `survivor_kill.rs` | Factoring attack (trial + Brent rho on a Montgomery bignum core) on the 18,742 Jacobi-inconclusive tail families; coprime-basis kill certificates, no primality testing needed. | 14,830 of 18,742 killed (rho budget 3e5/side) ⇒ **46,049/49,961 (92.2%)** of level-60 one-new-prime families proven empty; 3,912 open. |
| `close60.rs [K]` | Direct search for a level-60 #307 solution: all 60-sets with support in the first K primes and T>2, both-squares tested. | K=68: 1,258,448 sets, **0** pass the plus-square ⇒ no level-60 solution with max prime ≤ 337. |
| `close59.rs` | Independent verification of Prop. close59 (own bignum, enumeration order opposite to `code/close59.py`). | all 49,961 admissible 59-prime supports fail the both-squares test ⇒ any solution has \|P∪Q\| ≥ 60. ~2 s. |

`*_hits.txt` hold the certificates; `*.log` are sample run logs. Compiled binaries are committed for
convenience and rebuild from source in seconds. Typical deep runs (and the verifying Python) are
documented in the project's session record.

Example:

```
rustc -O -o gauss_hunt gauss_hunt.rs
./gauss_hunt 200000000 4000000 | tee gauss_run.log
```
