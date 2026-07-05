#!/usr/bin/env python3
"""full_classify.py — definitive kill/immune classification of the level-60
single-tail sector of Erdős #307, finishing what the reciprocity + rho pass leaves open.

Background (Prop. tailkill / Rem. campaign).  A level-60 tail family with base S is
empty for every tail prime q iff some prime ℓ | A_S·B_S of ODD multiplicity has
Legendre (D_S|ℓ) = −1  (A_S = N_S + 2D_S, B_S = N_S − 2D_S).  The Jacobi symbol
(D_S|A_S) detects this only up to parity: (D_S|A_S) = +1 means an EVEN number of −1
primes, which is NOT immunity — two −1 primes still kill.  hunt/survivor_kill.rs peels
A_S, B_S with rho / p−1 and applies the kill rule per found prime, but it leaves each
unfactored cofactor as a single piece and tests only its Jacobi symbol; a cofactor that
is a product of two −1 primes therefore slips through as "open".

This script closes that gap.  It reads the residual cofactors that survivor_kill.rs dumps
to `open_cofactors.txt`, FULLY factors each (SymPy: trial + rho + p−1 + ECM — the
cofactors are typically ~30–40 digits after the Rust peel, so this is fast), and applies
the per-prime kill rule.  Each still-open family becomes exactly one of:

  * KILLED  — an odd-multiplicity prime with (D_S|·) = −1 turned up on splitting a
              +1 cofactor  (certificate: the prime and the side);
  * IMMUNE  — every cofactor factors with all odd-multiplicity primes giving +1: by the
              completeness lemma the family admits NO tail congruence obstruction, for any
              q  (a theorem about the family, not a search limit);
  * PENDING — a cofactor did not factor within the time budget (the true factoring frontier).

Requires `open_cofactors.txt` from a run of the updated survivor_kill.rs (which emits
`OPEN base#… sel=[…] pieces: <decimal>^<mult>@<A|B> …`).  Resumable; Ctrl-C safe.

Usage:  python3 full_classify.py [open_cofactors.txt] [timeout_per_cofactor_s=25]
"""
import sys
import os
import re
import time
import signal
from sympy import primerange, factorint

SRC = sys.argv[1] if len(sys.argv) > 1 else "open_cofactors.txt"
TIMEOUT = int(sys.argv[2]) if len(sys.argv) > 2 else 25
STATE, KILLS, IMMUNE, PEND = "classify_state.txt", "classify_kills.txt", "classify_immune.txt", "classify_pending.txt"


class Timeout(Exception):
    pass


signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(Timeout()))

forced = [p for p in primerange(2, 168)]
Dforced = 1
for p in forced:
    Dforced *= p


def legendre(a, p):
    r = pow(a % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else (1 if r == 1 else 0)


def factor_budget(x, budget):
    signal.setitimer(signal.ITIMER_REAL, budget)
    try:
        return factorint(x)
    except Timeout:
        return None
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


LINE = re.compile(r"OPEN base#(\d+) sel=\[([0-9,\s]+)\] pieces:(.*)")
PIECE = re.compile(r"(\d+)\^(\d+)@([AB])")


def main():
    if not os.path.exists(SRC):
        sys.exit(f"missing {SRC}: run the updated hunt/survivor_kill.rs first (it dumps the residual cofactors).")
    lines = [l for l in open(SRC) if l.startswith("OPEN base#")]
    print(f"{len(lines)} open families with dumped cofactors in {SRC}", flush=True)
    print(f"(per-family progress below; each hard cofactor may take up to {TIMEOUT}s)", flush=True)
    if not lines:
        sys.exit(f"\nNO 'OPEN base#…' lines in {SRC} — the Rust didn't dump cofactors.\n"
                 f"Check with:  grep -c '^OPEN base#' {SRC}\n"
                 f"If that's 0, the survivor_kill run that produced it predates the dump patch — rerun the current binary.")

    start = killed = immune = pending = 0
    if os.path.exists(STATE):
        d = dict(kv.split("=") for kv in open(STATE).read().split() if "=" in kv)
        start, killed, immune, pending = (int(d.get(k, 0)) for k in ("next", "killed", "immune", "pending"))
        print(f"resuming at open #{start}")

    t0 = time.time()
    for i in range(start, len(lines)):
        m = LINE.match(lines[i].strip())
        if not m:
            continue
        base_id = m.group(1)
        sel = [int(x) for x in m.group(2).split(",")]
        D = Dforced
        for p in sel:
            D *= p
        pieces = PIECE.findall(m.group(3))
        verdict = ("IMMUNE", None, None)
        for dec, mult, side in pieces:
            sys.stderr.write(f"\r  #{i+1}/{len(lines)}  side {side}: factoring {len(dec)}-digit cofactor…   "
                             f"[killed={killed} immune={immune} pending={pending}]        ")
            sys.stderr.flush()
            fd = factor_budget(int(dec), TIMEOUT)
            if fd is None:
                verdict = ("PENDING", None, None)
                continue
            hit = next((p for p, e in fd.items()
                        if (e * int(mult)) % 2 == 1 and legendre(D, p) == -1), None)
            if hit is not None:
                verdict = ("KILLED", side, hit)
                break
        tag = verdict[0]
        if tag == "KILLED":
            killed += 1
            open(KILLS, "a").write(f"KILL base#{base_id} side={verdict[1]} prime={verdict[2]}\n")
        elif tag == "PENDING":
            pending += 1
            open(PEND, "a").write(f"PENDING base#{base_id}\n")
        else:
            immune += 1
            open(IMMUNE, "a").write(f"IMMUNE base#{base_id}\n")

        el = time.time() - t0
        eta = (len(lines) - i - 1) / max((i + 1 - start) / max(el, 1e-9), 1e-9)
        sys.stderr.write(f"\r  {i+1}/{len(lines)}  killed={killed} immune={immune} pending={pending}  "
                         f"{el/max(i+1-start,1):.1f}s/family  ETA {eta/60:.0f} min      ")
        sys.stderr.flush()
        if (i + 1) % 10 == 0 or i + 1 == len(lines):
            open(STATE + ".tmp", "w").write(f"next={i+1} killed={killed} immune={immune} pending={pending}")
            os.replace(STATE + ".tmp", STATE)
    sys.stderr.write("\n")

    print("\n=== residual open families, fully classified ===")
    print(f"  newly KILLED by splitting +1 cofactors: {killed}")
    print(f"  provably IMMUNE (no tail congruence obstruction, any q): {immune}")
    print(f"  PENDING (cofactor unfactored in {TIMEOUT}s): {pending}")
    tot = 31219  # reciprocity kills; add the rho/p-1 kills from survivor_kill_results.txt separately
    print(f"\nAdd `killed` here to the survivor_kill totals for the final single-tail sector count.")
    if pending == 0:
        print("No PENDING: every dumped family is now KILLED or provably IMMUNE — the sector is fully classified.")


if __name__ == "__main__":
    main()
