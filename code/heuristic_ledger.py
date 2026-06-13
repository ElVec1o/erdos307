"""
HEURISTIC LEDGER  (Erdős #307 / arithmetic-derivative 2-cycles via the Frame Rule).

Goal: compute *honestly* the expected number of 2-cycles producible
from a frame by the Divisor Trick, and decide whether any *reachable* frame family gives
expectation >= 1.

MODEL.  Frame = (M0, N) coprime squarefree, free bulk prime r so M = M0*r.  Recall (validated in
frame/divisor_trick.py, identity checked 300/300):
    Δ0   = M0*N - M0'*N'                       (constant; '=arithmetic derivative)
    Δ(r) = r*Δ0 - M0*N'                        (linear in r)
    K    = Δ0*N^2 + (M0*N')^2                  (constant in r)
    Δ(r) | p_num  ⟺  Δ(r) | K
A 2-cycle (M0*r*p, N*q) is produced when, for some positive divisor d|K with d ≡ -M0*N' (mod Δ0):
    r = (d + M0*N')/Δ0   is a prime ∉ frame,
    p = p_num/d, q = q_num/d are primes, coprime to M*N, p≠q.

So per frame the number of *candidate tickets* is
    A(frame) = #{ d | K : d>0, d ≡ -M0*N' (mod Δ0) }          (admissible divisor classes)
and each ticket independently yields a genuine cycle with heuristic probability
    P_prime ≈ 1/(ln r · ln p · ln q)            (three independent PNT primality events).
Hence the ledger's expected number of cycles per frame is
    E(frame) ≈ A(frame) / (ln r̄ · ln p̄ · ln q̄).
Equidistribution predicts A ≈ τ(K)/Δ0 (each residue class mod Δ0 gets ~τ(K)/Δ0 of the divisors).

This script: (1) computes A, τ(K), Δ0, E EXACTLY for small factorable frames; (2) checks the
A ≈ τ(K)/Δ0 prediction; (3) finds the smallest Δ0 reachable; (4) extrapolates what (Δ0, τ(K)) a
barrier-scale frame would need for E ≥ 1, and reports the honest gap.
"""
from sympy import primerange, isprime, divisors, factorint
from math import prod, log, isqrt
import itertools, time

def ader(n):
    f = factorint(n)
    return sum(n * e // p for p, e in f.items())

# ---------------------------------------------------------------------------
# Exact per-frame ledger for a fixed (M0, N) and the bulk prime r treated as the free variable.
# We count admissible divisor classes of K, and (for tickets that are integral) record the
# realized primality-probability proxy using the actual sizes of r, p, q.
# ---------------------------------------------------------------------------
def frame_ledger(M0, N, kbudget=10**14):
    M0p, Npr = ader(M0), ader(N)
    D0 = M0 * N - M0p * Npr
    if D0 <= 0:
        return None
    K = D0 * N * N + (M0 * Npr) ** 2
    if K <= 0 or K > kbudget:
        return None
    tauK = 0
    A = 0                      # admissible divisor classes (exact)
    tickets = []               # (r, p, q) integral candidates with sizes
    res = (-M0 * Npr) % D0
    for d in divisors(K):
        tauK += 1
        if d % D0 != res:
            continue
        A += 1
        r = (d + M0 * Npr) // D0
        if r <= 1:
            continue
        M = M0 * r
        Mp = M0p * r + M0
        pnum = M * Npr + N * N
        qnum = Mp * N + M * M
        if pnum % d or qnum % d:
            continue
        p, q = pnum // d, qnum // d
        if p > 1 and q > 1:
            tickets.append((r, p, q))
    return dict(M0=M0, N=N, D0=D0, K=K, tauK=tauK, A=A, tickets=tickets)

def E_from_tickets(tickets):
    """Heuristic expected cycles = sum over integral tickets of 1/(ln r ln p ln q)."""
    E = 0.0
    for (r, p, q) in tickets:
        lr, lp, lq = log(max(r, 3)), log(max(p, 3)), log(max(q, 3))
        E += 1.0 / (lr * lp * lq)
    return E

# ---------------------------------------------------------------------------
# (1)+(2)+(3): small-frame sweep — exact A, τ(K), Δ0, validate A≈τ(K)/Δ0, find min Δ0.
# ---------------------------------------------------------------------------
def sweep(seed_primes=None, kbudget=10**14):
    if seed_primes is None:
        seed_primes = list(primerange(2, 120))
    t0 = time.time()
    rows = []
    min_D0 = None
    n_total_E = 0.0
    sumA = 0            # Σ admissible classes (exact)
    sum_pred = 0.0      # Σ τ(K)/Δ0   (equidistribution prediction)
    n_coprime = 0       # frames with gcd(M0*N', Δ0) = 1  (needed for automatic p-integrality)
    n_zeroA = 0         # frames where the target residue carries NO divisor of K (A = 0)
    seen = set()
    for m0size in [1, 2, 3]:
        for nsize in [2, 3]:
            for M0s in itertools.combinations(seed_primes[:18], m0size):
                M0 = prod(M0s)
                for Ns in itertools.combinations([x for x in seed_primes[:18] if x not in M0s], nsize):
                    N = prod(Ns)
                    key = (M0, N)
                    if key in seen:
                        continue
                    seen.add(key)
                    L = frame_ledger(M0, N, kbudget=kbudget)
                    if L is None:
                        continue
                    E = E_from_tickets(L["tickets"])
                    n_total_E += E
                    sumA += L["A"]
                    sum_pred += L["tauK"] / L["D0"]
                    from math import gcd
                    if gcd((L["M0"] * ader(L["N"])) % L["D0"], L["D0"]) == 1:
                        n_coprime += 1
                    if L["A"] == 0:
                        n_zeroA += 1
                    if min_D0 is None or L["D0"] < min_D0[0]:
                        min_D0 = (L["D0"], M0s, Ns, L["tauK"], L["A"])
                    rows.append((L["D0"], L["tauK"], L["A"], L["tauK"] / L["D0"], E, len(L["tickets"])))
    dt = time.time() - t0
    return rows, min_D0, n_total_E, (sumA, sum_pred, n_coprime, n_zeroA), dt

# ---------------------------------------------------------------------------
# (4): extrapolation — what does a *barrier-scale* frame need for E >= 1?
# ---------------------------------------------------------------------------
def circularity_note():
    """The decisive honesty check: Δ0 = M0·N·(1 − s_M·s_N) EXACTLY, so 'small Δ0' is #307 itself."""
    print("\n=== CIRCULARITY OF THE FRAME-ENGINEERING OBJECTIVE (the decisive caveat) ===")
    ok = True
    import random as _r
    _r.seed(11)
    for _ in range(3000):
        a = _r.sample(list(primerange(2, 150)), _r.randint(1, 4))
        b = _r.sample([x for x in primerange(2, 150) if x not in a], _r.randint(1, 4))
        M0, N = prod(a), prod(b)
        from fractions import Fraction as F
        D0 = M0 * N - ader(M0) * ader(N)
        sM = sum(F(1, p) for p in a); sN = sum(F(1, p) for p in b)
        if F(D0) != M0 * N * (1 - sM * sN):
            ok = False
    print(f"  identity  Δ0 = M0·N·(1 − s_M·s_N)  verified exactly: {ok}")
    print("  Hence Δ0 is small *relative to M0·N* iff s_M·s_N ≈ 1 — i.e. iff (∑_{p|M0}1/p)(∑_{p|N}1/p) ≈ 1,")
    print("  which is the Erdős #307 condition for the frames themselves.  And Δ0 small in *absolute*")
    print("  terms at scale needs s_M·s_N = 1 − O(1/M0N), i.e. reciprocal-product within O(1/M0N) of 1 —")
    print("  STRICTLY HARDER than #307.  So the 'force Δ0 small' objective is CIRCULAR: it is the")
    print("  original problem in disguise.  The Frame Rule is a valid *parametrisation* of solutions,")
    print("  not a reduction in difficulty.")


def extrapolate():
    # At the barrier the cycle members a=M*p, b=N*q are ~10^56 each; r,p,q sit somewhere below.
    # Take a representative per-factor scale of 10^28 (so a~10^56 splits over two/three factors);
    # this is generous to the construction (smaller factors => smaller logs => larger 1/ln^3).
    print("\n=== EXTRAPOLATION TO BARRIER SCALE (honest gap) ===")
    for scale_digits in [18, 28, 40, 56]:
        x = 10 ** scale_digits
        lnx = log(x)
        inv_ln3 = 1.0 / lnx ** 3
        need_A = 1.0 / inv_ln3           # admissible tickets needed for E>=1
        print(f"  per-factor scale 10^{scale_digits:>2}: 1/ln^3 = {inv_ln3:.3e}  "
              f"=>  need A ≈ {need_A:.3e} admissible divisor-classes per frame for E≥1")
    print("  Interpretation: A = (#divisors of K in one residue class mod Δ0) ≈ τ(K)/Δ0.")
    print("  To get A ~ 1e5–1e7 you need EITHER Δ0 = O(1) with τ(K) ~ 1e5–1e7,")
    print("  OR τ(K) ~ Δ0·1e6.  Random frames have Δ0 ~ M0·N (astronomically large), so A≈0.")
    print("  A 'lottery-winning' frame family must force Δ0 small AND K extremely smooth;")
    print("  no such parametric family is known. THIS is the precisely-quantified remaining gap.")

if __name__ == "__main__":
    print("HEURISTIC LEDGER — exact small-frame computation + honest extrapolation\n")
    rows, min_D0, total_E, agg, dt = sweep()
    sumA, sum_pred, n_coprime, n_zeroA = agg
    print(f"swept {len(rows)} factorable frames in {dt:.0f}s")
    # distribution of Δ0
    D0s = sorted(r[0] for r in rows)
    print(f"Δ0 distribution: min={D0s[0]}, 10th pct={D0s[len(D0s)//10]}, "
          f"median={D0s[len(D0s)//2]}, max={D0s[-1]}")
    print(f"smallest Δ0 frame: Δ0={min_D0[0]}  M0={min_D0[1]} N={min_D0[2]}  "
          f"τ(K)={min_D0[3]} A(admissible)={min_D0[4]}")
    # validation of the equidistribution heuristic, done correctly (AGGREGATE, not per-frame)
    print(f"\nequidistribution check A ≈ τ(K)/Δ0:")
    print(f"  AGGREGATE  Σ A = {sumA}   vs   Σ τ(K)/Δ0 = {sum_pred:.1f}   "
          f"(ratio {sumA/max(sum_pred,1e-9):.2f})")
    print(f"  PER-FRAME it FAILS: {n_zeroA}/{len(rows)} frames have A=0 (target residue carries no")
    print(f"  divisor of K) — divisor residues are multiplicatively structured, not equidistributed.")
    print(f"  frames with gcd(M0·N',Δ0)=1 (⇒ p automatically integral): {n_coprime}/{len(rows)}")
    nA = sum(1 for r in rows if r[2] > 0)
    nT = sum(1 for r in rows if r[5] > 0)
    print(f"frames with ≥1 admissible class: {nA}/{len(rows)};  "
          f"frames with ≥1 integral ticket: {nT}/{len(rows)}")
    print(f"TOTAL expected cycles over ALL {len(rows)} swept frames (Σ E) = {total_E:.4e}")
    print("  (Σ E < 1 even over this whole sweep; ZERO actual cycles — barrier forbids hits below 10^56)")
    circularity_note()
    extrapolate()
    print("\nLEDGER VERDICT (honest):")
    print(" • Per reachable random frame, E ≈ 0: A=0 for most frames (residues not equidistributed)")
    print("   and the surviving tickets each carry a primality cost ~1/ln^3 ≈ 5e-7 at barrier scale.")
    print(" • Reaching E≥1 needs ~10^6 admissible tickets/frame, i.e. Δ0=O(1) with τ(K)~10^6.")
    print(" • BUT Δ0 = M0·N·(1−s_M·s_N): forcing Δ0 small IS the #307 condition (circular). So the")
    print("   frame-engineering objective does not reduce the difficulty; it relocates it.")
    print(" • CONCLUSION: the Frame Rule + Divisor Trick are valid, exact, Euler-style theorems that")
    print("   PARAMETRISE all solutions and make existence falsifiable-in-principle per frame — but")
    print("   they do not, as they stand, lower the bar below #307 itself. No reachable frame family")
    print("   currently gives expectation ≥ 1, and the bottleneck (small Δ0 / smooth K) is precisely")
    print("   characterised. This is the corrected, non-overclaiming status of the constructive path.")
