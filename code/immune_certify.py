#!/usr/bin/env python3
"""immune_certify.py — attempt rigorous primality certificates for the 34 immune families.

rem:campaign records 34 level-60 single-tail families in which A_S = N_S + 2 D_S and
B_S = N_S - 2 D_S are both Baillie-PSW probable primes; their immunity is therefore
labelled [C] (conditional), since BPSW is rigorous only in its COMPOSITE verdicts.

Upgrading to [P] needs primality CERTIFICATES. Without an ECPP implementation the
available route is Pocklington / Brillhart-Lehmer-Selfridge: factor n-1 as F * R with F
fully factored and gcd(F,R)=1; if F > n^(1/3) (BLS) the primality of n can be certified by
exhibiting a witness for each prime of F. This script measures how far partial
factorisation of A_S - 1 and B_S - 1 gets, i.e. whether the certificates are within reach
at all.

Method: enumerate the 49,961 admissible bases of prop:close59, find the 81 with A_S and B_S
both BPSW-prime, keep the 34 IMMUNE ones, those additionally satisfying (D_S | A_S) = +1
(the other 47 carry -1 and are already killed by reciprocity), then trial-divide n-1 to
3e6 and run bounded Pollard rho on BOTH sides, reporting log(F)/log(n) against the BLS
threshold 1/3 and taking the worse side, since immunity needs both A_S and B_S prime.

Earlier versions of this script diverged from the paper in three ways, all fixed here and all
found by external audit (REPRO-03): the Kronecker filter was missing, so `immune` held the 81
both-prime bases while being compared against the recorded 34; the trial-division limit was
1e6 against the paper's 3e6; and only A_S - 1 was factored, though the claim quantifies over
both sides.

Runtime: a few minutes (gmpy2). Deterministic; no randomness beyond fixed rho parameters.
"""
from fractions import Fraction
from math import log
import gmpy2
from gmpy2 import mpz, is_prime, gcd

# ---- primes to 800, the close59 setup -------------------------------------
N = 800
sieve = [True] * (N + 1); sieve[0] = sieve[1] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]:
        for j in range(i * i, N + 1, i): sieve[j] = False
primes = [i for i in range(2, N + 1) if sieve[i]]
T = lambda ps: sum(Fraction(1, p) for p in ps)
T58, T60 = T(primes[:58]), T(primes[:60])
forced = [p for p in primes if p <= 167]
pool = [p for p in primes if p > 167 and T58 + Fraction(1, p) > 2]
k = 59 - len(forced)
thr = 2 - T(forced)
pf = [Fraction(1, p) for p in pool]

bases = []
def dfs(i, need, cur, chosen):
    if need == 0:
        if cur > thr: bases.append(forced + [pool[j] for j in chosen])
        return
    if i + need > len(pool): return
    if cur + sum(pf[i:i + need]) <= thr: return
    dfs(i + 1, need - 1, cur + pf[i], chosen + [i])
    dfs(i + 1, need, cur, chosen)
dfs(0, k, Fraction(0), [])
print(f"admissible bases: {len(bases)} (expected 49961)")

# ---- both-prime bases, then the immune subset ------------------------------
both_prime, immune = [], []
for S in bases:
    D = mpz(1)
    for p in S: D *= p
    Nc = sum(D // p for p in S)
    A, B = Nc + 2 * D, Nc - 2 * D
    if is_prime(A) and is_prime(B):
        both_prime.append((S, A, B))
        # immunity also needs the reciprocity residue (D_S | A_S) = +1; the rest are killed
        if gmpy2.kronecker(D, A) == 1:
            immune.append((S, A, B))
print(f"bases with A_S, B_S both BPSW-prime : {len(both_prime)}  (paper: 81)")
print(f"of those, immune, (D_S|A_S) = +1    : {len(immune)}  (paper: 34)")
assert len(both_prime) == 81, f"both-prime count {len(both_prime)} != 81"
assert len(immune) == 34, f"immune count {len(immune)} != 34"

# ---- partial factorisation of n-1, and the BLS ratio -----------------------
def partial_factor(n, tdiv_limit=3 * 10 ** 6, rho_rounds=6):
    """return (F, factors) with F the fully-factored part of n found."""
    m = mpz(n); F = mpz(1); fs = []
    for p in range(2, tdiv_limit):
        if p * p > m and m > 1: break
        while m % p == 0:
            m //= p; F *= p; fs.append(p)
    # bounded Pollard rho on the remaining cofactor
    def rho(x, c, lim=200000):
        if x % 2 == 0: return mpz(2)
        y, d = mpz(2), mpz(1); xx = mpz(2)
        for _ in range(lim):
            xx = (xx * xx + c) % x
            y = (y * y + c) % x; y = (y * y + c) % x
            d = gcd(abs(xx - y), x)
            if d != 1: return d if d != x else None
        return None
    for c in range(1, rho_rounds + 1):
        if m == 1 or is_prime(m): break
        d = rho(m, c)
        if d and d != m:
            # keep only fully-identified prime pieces
            for piece in (d, m // d):
                pass
            if is_prime(d):
                while m % d == 0: m //= d; F *= d; fs.append(int(d))
    if m > 1 and is_prime(m):
        F *= m; fs.append(int(m)); m = mpz(1)
    return F, fs

print(f"\n{'#':>3} {'digits':>7} {'A ratio':>9} {'B ratio':>9} {'worse':>9} {'BLS 1/3':>8}")
certified = 0
for idx, (S, A, B) in enumerate(immune, 1):
    FA, _ = partial_factor(A - 1)
    FB, _ = partial_factor(B - 1)
    rA = log(FA) / log(A) if FA > 1 else 0.0
    rB = log(FB) / log(B) if FB > 1 else 0.0
    worse = min(rA, rB)          # immunity needs BOTH sides certified
    ok = worse > 1 / 3
    certified += ok
    print(f"{idx:>3} {len(str(A)):>7} {rA:>9.4f} {rB:>9.4f} {worse:>9.4f} {str(ok):>8}")
print(f"\nfamilies reaching the BLS threshold on both sides: {certified} of {len(immune)}")
print("Paper claims 0 of 34; the elementary route does not reach.")
print("The unconditional upgrade to [P] comes from APRCL instead: code/immune_prove.gp.")
