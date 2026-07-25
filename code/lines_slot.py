#!/usr/bin/env python3
"""Verify prop:lines + rem:minusslot — the determined slot on derivative lines,
and the coercive/degenerate dichotomy for the minus-square.

  On a line N' = eN + c, writing N = Mp with p = P+(N):  N' - eN = p(M' - eM) + M,
  so p = (c - M)/(M' - eM) is DETERMINED by M (no free root).  M' - eM != 0 always
  (sigma(M) = e integer would force D_M = 1 by rigidity/auto-lowest-terms).

Checks:
  1. determined slot on REAL classical data: PPN [2,6,42,1806,47058] on (e,c)=(1,-1)
     and Giuga [30,858,1722,66198] on (e,c)=(1,+1): formula p = (c-M)/(M'-eM) must
     reproduce P+(N) exactly. Also: on the stratum M'-M = -1 it reads p = M+1 (the
     classical oblong chain).
  2. E = M' - eM != 0 for ALL squarefree M <= 1e5 and e in {1,2,3} (rigidity, numeric).
  3. determined slot identically on slope-2 members: every squarefree N <= 1e5, omega>=2,
     with its own c := N'-2N: p_det == P+(N).
  4. exact threshold: 1/(2 - T58) = 794.2... => rough minus-hits (p > y >= 795) force
     sigma(base) >= 2 - 1/y > T58 => omega(base) >= 59.
  5. slope-2 lines at square heights are EMPTY <= 1e6 (= minus-hits empty; cor:emptytest).
  6. mod-8 line law: odd squarefree N, omega >= 2, c := N'-2N  =>  S(N) == cN + 2 (mod 8).
"""
from fractions import Fraction
from math import isqrt, gcd
from sympy import primerange

LIM = 10**6
spf = list(range(LIM + 1))
for i in range(2, isqrt(LIM) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j: spf[j] = i

def sqfree_factor(n):
    ps = []
    while n > 1:
        p = spf[n]; n //= p
        if n % p == 0: return None
        ps.append(p)
    return ps

def deriv(n):
    ps = sqfree_factor(n)
    return sum(n // p for p in ps)

# ---------- 1: classical lines ----------
print("1. determined slot on classical data:")
for name, e, c, members in (("PPN  (n'=n-1)", 1, -1, [2, 6, 42, 1806, 47058]),
                            ("Giuga (n'=n+1)", 1, 1, [30, 858, 1722, 66198])):
    ok = True
    for N in members:
        ps = sqfree_factor(N)
        assert deriv(N) == e * N + c, (name, N)
        if N == 2: continue                     # prime member: M=1 handled separately
        p = max(ps); M = N // p
        E = deriv(M) - e * M
        p_det, r = divmod(c - M, E)
        chain = f" [E=-1 stratum: p=M+1={M+1}]" if E == -1 else f" [E={E}]"
        line_ok = (r == 0 and p_det == p)
        ok &= line_ok
        print(f"   {name}: N={N} = M({M})*p({p}); formula p=({c}-{M})/({E}) = {p_det}"
              f"{chain}  {'OK' if line_ok else 'FAIL'}")
print()

# ---------- 2: E != 0 (rigidity) ----------
bad2 = 0
for M in range(2, 10**5 + 1):
    ps = sqfree_factor(M)
    if ps is None: continue
    d = sum(M // p for p in ps)
    for e in (1, 2, 3):
        if d == e * M: bad2 += 1
print(f"2. M'-eM != 0 for all squarefree M<=1e5, e in {{1,2,3}}: violations {bad2}")

# ---------- 3: determined slot identically (slope 2) ----------
bad3 = 0; n3 = 0
for N in range(6, 10**5 + 1):
    ps = sqfree_factor(N)
    if ps is None or len(ps) < 2: continue
    n3 += 1
    dN = sum(N // p for p in ps)
    c = dN - 2 * N
    p = max(ps); M = N // p
    dM = sum(M // q for q in sqfree_factor(M)) if M > 1 else 0
    E = dM - 2 * M
    if E == 0 or (c - M) % E or (c - M) // E != p: bad3 += 1
print(f"3. slope-2 determined slot p=(c-M)/E == P+(N) on {n3} squarefree N<=1e5: violations {bad3}")

# ---------- 4: threshold ----------
pr = list(primerange(2, 400))
T58 = sum(Fraction(1, p) for p in pr[:58])
thr = 1 / (2 - T58)
print(f"4. 1/(2-T58) = {float(thr):.1f}  => y >= {int(thr) + 1} forces omega(base) >= 59 "
      f"for every rough minus-hit  (T58 = {float(T58):.5f})")

# ---------- 5: minus-hits empty <= 1e6 ----------
cnt5 = 0
for N in range(6, LIM + 1):
    ps = sqfree_factor(N)
    if ps is None or len(ps) < 2: continue
    v = sum(N // p for p in ps) - 2 * N
    if v >= 0 and isqrt(v) ** 2 == v: cnt5 += 1
print(f"5. minus-hits (N'-2N = square >= 0) below 1e6: {cnt5}  (cor:emptytest predicts 0)")

# ---------- 6: mod-8 line law ----------
bad6 = 0; n6 = 0
for N in range(15, 10**5 + 1, 2):
    ps = sqfree_factor(N)
    if ps is None or len(ps) < 2: continue
    n6 += 1
    dN = sum(N // p for p in ps)
    c = dN - 2 * N
    if (sum(ps) - (c * N + 2)) % 8: bad6 += 1
print(f"6. mod-8 line law S(N) == cN+2 (mod 8), odd squarefree N<=1e5: {n6} tested, violations {bad6}")
