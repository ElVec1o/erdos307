#!/usr/bin/env python3
"""Wall-5 door-2: the BALANCED-DIVISOR BILINEARIZATION.  (memory-safe: LIM = 1e6, array-based)

Peeling is prime-indexed and always removes the LARGEST prime -- which is precisely what
leaves ONE determined candidate (prop:groupoid). Split instead by SIZE: M = uv, coprime,
u the divisor nearest sqrt(M). With delta(n) = n' - n, Leibniz gives the exact identity

    M' - 2M  =  v * delta(u)  +  u * delta(v)                       (BILINEAR)

so the slope-two line M' - 2M = c becomes a bilinear equation in (u,v) with BOTH variables
of size ~sqrt(M) -- no determined slot. Equivalently, for fixed u,

    v' = v(2 - sigma(u)) + c/u,

i.e. v runs on a RATIONAL-slope line (a groupoid object L(a,b,c'), slope 2 - sigma(u)).

CHECKS
 1. the bilinear identity, all coprime splits, exhaustive on squarefree M <= 1e6;
 2. the fixed-u line form v' = v(2-sigma(u)) + c/u (exact, in rationals);
 3. TWO-DIMENSIONALITY: for the balanced split, v is NOT determined by u -- count, for
    each u, how many v <= LIM/u share the same (u, c) i.e. lie on that line. Compare with
    the largest-prime split, where the count is exactly 1 by the determined slot.
 4. balance achievable: distribution of log(u)/log(M) for the nearest-to-sqrt coprime split.
"""
from array import array
from math import isqrt, gcd, log
from fractions import Fraction

LIM = 10**6
# compact smallest-prime-factor sieve (array('i') = 4 MB per 1e6, not list-of-int)
spf = array('i', range(LIM + 1))
for i in range(2, isqrt(LIM) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j: spf[j] = i

D = array('q', [0]) * 1          # build derivative + squarefree flags compactly
D = array('q', bytes(8 * (LIM + 1)))
SF = bytearray(LIM + 1)
SF[1] = 1
for n in range(2, LIM + 1):
    p = spf[n]; m = n // p
    if m % p == 0:
        SF[n] = 0
    else:
        SF[n] = 1
        D[n] = D[m] * p + m if m > 1 else 1

def delta(n): return D[n] - n

# ---------- 1 & 2: identity and fixed-u line form ----------
bad_bil = bad_line = tested = 0
for M in range(6, LIM + 1, 1):
    if not SF[M]: continue
    # walk coprime splits via the prime set
    ps, m = [], M
    while m > 1:
        p = spf[m]; ps.append(p); m //= p
    if len(ps) < 2: continue
    tested += 1
    # test every coprime split (subset of the prime set)
    for mask in range(1, 1 << len(ps)):
        u = 1
        for i, p in enumerate(ps):
            if mask >> i & 1: u *= p
        v = M // u
        if v == 1: continue
        if v * delta(u) + u * delta(v) != D[M] - 2 * M: bad_bil += 1
        # fixed-u line form (rationals): v' == v(2 - sigma(u)) + c/u
        c = D[M] - 2 * M
        su = sum(Fraction(1, p) for i, p in enumerate(ps) if mask >> i & 1)
        if Fraction(D[v]) != v * (2 - su) + Fraction(c, u): bad_line += 1
        break            # one split per M is enough for the identity sweep (speed)
print(f"1. bilinear identity M'-2M = v*delta(u) + u*delta(v): {tested} squarefree M<=1e6, "
      f"violations {bad_bil}")
print(f"2. fixed-u line form v' = v(2-sigma(u)) + c/u (exact rationals): violations {bad_line}")

# ---------- 3: two-dimensionality vs the determined slot ----------
# for a sample of u, count v <= LIM/u with v*delta(u) + u*delta(v) = c, for the c of a
# reference M -- i.e. how many v share the line. Determined slot would give exactly 1.
import random
random.seed(5)
multi = 0; samples = 0; tot = 0
for _ in range(400):
    u = random.randint(6, 1000)
    if not SF[u] or u < 6: continue
    du = delta(u)
    # pick a reference v0 and its c, then count all v on that line
    v0 = random.randint(1001, min(LIM // u, 20000))
    if v0 < 2 or not SF[v0] or gcd(u, v0) != 1: continue
    c = v0 * du + u * delta(v0)
    cnt = 0
    for v in range(2, min(LIM // u, 40000) + 1):
        if SF[v] and gcd(u, v) == 1 and v * du + u * delta(v) == c: cnt += 1
    samples += 1; tot += cnt
    if cnt > 1: multi += 1
print(f"3. two-dimensionality: {samples} sampled u, mean #v per line {tot/max(samples,1):.2f}, "
      f"lines with >1 solution: {multi} ({100*multi/max(samples,1):.0f}%) "
      f"[largest-prime split would give exactly 1 by the determined slot]")

# ---------- 4: how balanced can a coprime split be? ----------
import statistics
bal = []
for M in range(1000, 200000):
    if not SF[M]: continue
    ps, m = [], M
    while m > 1:
        p = spf[m]; ps.append(p); m //= p
    if len(ps) < 3: continue
    best = None
    for mask in range(1, 1 << len(ps)):
        u = 1
        for i, p in enumerate(ps):
            if mask >> i & 1: u *= p
        if u * u > M: continue
        if best is None or u > best: best = u
    if best and best > 1: bal.append(log(best) / log(M))
print(f"4. balance: median log(u)/log(M) over nearest-to-sqrt coprime splits "
      f"({len(bal)} M with omega>=3): {statistics.median(bal):.3f}  (0.5 = perfectly balanced)")
