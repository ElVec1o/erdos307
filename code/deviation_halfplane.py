#!/usr/bin/env python3
"""The deviation half-plane — census and verification.

For coprime squarefree a != b define the deviation pair, when integral,
    s = (a'-b)/a,   t = (b'-a)/b     (i.e.  a' = b + as,  b' = a + bt).
Both ladders are the lines t = -s (Pythagorean) and t = s (co-ladder); #307 is (0,0).

THEOREM (half-plane law):  sigma(ab) = a/b + b/a + s + t  >  2 + (s+t).
  => every integral stratum with s+t >= 0 is empty below the 59-prime barrier
     (omega(ab) >= 59, ab > 7.9e112);
  => strata with s+t <= -1 are unprotected, and indeed populated at tiny height.

CENSUS: all integral pairs with ab <= 1e7 (via the a | a'-b progression prefilter):
  record every populated stratum (s,t), its count and minimal ab; verify NO populated
  stratum has s+t >= 0 (the theorem's falsifiable prediction); tabulate the boundary
  line s+t = -1. Also: the (0,-1)-with-b=a' equation a'' + a' = a, censused to 1e7.
"""
from math import isqrt, gcd
from collections import defaultdict

LIM = 10**7
spf = list(range(LIM + 1))
for i in range(2, isqrt(LIM) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j: spf[j] = i

def sf_deriv(n):
    """derivative if squarefree else None"""
    if n > LIM: return None
    ps, m = [], n
    while m > 1:
        p = spf[m]; m //= p
        if m % p == 0: return None
        ps.append(p)
    return sum(n // p for p in ps)

# precompute derivatives up to 1e7 lazily via cache array (memory: use dict for sparse)
strata = defaultdict(lambda: [0, None])   # (s,t) -> [count, min ab]
bad_halfplane = 0
AMAX = 3163
for a in range(2, AMAX + 1):
    da = sf_deriv(a)
    if da is None: continue
    bmax = LIM // a
    b = da % a
    if b == 0: b = a
    while b <= bmax:
        if b != a and b > 1 and gcd(a, b) == 1:
            db = sf_deriv(b)
            if db is not None:
                s, r1 = divmod(da - b, a)
                t, r2 = divmod(db - a, b)
                if r1 == 0 and r2 == 0:
                    key = (s, t)
                    c = strata[key]
                    c[0] += 1
                    if c[1] is None or a * b < c[1]: c[1] = a * b
                    if s + t >= 0: bad_halfplane += 1
        b += a

print(f"integral-deviation pairs with ab <= 1e7 (a <= {AMAX}): "
      f"{sum(c[0] for c in strata.values())} in {len(strata)} strata")
print(f"pairs violating the half-plane law (s+t >= 0): {bad_halfplane}   <- theorem predicts 0")
print("\npopulated strata nearest the origin (by |s|+|t|):")
near = sorted(strata.items(), key=lambda kv: (abs(kv[0][0]) + abs(kv[0][1]), kv[1][1]))[:10]
for (s, t), (cnt, mn) in near:
    print(f"  (s,t)=({s},{t})  s+t={s+t}:  {cnt} pairs, min ab = {mn}")
print("\nboundary-adjacent line s+t = -1:")
line = sorted((kv for kv in strata.items() if kv[0][0] + kv[0][1] == -1), key=lambda kv: kv[1][1])[:8]
for (s, t), (cnt, mn) in line:
    print(f"  ({s},{t}): {cnt} pairs, min ab = {mn}")

# hand-verify the seed points
for (A, B) in ((6, 5), (5, 6)):
    da, db = sf_deriv(A), sf_deriv(B)
    print(f"\nseed ({A},{B}): a'={da} (=b+{(da-B)//A}a), b'={db} (=a+{(db-A)//B}b)  "
          f"stratum ({(da-B)//A},{(db-A)//B})")

# the a''+a'=a equation ((0,-1) stratum with b = a')
sols = []
for a in range(2, LIM + 1):
    da = sf_deriv(a)
    if da is None or da < 2: continue
    dda = sf_deriv(da)
    if dda is None: continue
    if dda + da == a:
        if gcd(a, da) == 1:
            sols.append(a)
print(f"\na'' + a' = a (squarefree chain, coprime): solutions <= 1e7: {sols}")
