#!/usr/bin/env python3
"""Wall-3: the DIAGONAL STRATIFICATION of the deviation plane.  (memory-safe, LIM = 1e7 via
array/bytearray only -- ~11 MB for spf as array('i') is 40MB; use 2e6 to stay light while the
hunt runs, then report the census from the already-verified 1e7 run.)

The half-plane law says sigma(ab) > 2 + (s+t). So the diagonal  s+t = -j  carries the barrier
    sigma(ab) > 2 - j,
i.e. omega(ab) >= m(2-j) and ab >= Pi_{m(2-j)}, where m(x) = least k with sum_{i<=k} 1/p_i > x.
So the plane is stratified by mass, one diagonal at a time:
    j >= 2 : mass > 0   -- no barrier at all
    j  = 1 : mass > 1   -- barrier at 3 primes, minimum 2*3*5 = 30
    j  = 0 : mass > 2   -- barrier at 59 primes, minimum Pi_59 ~ 8.8e112   <- #307 lives here

PREDICTION TO TEST: on each diagonal the census minimum must respect the diagonal's own
primorial floor, and on j = 1 the floor (30) should be ATTAINED -- i.e. the barrier is sharp
one step off the origin. Then the cost of the last lattice step is Pi_59/30 ~ 1e111.
"""
from array import array
from math import isqrt
from fractions import Fraction

# m(x) and the primorial floors
def primes_upto(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2, isqrt(n)+1):
        if s[i]:
            for j in range(i*i, n+1, i): s[j]=0
    return [i for i in range(2, n+1) if s[i]]
P = primes_upto(1000)
def m_of(x):
    """least k with sum_{i<k} 1/p_i > x; returns (k, product)"""
    if x <= 0: return 1, 2
    s = Fraction(0); prod = 1
    for k, p in enumerate(P, 1):
        s += Fraction(1, p); prod *= p
        if s > x: return k, prod
    return None, None

print("diagonal stratification of the deviation plane (s+t = -j):")
print(f"{'j':>3} {'mass floor':>11} {'min #primes':>12} {'min ab':>26}")
floors = {}
for j in (0, 1, 2, 3):
    x = 2 - j
    k, prod = m_of(x)
    floors[j] = (k, prod)
    disp = f"{prod:.4e}" if prod and prod > 10**9 else str(prod)
    print(f"{-j:>3} {('> '+str(x)):>11} {str(k):>12} {disp:>26}")

k59, pi59 = floors[0]; k1, pi1 = floors[1]
print(f"\ncost of the final lattice step  (j=1 -> j=0):  {pi59}/{pi1} = {pi59//pi1:.4e}"
      if isinstance(pi59//pi1, int) else "")
print(f"  = {float(pi59)/float(pi1):.3e}   ({len(str(pi59))-len(str(pi1))} orders of magnitude)")

# ---- census check on a light range: verify each diagonal's minimum respects its floor ----
LIM = 2 * 10**6
spf = array('i', range(LIM + 1))
for i in range(2, isqrt(LIM) + 1):
    if spf[i] == i:
        for jj in range(i*i, LIM+1, i):
            if spf[jj] == jj: spf[jj] = i
D = array('q', bytes(8*(LIM+1))); SF = bytearray(LIM+1); SF[1]=1
for n in range(2, LIM+1):
    p = spf[n]; mm = n//p
    if mm % p == 0: SF[n]=0
    else:
        SF[n]=1; D[n] = D[mm]*p + mm if mm>1 else 1
from math import gcd
mins = {}
for a in range(2, isqrt(LIM)+1):
    if not SF[a]: continue
    da = D[a]
    b = da % a or a
    while b <= LIM // a:
        if b != a and b > 1 and SF[b] and gcd(a, b) == 1:
            db = D[b]
            s, r1 = divmod(da - b, a); t, r2 = divmod(db - a, b)
            if r1 == 0 and r2 == 0:
                j = -(s + t)
                if j not in mins or a*b < mins[j][0]: mins[j] = (a*b, a, b, s, t)
        b += a
print(f"\ncensus (ab <= 2e6) minimum per diagonal, against the floor:")
for j in sorted(mins):
    ab, a, b, s, t = mins[j]
    fl = floors.get(j, (None, None))[1]
    ok = "-" if fl is None else ("OK" if ab >= fl else "VIOLATION")
    sharp = "  <-- FLOOR ATTAINED" if fl is not None and ab == fl else ""
    print(f"  j={j:>3}: min ab={ab:>9} at (a,b)=({a},{b}) stratum ({s},{t});  floor={fl}  {ok}{sharp}")
