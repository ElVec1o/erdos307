#!/usr/bin/env python3
"""The co-ladder / arithmetic Riccati equation — verification.

Extend ' to Q by the quotient rule: (a/b)' = (a'b - ab')/b^2.

CLAIMS:
 (1) EQUIVALENCE: for coprime squarefree a != b, TFAE:
     [R] u = a/b satisfies u' = 1 - u^2  (arithmetic Riccati)
     [W] a'b - ab' = b^2 - a^2           (Wronskian form)
     [L] exists k in Z: a' = b + ak  AND  b' = a + bk   (the CO-ladder: same sign!)
     Identity behind [W]<=>[L]:  a'b - ab' - (b^2-a^2) = ab(k1 - k2),
     k1 = (a'-b)/a, k2 = (b'-a)/b.  And k CANCELS in u' (the Riccati form is k-free).
 (2) POSITIVITY: on the co-ladder k >= 0 (if k <= -1, WLOG a<b gives b' <= a-b < 0).
     Hence sigma(a)+sigma(b) = a/b + b/a + 2k > 2  =>  omega(ab) >= 59, ab > 7.9e112:
     the co-ladder is EMPTY at every reachable scale — by positivity, not the minus-square.
     Exhaustive check: no co-ladder pair with ab <= 1e7.
 (3) CONTRAST with the Pythagorean ladder (a' = b+ak, b' = a-bk): opposite sign; there
     a'^2+b'^2 = (k^2+1)(a^2+b^2); here a'^2+b'^2 = (k^2+1)(a^2+b^2) + 4kab.
     Multiplier forms: antisym Dz = (k+i) zbar;  sym Dz = k z + i zbar.  #307 = both k = 0.
 (4) GAUSSIAN PROBE: over Z[i] (canonical primes, pi' = 1) the positivity argument dies.
     Small census of co-ladder points b = a' - ak with b' = a + bk.
"""
from math import isqrt, gcd
from fractions import Fraction
from sympy import symbols, simplify, factorint, I, expand

# ---------- symbolic identities ----------
a, b, ap, bp, k = symbols('a b ap bp k', positive=True)
k1 = (ap - b) / a
k2 = (bp - a) / b
print("identity  a'b - ab' - (b^2-a^2) - ab(k1-k2) =",
      simplify(ap*b - a*bp - (b*b - a*a) - a*b*(k1 - k2)))
# k cancels in u' on the co-ladder:
u_num = (b + a*k)*b - a*(a + b*k)          # a'b - ab' with co-ladder substitution
print("k-cancellation: (a'b-ab')|_L - (b^2-a^2) =", simplify(expand(u_num - (b*b - a*a))))
# norm identities
sym = expand((b + a*k)**2 + (a + b*k)**2 - ((k*k+1)*(a*a+b*b) + 4*k*a*b))
anti = expand((b + a*k)**2 + (a - b*k)**2 - (k*k+1)*(a*a+b*b))
print("norm identities (sym with +4kab / antisym without):", simplify(sym), simplify(anti))

# ---------- exhaustive Z-side: no co-ladder points with ab <= 1e7 ----------
LIM = 10**7
spf = list(range(3163 + 1))
for i in range(2, 57):
    if spf[i] == i:
        for j in range(i*i, 3164, i):
            if spf[j] == j: spf[j] = i

def deriv_sf(n, cache={}):
    if n in cache: return cache[n]
    ps, m = [], n
    while m > 1:
        p = m if all(m % q for q in range(2, isqrt(m)+1)) else next(q for q in range(2, isqrt(m)+1) if m % q == 0)
        if (m // p) % p == 0: cache[n] = None; return None
        ps.append(p); m //= p
    d = sum(n // p for p in ps)
    cache[n] = d
    return d

hits = 0; checked = 0
for A in range(2, 3163):                      # a <= sqrt(1e7)
    da = deriv_sf(A)
    if da is None: continue
    # co-ladder needs a | a'-b: b == da (mod A), b > A, ab <= LIM, gcd=1
    start = da % A
    if start <= A: start += A * ((A - start)//A + 1)
    for B in range(start, LIM // A + 1, A):
        if gcd(A, B) != 1: continue
        db = deriv_sf(B)
        if db is None: continue
        checked += 1
        kk1, r1 = divmod(da - B, A)
        kk2, r2 = divmod(db - A, B)
        if r1 == 0 and r2 == 0 and kk1 == kk2:
            hits += 1
            print("  CO-LADDER POINT:", A, B, kk1)
print(f"Z-side: coprime squarefree pairs with a|a'-b, ab<=1e7: {checked} candidates, "
      f"co-ladder points: {hits}  (positivity barrier predicts 0)")

# ---------- Gaussian probe ----------
def gprimes(maxnorm):
    """canonical first-quadrant Gaussian primes (x>0, y>=0), norm <= maxnorm"""
    out = []
    for x in range(1, isqrt(maxnorm)+1):
        for y in range(0, isqrt(maxnorm - x*x + 1)+1):
            n = x*x + y*y
            if n < 2 or n > maxnorm: continue
            z = complex(x, y)
            # prime iff norm prime, or y==0 and x prime == 3 mod 4
            from sympy import isprime
            if y == 0:
                if isprime(x) and x % 4 == 3: out.append((x, 0))
            elif isprime(n): out.append((x, y))
    return out

def gmul(u, v): return (u[0]*v[0]-u[1]*v[1], u[0]*v[1]+u[1]*v[0])
def gadd(u, v): return (u[0]+v[0], u[1]+v[1])
def gsub(u, v): return (u[0]-v[0], u[1]-v[1])
def gnorm(u): return u[0]*u[0]+u[1]*u[1]
def gdiv(u, v):
    n = gnorm(v)
    x = u[0]*v[0]+u[1]*v[1]; y = u[1]*v[0]-u[0]*v[1]
    if x % n or y % n: return None
    return (x//n, y//n)

GP = gprimes(200)
from itertools import combinations
cands = 0; ghits = []
for r in (2, 3):
    for combo in combinations(GP, r):
        A = (1, 0)
        for pz in combo: A = gmul(A, pz)
        if gnorm(A) > 4*10**5: continue
        # a' = sum a/pi  (pi' = 1 canonical)
        Ap = (0, 0)
        for pz in combo: Ap = gadd(Ap, gdiv(A, pz))
        for kx in range(-4, 5):
            for ky in range(-4, 5):
                K = (kx, ky)
                B = gsub(Ap, gmul(A, K))
                nb = gnorm(B)
                if nb < 2 or nb > 4*10**5: continue
                # factor B via norm; require squarefree, coprime to A, canonicalizable
                fb = factorint(nb)
                # build Gaussian factorization of B
                import sympy
                rem = B; gps = []; ok = True
                for p, e in fb.items():
                    if p % 4 == 3:
                        if e % 2: ok = False; break
                        for _ in range(e//2):
                            d = gdiv(rem, (p, 0))
                            if d is None: ok = False; break
                            rem = d; gps.append((p, 0))
                    else:
                        # split or ramified: find gaussian prime divisors
                        for _ in range(e):
                            done = False
                            for gp in GP:
                                if gnorm(gp) == p:
                                    d = gdiv(rem, gp)
                                    if d is not None:
                                        rem = d; gps.append(gp); done = True; break
                                    # try conjugate-class rep via unit twists
                                    for ut in ((0,1),(-1,0),(0,-1)):
                                        d = gdiv(rem, gmul(gp, ut))
                                        if d is not None:
                                            rem = d; gps.append(gp); done = True; break
                                    if done: break
                            if not done: ok = False; break
                        if not ok: break
                if not ok or len(set(gps)) != len(gps): continue
                if any(g in combo for g in gps): continue     # coprime to a
                cands += 1
                # b' = unit * sum(canonical/pi): rem is the residual unit
                Bp = (0, 0)
                canonB = (1, 0)
                for g in gps: canonB = gmul(canonB, g)
                for g in gps: Bp = gadd(Bp, gdiv(canonB, g))
                Bp = gmul(rem, Bp)            # unit rule (u x)' = u x'
                target = gadd(A, gmul(B, K))
                if Bp == target:
                    ghits.append((A, B, K))
print(f"Gaussian probe: {cands} squarefree-coprime candidates scanned, "
      f"co-ladder points found: {len(ghits)}")
for h in ghits[:8]: print("   GAUSSIAN CO-LADDER:", h)
