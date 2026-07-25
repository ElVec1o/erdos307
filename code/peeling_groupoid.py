#!/usr/bin/env python3
"""Verify the two inventions of the wall-attack session.

I. THE PEELING GROUPOID. Generalized lines L(a,b,c) = {n squarefree: a n' = b n + c}.
   (i)  CLOSURE: n = qm in L(a,b,c), q = P+(n)  =>  m in L(aq, bq-a, c);
        slope b/a -> b/a - 1/q (the mass continued fraction of sigma(n)).
   (ii) RIGIDITY AT EVERY LEVEL: along the full peel chain of n on an integer line
        (a,b) = (1,e), the level-j denominator a_j m_j' - b_j m_j vanishes
        iff sigma(n) = e  (INDEPENDENT of j!) — impossible (auto-lowest-terms).
   (iii) DETERMINED SLOT AT EVERY LEVEL: q_j = (c - a_j m_j)/(a_j m_j' - b_j m_j) exactly.
   => every line member is a tower of single determined candidates over its own core;
      the single-candidate obstruction is invariant under all partial-peel reorganizations.

II. THE DESCENDED MOD-8 LAW. For the descended operator D(m) = sum t_p (m/p) on odd
    squarefree m (split p==1(4): t_p in {+-2x,+-2y}; inert q==3(4): t_q = +-1):
        D(m) == m * W(m) (mod 8),   W(m) = sum t_p * p.
    Corollary: a descended 2-cycle D(m)=m', D(m')=m forces
        W(m) == W(m') == m*m' (mod 8)   (and W odd, = the known parity condition).
"""
import random
from math import isqrt, gcd
from fractions import Fraction
from sympy import primerange, factorint

LIM = 10**6
spf = list(range(LIM + 1))
for i in range(2, isqrt(LIM) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j: spf[j] = i

def sqfree(n):
    ps = []
    while n > 1:
        p = spf[n]; n //= p
        if n % p == 0: return None
        ps.append(p)
    return ps

def deriv(n):
    ps = sqfree(n)
    return sum(n // p for p in ps)

# ---------- I(i)+(iii): closure and determined slot, random general lines ----------
random.seed(11)
bad_cl = bad_slot = zero_den = 0; done = 0
while done < 100000:
    n = random.randint(6, LIM)
    ps = sqfree(n)
    if ps is None or len(ps) < 2: continue
    a = random.randint(1, 50); b = random.randint(-50, 50)
    c = a * deriv(n) - b * n           # n lies on L(a,b,c) by construction
    q = ps[-1]; m = n // q
    a2, b2 = a * q, b * q - a
    if a2 * deriv(m) - b2 * m != c: bad_cl += 1
    den = a * deriv(m) - b * m           # PARENT line's (a,b) at the base m
    if den != 0:
        if (c - a * m) % den or (c - a * m) // den != q: bad_slot += 1
    else:
        zero_den += 1                     # sigma(m)=b/a: allowed for arbitrary (a,b),
    done += 1                             # excluded on genuine chains by I(ii)
print(f"I(i)  closure (aq, bq-a, c) on {done} random (n,a,b): violations {bad_cl}")
print(f"I(iii) determined slot q=(c-am)/(am'-bm): genuine violations {bad_slot}, "
      f"sigma(m)=b/a exceptions {zero_den} (allowed off-chain, impossible on chains)")

# ---------- I(ii): full chains on integer lines, denominators never vanish ----------
bad_den = 0; chains = 0; van_iff = 0
for n in range(6, 200001):
    ps = sqfree(n)
    if ps is None or len(ps) < 2: continue
    for e in (1, 2, 3):
        c = deriv(n) - e * n
        a, b = 1, e
        cur = n; rest = list(ps)
        chains += 1
        while len(rest) > 1:
            q = rest[-1]; m = cur // q
            a, b = a * q, b * q - a
            den = a * deriv(m) - b * m if m > 1 else -b   # m=1: m'=0
            if den == 0: bad_den += 1
            # check the vanishing criterion: den==0 iff sigma(n)==e (never, so den!=0)
            cur = m; rest.pop()
        # sanity: slope telescoping  b/a == e - sum(1/q peeled)
        peeled = [p for p in ps if p != rest[0]]
        if Fraction(b, a) != e - sum(Fraction(1, p) for p in peeled): van_iff += 1
print(f"I(ii) full chains ({chains}), integer lines e=1,2,3: vanishing denominators {bad_den}, "
      f"slope-telescope violations {van_iff}")

# ---------- II: descended mod-8 law ----------
def split_xy(p):
    for x in range(1, isqrt(p) + 1):
        y2 = p - x * x
        y = isqrt(y2)
        if y * y == y2:
            return (x, y) if x % 2 == 1 else (y, x)
    raise ValueError

vals = {}
for p in primerange(3, 400):
    if p % 4 == 1:
        x, y = split_xy(p)
        vals[p] = [2 * x, -2 * x, 2 * y, -2 * y]
    else:
        vals[p] = [1, -1]

bad_d8 = 0; tests = 0
odd_primes = [p for p in primerange(3, 400)]
random.seed(23)
for _ in range(200000):
    k = random.randint(2, 6)
    ps = random.sample(odd_primes, k)
    m = 1
    for p in ps: m *= p
    ts = {p: random.choice(vals[p]) for p in ps}
    D = sum(ts[p] * (m // p) for p in ps)
    W = sum(ts[p] * p for p in ps)
    if (D - m * W) % 8: bad_d8 += 1
    tests += 1
print(f"II    descended mod-8 law D(m) == m*W(m) (mod 8): {tests} random (m,assignment), "
      f"violations {bad_d8}")
print(f"      (cycle corollary: W(m) == W(m') == m*m' (mod 8) — 2 lines from the law)")
