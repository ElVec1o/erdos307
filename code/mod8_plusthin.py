#!/usr/bin/env python3
"""Verify two candidate additions.

A. MOD-8 LAW: for odd squarefree m with S(m)=sum of primes:   m*m' == S(m) (mod 8).
   (a) mod 2 it is the parity law m' == omega(m);
   (b) all-odd 2-cycle a'=b,b'=a  =>  S(a) == S(b) == ab (mod 8);
   (c) mixed case a=2k (k odd sf): b=(2k)' satisfies b == k(1+2S(k)) (mod 16),
       and the even companion (2k)*(2k)' == 2+4S(k) (mod 16);
   (d) odd squarefree N: N'+2N == N(S(N)+2) (mod 8), and a plus-hit forces
       ==1 (8) if omega odd,  in {0,4} (8) if omega even.

B. PLUS-THIN: semiprime plus-hits N=pq<=X are injectively (s,{2p+1,2q+1}) with
   2s^2+1=(2p+1)(2q+1), s<=sqrt(3X); so count <= (1/2) sum tau(2s^2+1).
   Sanity: reproduce the paper's censuses (114 hits < 2e5; 251 < 1e6; 59 semiprime < 2e5;
   68 members of the p=5 family with s<2000), the injection, Hensel rho(p^j)=rho(p),
   and the growth of sum tau(2s^2+1) ~ Y log Y.
"""
from math import isqrt, log
from sympy import isprime

LIM = 10**6

# smallest-prime-factor sieve
spf = list(range(LIM + 1))
for i in range(2, isqrt(LIM) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j: spf[j] = i

def sqfree_factor(n):  # returns prime list or None if not squarefree
    ps = []
    while n > 1:
        p = spf[n]; n //= p
        if n % p == 0: return None
        ps.append(p)
    return ps

# ---------- A: the law, exhaustive over odd squarefree m <= 1e6 ----------
bad_law = bad_mix = bad_evencomp = tested = 0
for m in range(3, LIM + 1, 2):
    ps = sqfree_factor(m)
    if ps is None: continue
    tested += 1
    d = sum(m // p for p in ps)   # m'
    S = sum(ps)
    if (m * d - S) % 8: bad_law += 1
    # mixed-case chain: b=(2m)'=m+2m'
    b = m + 2 * d
    if (b - m * (1 + 2 * S)) % 16: bad_mix += 1
    if (2 * m * b - (2 + 4 * S)) % 16: bad_evencomp += 1
print(f"A. law m*m'==S(m) mod 8   : {tested} odd squarefree m<=1e6, violations {bad_law}")
print(f"   (c) b==k(1+2S(k)) mod16: violations {bad_mix};  even companion mod16: violations {bad_evencomp}")

# ---------- plus-hits (validates sieve against paper + checks (d)) ----------
def deriv_ps(n, ps): return sum(n // p for p in ps)
hits = []
for N in range(2, LIM + 1):
    ps = sqfree_factor(N)
    if ps is None or len(ps) < 2: continue
    v = deriv_ps(N, ps) + 2 * N
    r = isqrt(v)
    if r * r == v: hits.append((N, ps, r))
h2e5 = [h for h in hits if h[0] < 2 * 10**5]
print(f"   census: {len(h2e5)} plus-hits < 2e5 (paper: 114), {len(hits)} < 1e6 (b-file: 251)")
bad_d = 0
for N, ps, s in hits:
    if N % 2 == 0: continue
    S = sum(ps); w = len(ps)
    lhs = (N * (S + 2)) % 8
    if w % 2 == 1 and lhs != 1: bad_d += 1
    if w % 2 == 0 and lhs not in (0, 4): bad_d += 1
print(f"   (d) filter on all odd plus-hits < 1e6: violations {bad_d}")

# ---------- B: semiprime injection ----------
semi = [(N, ps, s) for N, ps, s in h2e5 if len(ps) == 2]
print(f"B. semiprime plus-hits < 2e5: {len(semi)} (paper: 59); all-odd: {all(N%2 for N,_,_ in semi)}")
seen = set(); bad_inj = 0
for N, (p, q), s in semi:
    if (2*p+1)*(2*q+1) != 2*s*s + 1: bad_inj += 1
    key = (s, frozenset((2*p+1, 2*q+1)))
    if key in seen: bad_inj += 1
    seen.add(key)
    if s > isqrt(3 * 2 * 10**5) + 1: bad_inj += 1
print(f"   identity (2p+1)(2q+1)=2s^2+1, injectivity, s<=sqrt(3X): violations {bad_inj}")

# Hensel: rho(p^j) = rho(p) for odd p (disc -8)
bad_h = 0
for p in (3, 5, 7, 11, 13, 17, 19, 23):
    r1 = sum(1 for s in range(p) if (2*s*s+1) % p == 0)
    for j in (2, 3):
        rj = sum(1 for s in range(p**j) if (2*s*s+1) % p**j == 0)
        if rj != r1: bad_h += 1
print(f"   Hensel rho(p^j)=rho(p) for p<=23, j<=3: violations {bad_h}  (rho in {{0,2}}: "
      f"{sorted(set(sum(1 for s in range(p) if (2*s*s+1)%p==0) for p in (3,5,7,11,13,17,19,23)))})")

# growth of sum tau(2s^2+1): ratio to Y log Y should be roughly stable
from sympy import divisor_count
for Y in (500, 1000, 2000):
    tot = sum(divisor_count(2*s*s+1) for s in range(1, Y+1))
    print(f"   sum_{{s<={Y}}} tau(2s^2+1) = {tot}   ratio/(Y ln Y) = {tot/(Y*log(Y)):.3f}")

# the p=5 Bunyakovsky family (paper (iii)): 68 hits with s<2000
cnt = 0
for s in range(2, 2000, 2):
    if s % 11 in (4, 7):
        q, r = divmod(s*s - 5, 11)
        if r == 0 and isprime(q): cnt += 1
print(f"   p=5 family, s<2000: {cnt} prime values (paper: 68)")
