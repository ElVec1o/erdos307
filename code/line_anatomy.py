#!/usr/bin/env python3
"""Verify prop:lineanatomy — structure of members of derivative lines M' = eM + c.

For squarefree M with two largest primes p > q and R = M/(pq):
  (0) LINE CONGRUENCE (generalized Giuga): M/t == c (mod t) for EVERY prime t | M.
  (a) TOP CAP:      if M/p != c then p <= sqrt(M) + |c|   (from |M/p - c| >= p).
  (b) COUPLING:     pq | R(p+q) - c   (gcd(pq,c)=1 automatic: p|c => p|qR, impossible).
  (c) SECOND CAP:   if R(p+q) != c then q < R + sqrt(R^2+|c|);
      degenerate stratum R(p+q)=c forces c >= 2*sqrt(R*M).

Test: EVERY squarefree n <= LIM with omega >= 3, both e in {1,2}, with c := n' - e*n
(tautologically a line member) — plus the classical PPN/Giuga members.
"""
from math import isqrt, gcd

LIM = 2 * 10**7
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

bad = [0]*5; tested = 0; tight = None; degen = 0
for n in range(30, LIM + 1):
    ps = sqfree_factor(n)
    if ps is None or len(ps) < 3: continue
    tested += 1
    d = sum(n // t for t in ps)
    p, q = ps[-1], ps[-2]; R = n // (p * q)
    for e in (1, 2):
        c = d - e * n
        # (0) line congruence at every prime
        if any((n // t - c) % t for t in ps): bad[0] += 1
        # (a) top cap
        if n // p != c and not (p <= isqrt(n) + abs(c) + 1): bad[1] += 1
        # (b) coupling + automatic coprimality
        if (R * (p + q) - c) % (p * q): bad[2] += 1
        if gcd(p * q, c) != 1: bad[3] += 1
        # (c) second cap / degenerate stratum
        if R * (p + q) != c:
            capv = R + isqrt(R * R + abs(c)) + 1
            if not (q <= capv): bad[4] += 1
            slack = capv - q
            if tight is None or slack < tight[0]: tight = (slack, n, e, c, q, R)
        else:
            degen += 1
            assert c * c >= 4 * R * n, (n, e, c)   # c >= 2 sqrt(RM)
print(f"tested {tested} squarefree n<=2e7 (omega>=3), both e in {{1,2}}:")
print(f"  (0) line congruence violations : {bad[0]}")
print(f"  (a) top cap violations         : {bad[1]}")
print(f"  (b) coupling violations        : {bad[2]}   (gcd(pq,c)!=1 count: {bad[3]})")
print(f"  (c) second-cap violations      : {bad[4]}   degenerate-stratum members: {degen}")
print(f"  tightest second cap: slack {tight[0]} at n={tight[1]} (e={tight[2]}, c={tight[3]}, q={tight[4]}, R={tight[5]})")

# classical members explicitly
print("\nclassical members:")
for name, e, c, N in (("PPN", 1, -1, 42), ("PPN", 1, -1, 1806), ("PPN", 1, -1, 47058),
                      ("Giuga", 1, 1, 30), ("Giuga", 1, 1, 858), ("Giuga", 1, 1, 1722), ("Giuga", 1, 1, 66198)):
    ps = sqfree_factor(N)
    p, q = ps[-1], ps[-2]; R = N // (p * q)
    coup = (R * (p + q) - c) // (p * q)
    cap = R + isqrt(R * R + abs(c)) + 1
    print(f"  {name} {N}: p={p} q={q} R={R};  (R(p+q)-c)/(pq) = {coup} (exact: "
          f"{(R*(p+q)-c) % (p*q) == 0});  q={q} <= cap {cap}: {q <= cap}")
