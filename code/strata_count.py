#!/usr/bin/env python3
"""Verify prop:strata — slot counting bounds every fixed-omega stratum of the plus-layer.

Claims to check on every plus-hit N <= 1e6 with omega >= 3 (and the machinery for omega=2):
  1. p := P+(N) (largest prime), M := N/p, E0(M) := M'+2M. SLOT identity:
         N'+2N = p*E0(M) + M       (Prop 21 with base M, slot p)
     and hence s^2 == M (mod E0(M)) with p = (s^2-M)/E0(M): the map N -> (M,s) is injective.
  2. gcd(M, M') = 1 for squarefree M  (=> gcd(M, E0(M)) = 1 => the congruence s^2 == M mod E0
     is nonsingular at every odd prime; Hensel => rho(E0) <= 4*2^omega(E0)).
  3. P+(N) >= N^(1/r) for omega(N)=r  => M <= X^(1-1/r).
  4. stratum counts by omega at 1e5 / 1e6 (recorded; compared to the X^(1-1/r) bound and to sqrt X).
  5. sample: average rho(E0(M)) over semiprime M (supports the remark that the true size
     is governed by the no-residue trichotomy; empirically avg < 1).
"""
from math import isqrt, gcd
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

def deriv(ps, n): return sum(n // p for p in ps)

hits = []
for N in range(2, LIM + 1):
    ps = sqfree_factor(N)
    if ps is None or len(ps) < 2: continue
    v = deriv(ps, N) + 2 * N
    r = isqrt(v)
    if r * r == v: hits.append((N, ps, r))

# 1-3: the injection machinery on every hit with omega>=2
bad_slot = bad_gcd = bad_pplus = 0
seen = set()
for N, ps, s in hits:
    p = max(ps)
    M = N // p
    Mps = [q for q in ps if q != p]
    E0 = deriv(Mps, M) + 2 * M
    # slot identity
    if s * s != p * E0 + M: bad_slot += 1
    # injectivity key
    key = (M, s)
    if key in seen: bad_slot += 1
    seen.add(key)
    # congruence + integrality
    if (s * s - M) % E0 != 0 or (s * s - M) // E0 != p: bad_slot += 1
    # gcd(M, M') = 1  (M=1 for omega=1 base excluded: omega(N)>=2 => M>1... M=1 iff omega(N)=1, absent)
    if M > 1 and gcd(M, deriv(Mps, M)) != 1: bad_gcd += 1
    # P+ >= N^(1/r)
    r = len(ps)
    if p ** r < N: bad_pplus += 1
print(f"hits <=1e6: {len(hits)}; slot-identity/injection violations {bad_slot}; "
      f"gcd(M,M') violations {bad_gcd}; P+ >= N^(1/r) violations {bad_pplus}")

# 4: stratum counts
from collections import Counter
for X in (10**5, 10**6):
    c = Counter(len(ps) for N, ps, s in hits if N <= X)
    tot = sum(c.values())
    print(f"X=1e{len(str(X))-1}: strata {dict(sorted(c.items()))}  total {tot}  sqrtX {isqrt(X)}  "
          f"X^(2/3) {int(X**(2/3))}")

# 5: average rho(E0(M)) over semiprime M  (brute-force root count of s^2 == M mod E0)
import random
random.seed(5)
semis = []
for M in range(15, 20001, 2):
    ps = sqfree_factor(M)
    if ps and len(ps) == 2 and 2 not in ps: semis.append((M, ps))
sample = random.sample(semis, 400)
tot_rho = 0
for M, ps in sample:
    E0 = deriv(ps, M) + 2 * M
    tot_rho += sum(1 for s in range(E0) if (s * s - M) % E0 == 0)
print(f"5. average rho(E0(M)) over {len(sample)} random odd semiprime bases M<=2e4: "
      f"{tot_rho/len(sample):.3f}  (<1 => no-residue dominates, as in the slot trichotomy)")
