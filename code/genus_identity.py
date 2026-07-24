#!/usr/bin/env python3
"""Verify (and thereby support the proof of) the rem:fiveeighths genus identity.

Claim:  for an admissible base S with D = prod S = 2*D1 (D1 odd), N = sum_{p|D} D/p,
        (N | D1)  =  (-1)^(s + C(t,2)),
        s = #{p | D1 : p = 3,5 mod 8},  t = #{p | D1 : p = 3 mod 4},
independent of N.

Proof to check:
  (N|D1) = prod_{p|D1} (N|p);  N = D/p mod p  (cofactor survival);  D/p = 2*D1/p
        => (N|p) = (2|p) * (D1/p | p)
  prod_p (2|p)      = (-1)^s
  prod_p (D1/p | p) = prod_{p != q} (q|p) = prod_{{p,q}} (q|p)(p|q)
                    = prod_{{p,q}} (-1)^{((p-1)/2)((q-1)/2)} = (-1)^{C(t,2)}
"""
from sympy import jacobi_symbol, primerange
import random
from math import comb

def cofactor_sum(primes):
    D = 1
    for p in primes: D *= p
    return sum(D // p for p in primes), D

def genus_pred(odd_primes):
    s = sum(1 for p in odd_primes if p % 8 in (3, 5))
    t = sum(1 for p in odd_primes if p % 4 == 3)
    return (-1) ** (s + comb(t, 2))

POOL = list(primerange(3, 400))
random.seed(11)
bad = bad_step = 0
tested = 0
for trial in range(20000):
    k = random.randint(2, 12)
    odd = sorted(random.sample(POOL, k))
    S = [2] + odd
    N, D = cofactor_sum(S)
    D1 = D // 2
    from math import gcd
    if gcd(N, D1) != 1:            # rigidity guarantees this for real bases; skip degenerate draws
        continue
    tested += 1
    lhs = jacobi_symbol(N, D1)
    if lhs != genus_pred(odd): bad += 1
    # also check the intermediate step  (N|p) == (2|p)*(D1/p|p)  prime by prime
    for p in odd:
        if (jacobi_symbol(N, p) != jacobi_symbol(2, p) * jacobi_symbol(D1 // p, p)):
            bad_step += 1

print(f"bases tested: {tested}")
print(f"closed form  (N|D1) = (-1)^(s+C(t,2))     : violations {bad}")
print(f"step         (N|p) = (2|p)(D1/p|p)        : violations {bad_step}")

# independence of N: perturb N by any multiple of D1 -> same symbol (sanity on the statement)
odd = [3, 5, 7, 11, 13]; S = [2] + odd
N, D = cofactor_sum(S); D1 = D // 2
vals = {jacobi_symbol(N + j * D1, D1) for j in range(1, 40)}
print(f"independence check: (N + j*D1 | D1) over j=1..39 -> {vals}  (predicted {genus_pred(odd)})")
