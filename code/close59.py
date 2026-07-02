#!/usr/bin/env python3
"""close59.py — finite verification closing the 59-prime level of Erdős #307.

THEOREM (Prop. close59 of the note): no solution of #307 has |P ∪ Q| = 59;
hence |P ∪ Q| >= 60 and min(prod P, prod Q) > 3.50e57.

Completeness of the candidate list (U = P ∪ Q, |U| = 59, T(U) = sum 1/p > 2):
  (i)  every prime p <= 167 lies in U: omitting p caps T(U) at T60 - 1/p < 2,
       because the 59 largest prime reciprocals avoiding p are those of the
       first 60 primes less p, and 1/p > T60 - 2 = 0.00590... exactly for p <= 167
       (39 forced primes);
  (ii) every element p' >= 281 satisfies T58 + 1/p' > 2 (the other 58 reciprocals
       sum to at most T58), hence p' <= 787.
  So U = {39 forced primes} ∪ {20 primes from (167, 787]}; exactly 49,961 such
  sets have T(U) > 2 (exact rational arithmetic throughout).

Necessary condition tested (rigidity + the k=0 case of the pair form):
  a solution supported on U gives N = prod U = a*b with a' = b, b' = a, so
  N' = a^2 + b^2 and BOTH  N' + 2N = (a+b)^2  and  N' - 2N = (a-b)^2  must be
  perfect squares (N' = cofactor sum of U).  One bigint test per U excludes all
  2^58 splits of U at once.

RESULT: N' + 2N is a non-square for every one of the 49,961 candidates.
An independent Rust implementation (hunt/close59.rs, different enumeration
order and pruning, hand-rolled bignum) confirms both the count and the result.

Runtime: a few seconds (CPython 3.9+, stdlib only).
"""
from math import isqrt
from fractions import Fraction
import sys

sys.setrecursionlimit(10000)

# ---- primes to 800 ------------------------------------------------------
N = 800
sieve = [True] * (N + 1)
sieve[0] = sieve[1] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]:
        for j in range(i * i, N + 1, i):
            sieve[j] = False
primes = [i for i in range(2, N + 1) if sieve[i]]

T = lambda ps: sum(Fraction(1, p) for p in ps)
T58, T59, T60 = T(primes[:58]), T(primes[:59]), T(primes[:60])
assert T58 < 2 < T59 < T60, "59 is the first crossing of 2"

# ---- forced primes and pool (completeness bounds (i), (ii)) -------------
forced = [p for p in primes[:60] if T60 - Fraction(1, p) < 2]
assert forced == [p for p in primes if p <= 167] and len(forced) == 39
pool = [p for p in primes if p > 167 and T58 + Fraction(1, p) > 2]
assert pool[0] == 173 and pool[-1] == 787
k = 59 - len(forced)          # 20 free slots
thr = 2 - T(forced)           # chosen reciprocals must exceed this
pf = [Fraction(1, p) for p in pool]

# ---- enumerate + test ----------------------------------------------------
def is_square(x: int) -> bool:
    r = isqrt(x)
    return r * r == x

count = 0
survivors = []

def test(chosen_idx):
    global count
    U = forced + [pool[i] for i in chosen_idx]
    D = 1
    for p in U:
        D *= p
    Nu = sum(D // p for p in U)          # cofactor sum = N' for squarefree N
    assert Nu > 2 * D                    # T(U) > 2, exact
    count += 1
    if is_square(Nu + 2 * D) and is_square(Nu - 2 * D):
        survivors.append(U)

def dfs(i, need, cur, chosen):
    if need == 0:
        if cur > thr:
            test(chosen)
        return
    if i + need > len(pool):
        return
    if cur + sum(pf[i:i + need]) <= thr:  # best-possible prune (exact)
        return
    dfs(i + 1, need - 1, cur + pf[i], chosen + [i])
    dfs(i + 1, need, cur, chosen)

# positive/negative control of the square tester on 115-digit integers
_D = 1
for p in forced + pool[:k]:
    _D *= p
_t = isqrt(_D)
assert is_square(_t * _t) and not is_square(_t * _t + 1)

dfs(0, k, Fraction(0), [])

print(f"admissible 59-prime supports: {count}")
print(f"passing both-squares test:    {len(survivors)}")
for U in survivors:
    print("  SURVIVOR:", U)
if count == 49961 and not survivors:
    print("VERIFIED: no 59-prime support closes -> any #307 solution has |P∪Q| >= 60.")
else:
    print("WARNING: unexpected count or survivors -- investigate before citing.")
