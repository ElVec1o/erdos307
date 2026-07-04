#!/usr/bin/env python3
"""tailkill.py — reciprocity kill of level-60 tail families of Erdős #307.

THEOREM (Prop. tailkill): no solution of #307 has support U = {first 59 primes} ∪ {q},
for ANY prime q.

Certificate: a solution supported on U forces x² = A·q + Π₅₉ with A = N₅₉ + 2Π₅₉.
Every prime ℓ | A exceeds 277 (else ℓ | gcd(N₅₉, Π₅₉) = 1, contradicting rigidity),
so x² ≡ Π₅₉ (mod ℓ) requires (Π₅₉|ℓ) ≠ −1.  The Jacobi symbol (Π₅₉|A) = −1 (computed
below, no factorization needed), so some ℓ | A of odd multiplicity has Legendre
(Π₅₉|ℓ) = −1: the family is empty.

Identity: for any admissible base S (a 59-prime set with Σ1/p > 2), the two symbols
agree, (D_S | A_S) = (D_S | B_S): A_S ≡ B_S (mod 8) and mod every odd p | D_S, and the
reciprocity sign difference vanishes since (A_S − B_S)/2 = 2·D_S is even.  One binary
certificate per family.

Sweep: over all 49,961 admissible bases, the certificate is −1 for 31,219 families
(62.5% — proven empty for every tail prime q); 18,742 are Jacobi-inconclusive.

Runtime: ~10 s (stdlib only).
"""
import sys
from fractions import Fraction
sys.setrecursionlimit(10000)


def jacobi(a: int, n: int) -> int:
    assert n > 0 and n % 2 == 1
    a %= n
    t = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                t = -t
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            t = -t
        a %= n
    return t if n == 1 else 0


# primes to 800
N = 800
sieve = [True] * (N + 1)
sieve[0] = sieve[1] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]:
        for j in range(i * i, N + 1, i):
            sieve[j] = False
primes = [i for i in range(2, N + 1) if sieve[i]]

# canonical family
P59 = [p for p in primes if p <= 277]
Pi59 = 1
for p in P59:
    Pi59 *= p
N59 = sum(Pi59 // p for p in P59)
A, B = N59 + 2 * Pi59, N59 - 2 * Pi59
jA, jB = jacobi(Pi59 % A, A), jacobi(Pi59 % B, B)
print(f"canonical family: (Pi59|A) = {jA}, (Pi59|B) = {jB}")
assert jA == jB == -1, "certificate changed?!"
print("=> the canonical level-60 tail family {first 59 primes} ∪ {q} is EMPTY for every q.\n")

# sweep all admissible bases (enumeration identical to close59.py)
forced = [p for p in primes if p <= 167]
pool = [p for p in primes if 167 < p <= 787]
thr = 2 - sum(Fraction(1, p) for p in forced)
pf = [Fraction(1, p) for p in pool]
Dforced = 1
for p in forced:
    Dforced *= p

count = killed = 0
agree = True


def test(idx):
    global count, killed, agree
    D = Dforced
    for i in idx:
        D *= pool[i]
    S = forced + [pool[i] for i in idx]
    Ns = sum(D // p for p in S)
    ja = jacobi(D % (Ns + 2 * D), Ns + 2 * D)
    jb = jacobi(D % (Ns - 2 * D), Ns - 2 * D)
    if ja != jb:
        agree = False
    count += 1
    if ja == -1:
        killed += 1


def dfs(i, need, cur, chosen):
    if need == 0:
        if cur > thr:
            test(chosen)
        return
    if i + need > len(pool):
        return
    if cur + sum(pf[i:i + need]) <= thr:
        return
    dfs(i + 1, need - 1, cur + pf[i], chosen + [i])
    dfs(i + 1, need, cur, chosen)


dfs(0, 20, Fraction(0), [])
print(f"admissible bases: {count} (expected 49961)")
print(f"identity (D|A_S) == (D|B_S) held for all: {agree}")
print(f"families PROVEN EMPTY (certificate -1): {killed}")
print(f"Jacobi-inconclusive survivors:           {count - killed}")
if count == 49961 and killed == 31219 and agree:
    print("VERIFIED: matches the recorded values (31,219 / 49,961 killed; identity universal).")
else:
    print("WARNING: values differ from the recorded ones — investigate before citing.")
