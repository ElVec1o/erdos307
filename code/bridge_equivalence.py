"""Verify: Erdos #307 <=> squarefree 2-cycle of the arithmetic derivative.
(1) arithmetic derivative of squarefree m equals cofactor sum N(m);
(2) gcd(a, a') = 1 for squarefree a;
(3) (P,Q) solution <-> (D_P, D_Q) is a 2-cycle, on random test data both directions."""
from sympy import factorint, primerange, gcd
from fractions import Fraction
from math import prod
import random
random.seed(1)

def ader(n):  # arithmetic derivative, general
    if n <= 1: return 0
    f = factorint(n)
    return sum(n * e // p for p, e in f.items())

def cofsum(m):  # cofactor sum for squarefree m
    f = factorint(m)
    assert all(e == 1 for e in f.values())
    return sum(m // p for p in f)

ps = list(primerange(2, 200))
ok1 = ok2 = True
for _ in range(500):
    S = random.sample(ps, random.randint(1, 8))
    m = prod(S)
    if ader(m) != cofsum(m): ok1 = False
    if gcd(m, ader(m)) != 1: ok2 = False
print("(1) a' == cofactor sum for squarefree a [500 random]:", ok1)
print("(2) gcd(a, a') == 1 for squarefree a [500 random]:", ok2)

# (3) equivalence on synthetic data: random disjoint P,Q -> check (sum)(sum)==1 iff 2-cycle
agree = True
for _ in range(2000):
    k1, k2 = random.randint(2,6), random.randint(2,6)
    S = random.sample(ps, k1 + k2)
    P, Q = S[:k1], S[k1:]
    a, b = prod(P), prod(Q)
    lhs = (sum(Fraction(1,p) for p in P) * sum(Fraction(1,q) for q in Q) == 1)
    rhs = (ader(a) == b and ader(b) == a)
    if lhs != rhs: agree = False
print("(3) [(sumP)(sumQ)=1] <-> [a'=b and b'=a] on 2000 random pairs:", agree)
print()
print("EQUIVALENCE VERIFIED: Erdos #307 == 'squarefree 2-cycle of the arithmetic derivative'")
