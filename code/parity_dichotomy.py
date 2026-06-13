"""New structural lemmas in derivative language, exact arithmetic.
LEMMA (parity dichotomy): in a squarefree 2-cycle a'=b, b'=a either
 (i) exactly one of a,b is even, or (ii) both odd.
Case (ii) barrier: union has NO factor 2, so sum over P∪Q of 1/p > 2 must be
achieved by odd primes only -> compute exact minimal count and product bound."""
from sympy import prime
from fractions import Fraction
from math import isqrt

# case (ii): both odd
s = Fraction(0); m = 0; ps = []
i = 2  # skip p_1 = 2
while s <= 2:
    p = prime(i); i += 1; m += 1; ps.append(p); s += Fraction(1, p)
print(f"both-odd case: need >= {m} odd primes (sum over first {m} odd primes = {float(s):.5f})")
prod = 1
for q in ps: prod *= q
T = s
import math
DPmin2 = isqrt(int(Fraction(prod, T)))
print(f"both-odd barrier: min(a,b) >= ~10^{len(str(DPmin2))-1}  (vs 10^56 in the mixed case)")

# case (i) refinement: wlog 2|a, a=2m (m odd squarefree). a' = m + 2m' = b (odd). 
# b odd squarefree: b' = sum of ω(b) odd terms => b' ≡ ω(b) (mod 2); b' = a even => ω(b) even.
# also a' = b: m odd, so b ≡ m + 0 ≡ 1 (mod 2) consistent.  Verify on random data:
from sympy import primerange, factorint
from math import prod as mprod
import random
random.seed(2)
ps_all = list(primerange(3, 500))
ok = True
def ader(n):
    f = factorint(n); return sum(n*e//p for p,e in f.items())
for _ in range(300):
    P = [2] + random.sample(ps_all, random.randint(2,7))
    a = mprod(P); b = ader(a)
    f = factorint(b)
    if all(e==1 for e in f.values()):           # b squarefree
        if b % 2 == 0: ok = False               # must be odd
        # if also b' = a held, ω(b) must be even — can't test the full cycle (none exist small),
        # but test the parity identity b' ≡ ω(b) mod 2 for odd squarefree b:
        if (ader(b) - len(f)) % 2 != 0: ok = False
print("parity identities verified on 300 random cases:", ok)
print()
print("LEMMA (mixed case, wlog 2|a): b = a' is odd, and ω(b) must be EVEN.")
