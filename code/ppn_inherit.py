# ppn_inherit.py -- exhaustive one- and two-prime inheritance for primary pseudoperfect numbers.
#
# A primary pseudoperfect number is squarefree n with d(n) = n - 1 (Erdos #313, OEIS A054377).
# Inheritance, following Wang (arXiv:2605.21518, Cor. 5.2 and 5.3), where K is a PPN:
#   one prime : K(K+1) is a PPN  iff  K+1 is prime.
#   two primes: K p q  is a PPN  iff  (p-K)(q-K) = K^2 + 1, with p, q prime and not dividing K.
# Both are equivalences, so a COMPLETE factorisation of K^2+1 decides the two-prime case outright:
# the divisor pairs are the entire candidate set, and exhausting them is a proof, not a search.
#
# Run: python3 ppn_inherit.py
from sympy import isprime, factorint, divisors

N9 = 5998279018951962402
PPN = {1: 2, 2: 6, 3: 42, 4: 1806, 5: 47058, 6: 2214502422, 7: 52495396602,
       8: 8490421583559688410706771261086, 9: N9, 10: N9 * (N9 + 1)}

def is_ppn(n):
    f = factorint(n)
    return all(e == 1 for e in f.values()) and sum(n // p for p in f) == n - 1

for r, K in sorted(PPN.items()):
    assert is_ppn(K) and len(factorint(K)) == r, r

print("one-prime inheritance: K(K+1) is a PPN iff K+1 is prime")
for r, K in sorted(PPN.items()):
    print("  r=%2d -> %2d : K+1 prime? %s" % (r, r + 1, isprime(K + 1)))

print()
print("two-prime inheritance: K p q is a PPN iff (p-K)(q-K) = K^2+1")
for r, K in sorted(PPN.items()):
    M = K * K + 1
    f = factorint(M)
    nd = 1
    for e in f.values():
        nd *= e + 1
    hits = []
    for d in divisors(M):
        e = M // d
        if d > e:
            continue
        p, q = K + d, K + e
        if isprime(p) and isprime(q) and K % p and K % q:
            hits.append((d, p, q))
    print("  r=%2d -> %2d : K^2+1 has %2d digits, %3d divisors, candidates %d"
          % (r, r + 2, len(str(M)), nd, len(hits)))
    for d, p, q in hits:
        n = K * p * q
        print("      p=%d  q=%d  ->  %d-digit PPN with omega=%d, verified %s"
              % (p, q, len(str(n)), len(factorint(n)), is_ppn(n)))
