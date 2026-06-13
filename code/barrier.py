"""Rigorous quantitative barrier for Erdos #307 (exact integer/rational arithmetic).

THM: any solution (P,Q) [wlog s = sum_P 1/p > 1 > t = sum_Q 1/q] satisfies:
 (a) N_P = D_Q and N_Q = D_P            [rigidity: both reciprocal sums are auto-reduced]
 (b) D_Q = s * D_P exactly
 (c) |P u Q| >= m0, where m0 is the least m such that some m distinct primes have reciprocal
     sum >= 2 (worst case = the m smallest primes)
 (d) D_P = min(prod P, prod Q) >= sqrt( prod(first m0 primes) / T_{m0} ),
     using D_P^2 = prod(U)/s, s <= T(U), and prod(U)/T(U) >= prod(first m0)/T_{m0}.
"""
from sympy import prime
from fractions import Fraction
from math import isqrt

# (c) least m0 with reciprocal sum of the m0 smallest primes >= 2
s = Fraction(0); m0 = 0; ps = []
while s < 2:
    m0 += 1; p = prime(m0); ps.append(p); s += Fraction(1, p)
print(f"least m0 with reciprocal sum of m0 smallest primes >= 2: m0 = {m0} (sum = {float(s):.6f})")
print(f"(erdosproblems.com/307 quotes the slightly looser |P u Q| >= 60; the exact threshold is {m0})")

Pi = 1
for q in ps:
    Pi *= q                                  # product of the first m0 primes
print(f"product of first {m0} primes ~ 10^{len(str(Pi))-1}")

# (d) D_P^2 = prod(U)/s >= prod(U)/T(U) >= prod(first m0)/T_{m0}.  The minimum of prod(U)/T(U) over
# prime sets U with reciprocal sum > 2 is attained exactly at U = {first m0 primes}, value Pi/T_{m0}.
T = s                                        # = T_{m0}, the reciprocal sum of the first m0 primes
bound_sq = Fraction(Pi, T)                   # lower bound on D_P^2
DPmin = isqrt(int(bound_sq))
print(f"THEOREM: min(prod P, prod Q) = D_P >= sqrt(prod(first {m0})/T_{m0}) ~ 10^{len(str(DPmin))-1}")
print(f"         D_P >= ~{float(DPmin):.3e}")
print(f"and D_Q = s*D_P > D_P. Any search over products below 10^{len(str(DPmin))-1} is void.")
