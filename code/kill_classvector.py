#!/usr/bin/env python3
"""The kill certificate is a class-vector functional — closing the '3/4 awaits explanation'.

For a level-59 admissible base S (39 forced + 20 window primes), D = prod S = 2*D1,
N = cofactor sum, A = N + 2D. The Jacobi kill is (D|A) = -1.

CHAIN (rem:fiveeighths, genus identity proved):
    (D|A) = (2|A) * (D1|N),   (2|A) = +1 iff N == 3,5 (mod 8)   [A == N+4 mod 8],
    (D1|N) = (N|D1) * (-1)^((D1-1)/2 * (N-1)/2),   (N|D1) = (-1)^(s + C(t,2)),
    s = #{p|D1: p==3,5 mod 8},  t = #{p|D1: p==3 mod 4}.

CLASS-VECTOR CLAIM (new): let v(S) = (n1,n3,n5,n7) mod 4 count the odd primes of S in the
classes 1,3,5,7 mod 8. Then EVERY factor above is a function of v alone:
    s == n3+n5 (2);  t == n3+n7;  C(t,2) needs t mod 4;  D1 == 3^n3 5^n5 7^n7 (8);
    D1 == (-1)^t (4);  S(D1) == (n1+n5) - (n3+n7) (mod 4);
    N == D1 + 2*(D1*S(D1) mod 4) (mod 8)          [the mod-8 law:  D1' == D1*S(D1) (8)].
Hence (D|A) = K(v) — the kill is decided by 16 residue counts mod 4.

VERIFY: enumerate all 49,961 bases; per base compute (D|A) three ways:
  direct bignum Jacobi  ==  chain from actual N,D1  ==  K(v) from the vector alone.
Aggregate: total kills (paper: 31,219), exact conditional rates by N mod 8.
"""
from math import isqrt
from fractions import Fraction
from sympy import jacobi_symbol
from math import comb
import sys
sys.setrecursionlimit(10000)

NN = 800
sieve = [True] * (NN + 1); sieve[0] = sieve[1] = False
for i in range(2, int(NN ** 0.5) + 1):
    if sieve[i]:
        for j in range(i * i, NN + 1, i): sieve[j] = False
primes = [i for i in range(2, NN + 1) if sieve[i]]
T = lambda ps: sum(Fraction(1, p) for p in ps)
T58, T60 = T(primes[:58]), T(primes[:60])
forced = [p for p in primes[:60] if T60 - Fraction(1, p) < 2]
pool = [p for p in primes if p > 167 and T58 + Fraction(1, p) > 2]
k = 59 - len(forced); thr = 2 - T(forced)
pf = [Fraction(1, p) for p in pool]

def K_of_v(n1, n3, n5, n7):
    """kill sign from the class vector alone (all mod-4 data)."""
    s = (n3 + n5) % 2
    t = (n3 + n7) % 4
    ct2 = comb(t, 2) % 2 if t < 4 else 0           # C(t,2) mod 2 depends on t mod 4
    ct2 = (t * (t - 1) // 2) % 2
    ND1 = pow(3, n3 % 2, 8) * pow(5, n5 % 2, 8) * pow(7, n7 % 2, 8) % 8   # D1 mod 8
    SD1 = ((n1 + n5) - (n3 + n7)) % 4               # S(D1) mod 4
    Nmod8 = (ND1 + 2 * ((ND1 % 4) * SD1 % 4)) % 8   # mod-8 law
    two_A = 1 if Nmod8 in (3, 5) else -1            # (2|A)
    N_D1 = (-1) ** ((s + ct2) % 2)                  # (N|D1), genus identity
    recip = (-1) ** ((((-1) ** (t % 2) - 1) // 2 % 2) * ((Nmod8 - 1) // 2 % 2) % 2)
    # (D1-1)/2 mod 2 = t mod 2 ; (N-1)/2 mod 2 from N mod 4
    recip = (-1) ** ((t % 2) * (((Nmod8 % 4) - 1) // 2) % 2)
    return two_A * N_D1 * recip, Nmod8

stats = {"n": 0, "kill": 0, "mismatch_chain": 0, "mismatch_v": 0}
by8 = {}   # Nmod8 -> [count, kills]
vecs = {}  # v -> [count, kill_sign]

def test(chosen_idx):
    U = forced + [pool[i] for i in chosen_idx]
    D = 1
    for p in U: D *= p
    Nu = sum(D // p for p in U)
    D1 = D // 2
    A = Nu + 2 * D
    # direct
    kill_direct = jacobi_symbol(D, A)
    # chain from actual numbers
    odd = U[1:]
    s = sum(1 for p in odd if p % 8 in (3, 5))
    t = sum(1 for p in odd if p % 4 == 3)
    two_A = 1 if Nu % 8 in (3, 5) else -1
    N_D1 = (-1) ** ((s + t * (t - 1) // 2) % 2)
    recip = (-1) ** (((D1 - 1) // 2 % 2) * ((Nu - 1) // 2 % 2))
    kill_chain = two_A * N_D1 * recip
    # vector form
    n1 = sum(1 for p in odd if p % 8 == 1) % 4
    n3 = sum(1 for p in odd if p % 8 == 3) % 4
    n5 = sum(1 for p in odd if p % 8 == 5) % 4
    n7 = sum(1 for p in odd if p % 8 == 7) % 4
    kill_v, Nmod8_v = K_of_v(n1, n3, n5, n7)
    stats["n"] += 1
    if kill_chain != kill_direct: stats["mismatch_chain"] += 1
    if kill_v != kill_direct or Nmod8_v != Nu % 8: stats["mismatch_v"] += 1
    if kill_direct == -1: stats["kill"] += 1
    c = by8.setdefault(Nu % 8, [0, 0]); c[0] += 1
    if kill_direct == -1: c[1] += 1
    v = (n1, n3, n5, n7)
    if v in vecs:
        assert vecs[v][1] == kill_direct, ("v not constant!", v)
        vecs[v][0] += 1
    else:
        vecs[v] = [1, kill_direct]

def dfs(i, need, cur, chosen):
    if need == 0:
        if cur > thr: test(chosen)
        return
    if i + need > len(pool): return
    if cur + sum(pf[i:i + need]) <= thr: return
    dfs(i + 1, need - 1, cur + pf[i], chosen + [i])
    dfs(i + 1, need, cur, chosen)

dfs(0, k, Fraction(0), [])
n, kills = stats["n"], stats["kill"]
print(f"bases {n} (paper: 49,961)   kills {kills} (paper: 31,219)   rate {kills/n:.5f} (5/8 = 0.625)")
print(f"chain == direct mismatches: {stats['mismatch_chain']};  K(v) == direct mismatches: {stats['mismatch_v']}")
print("conditional kill rates by N mod 8:")
for r in sorted(by8):
    c, kk = by8[r]
    print(f"  N == {r} (mod 8): {kk}/{c} = {kk/c:.5f}")
print(f"distinct class vectors realized: {len(vecs)} (of 256 possible); K constant on each: verified by assert")
top = sorted(vecs.items(), key=lambda kv: -kv[1][0])[:6]
print("dominant vectors (v=(n1,n3,n5,n7) mod 4: count, kill):", top)
