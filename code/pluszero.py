#!/usr/bin/env python3
"""Verify the ingredients of prop:pluszero — the plus-layer has density zero, unconditionally.

Proof shape: split at y = X^(1/u), u = loglog X.
  SMOOTH (P+(N) <= y): Psi(X,y) = X * u^(-u(1+o(1)))  [Rankin; Tenenbaum].
  ROUGH  (P+(N) = p > y): slot injection N -> (M,s), M = N/p <= X^(1-1/u);
      per-base root count rho(E0(M)) <= 4*2^omega(E0) <= exp((log2+o(1)) logX/loglogX) [Wigert/HW];
      rough count <= X^(1/2+o(1)) + X^(1-1/u) * exp((log2+o(1)) logX/loglogX)
                  =  X * exp(-(1-log2-o(1)) logX/loglogX),   and  1 - log 2 = 0.3068 > 0.

Checks:
  1. margin: 1 - log 2 > 0 (the whole theorem hangs on this single inequality).
  2. general-c slot identity: (Mp)' + c*Mp = p*(M'+cM) + M for coprime p (symbolic + numeric).
  3. rho(E0) <= 4*2^omega(E0) on samples (brute root count vs bound).
  4. Wigert sanity: max 2^omega(E0(M)) over M <= 2e4 vs exp(log2 * logX/loglogX).
  5. smooth-count sanity: Psi(1e6, y) with u=loglog(1e6): observed vs X*u^-u order.
  6. the rough/smooth split is exhaustive & injection distinct on real hits (re-check at 1e6).
"""
from math import isqrt, log, exp, gcd
from sympy import symbols, simplify, primerange

# ---------- 1: the margin ----------
print(f"1. 1 - log2 = {1 - log(2):.4f} > 0  (the theorem's engine)")

# ---------- 2: general-c slot identity ----------
Mv, pv, Mp, c = symbols("M p Mprime c")
# (Mp)' = M'p + M (Leibniz, gcd(M,p)=1);  (Mp)' + c*Mp = p*(M'+cM) + M
lhs = (Mp * pv + Mv) + c * Mv * pv
rhs = pv * (Mp + c * Mv) + Mv
print("2. slot identity for general c (symbolic):", simplify(lhs - rhs))

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

bad2 = 0
import random
random.seed(3)
for _ in range(3000):
    M = random.randint(2, 10**4)
    ps = sqfree_factor(M)
    if ps is None: continue
    p = random.choice([q for q in primerange(2, 300) if M % q])
    for cc in (1, 2, 3, 5):
        N = M * p
        psN = sorted(ps + [p])
        if deriv(psN, N) + cc * N != p * (deriv(ps, M) + cc * M) + M: bad2 += 1
print(f"   numeric (3000 random M, c in {{1,2,3,5}}): violations {bad2}")

# ---------- 3: rho(E0) <= 4*2^omega(E0) ----------
bad3 = 0; checked = 0
for M in range(3, 3000):
    ps = sqfree_factor(M)
    if ps is None or len(ps) < 2: continue
    E0 = deriv(ps, M) + 2 * M
    if E0 > 60000: continue
    checked += 1
    rho = sum(1 for s in range(E0) if (s * s - M) % E0 == 0)
    om = len(set(q for q, _ in __import__('sympy').factorint(E0).items()))
    if rho > 4 * 2 ** om: bad3 += 1
print(f"3. rho(E0) <= 4*2^omega(E0) on {checked} bases: violations {bad3}")

# ---------- 4: Wigert sanity ----------
best = 0; arg = None
for M in range(3, 20001):
    ps = sqfree_factor(M)
    if ps is None or len(ps) < 2: continue
    E0 = deriv(ps, M) + 2 * M
    om = len(__import__('sympy').factorint(E0))
    if 2 ** om > best: best, arg = 2 ** om, (M, E0, om)
X = 20000 * 3  # E0 scale ~ 3M
wig = exp(log(2) * log(X) / log(log(X)))
print(f"4. max 2^omega(E0(M)) over M<=2e4: {best} at M={arg[0]} (omega={arg[2]});"
      f" Wigert scale exp(log2*logX/loglogX) = {wig:.0f}  (bound comfortably above: {best <= 4*wig})")

# ---------- 5: smooth-count sanity ----------
u = log(log(LIM))            # loglog 1e6 = 2.63
y = LIM ** (1 / u)           # ~ 191
smooth = 0
for n in range(2, LIM + 1):
    m, big = n, 1
    # largest prime factor via spf chain
    while m > 1:
        q = spf[m]
        if q > big: big = q
        while m % q == 0: m //= q
    if big <= y: smooth += 1
print(f"5. Psi(1e6, {y:.0f}) = {smooth}  vs  X*u^-u = {LIM * u ** (-u):.0f}  "
      f"(same order: ratio {smooth / (LIM * u ** (-u)):.2f} — Rankin is an upper-bound scale)")

# ---------- 6: split exhaustive + injection on the real hits ----------
hits = []
for N in range(2, LIM + 1):
    ps = sqfree_factor(N)
    if ps is None or len(ps) < 2: continue
    v = deriv(ps, N) + 2 * N
    r = isqrt(v)
    if r * r == v: hits.append((N, ps, r))
rough = smooth_h = 0
seen = set(); bad6 = 0
for N, ps, s in hits:
    p = max(ps)
    if p > y:
        rough += 1
        M = N // p
        key = (M, s)
        if key in seen: bad6 += 1
        seen.add(key)
    else:
        smooth_h += 1
print(f"6. hits at 1e6: {len(hits)} = rough {rough} + smooth {smooth_h} (exhaustive);"
      f" rough-injection collisions: {bad6}")
