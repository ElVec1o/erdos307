#!/usr/bin/env python3
"""Verify prop:pairlocal — the pair sector admits no congruence kill (all bases, all moduli).

System per base W:  x^2 = A*t + D*s,  y^2 = B*t + D*s,  t = alpha*beta, s = alpha+beta,
alpha,beta unit residues (classes of the two new primes p,q), A = N+2D, B = N-2D, gcd(N,D)=1.

Checks:
  0. symbolic: with m=(x^2-y^2)/(4D), u=(x^2-A m)/D and A-B=4D:  B m + D u == y^2 IDENTICALLY.
  1. forced primes at level 60: 1/103 > T61-2 > 1/107  (=> every odd l<=103 divides D_W).
  2. regime 1 (l odd, l | D): the constructive solution beta=1, x=1, alpha=(1-D)/(A+D):
     second target == 1 mod l, is a unit square mod l^j; explicit y found; all l in W, j<=3.
  3. regime 2 (l odd, l !| 2D, 107<=l<=600): solutions exist for EVERY such l (scan (x,y),
     recover alpha,beta as roots of z^2-uz+m, verify both congruences, alpha*beta != 0);
     also measure the (x,y)-success fraction ~ 1/2 (Weil-count sanity).
  4. regime 3 (l=2): (a) both targets odd and congruent mod 8; (b) full table over
     (A mod 8, D mod 8 in {2,6}): some achievable (t,s) = (ab, a+b) with a,b odd makes the
     common target == 1 mod 8 (=> 2-adic square => soluble mod 2^j for all j);
     (c) direct mod-32 check on the test bases.
  5. gcd(A,D) = gcd(B,D) = 1 (the 2-line no-constant-certificate fact).
"""
from fractions import Fraction
from sympy import primerange, symbols, simplify, gcd as sgcd
from math import gcd

# ---------- 0: the collapse identity ----------
x, y, A, B, D = symbols('x y A B D')
m = (x**2 - y**2) / (4*D)
u = (x**2 - A*m) / D
expr = (B*m + D*u - y**2).subs(B, A - 4*D)
print("0. collapse identity  B m + D u - y^2  (with B=A-4D):", simplify(expr))

# ---------- 1: forced primes at level 60 ----------
primes100 = list(primerange(2, 1000))
T61 = sum(Fraction(1, p) for p in primes100[:61])
print(f"1. T61-2 = {float(T61-2):.5f};  1/103 = {1/103:.5f} > it: {Fraction(1,103) > T61-2};"
      f"  1/107 = {1/107:.5f} < it: {Fraction(1,107) < T61-2}  => forced set = odd primes <= 103")

# ---------- test bases ----------
P58 = primes100[:58]                       # 2..271
bases = {
    "W1 = first 58 primes": P58,
    "W2 = swap 271->277":   P58[:57] + [277],
    "W3 = swap 269,271->277,281": P58[:56] + [277, 281],
}

def ND(W):
    Dv = 1
    for p in W: Dv *= p
    Nv = sum(Dv // p for p in W)
    return Nv, Dv

def is_sq_mod_odd_pp(v, l, j):
    """unit v a square mod l^j (l odd)? Euler on the cyclic unit group."""
    mod = l**j
    phi = mod // l * (l - 1)
    return pow(v % mod, phi // 2, mod) == 1

def sqrt_mod_pp(v, l, j):
    """y with y^2 == v mod l^j, l odd, v unit square. Brute mod l then Hensel."""
    y0 = next(t for t in range(1, l) if (t*t - v) % l == 0)
    yk, mod = y0, l
    for _ in range(j - 1):
        mod *= l
        inv = pow(2*yk, -1, mod)
        yk = (yk - (yk*yk - v) * inv) % mod
    return yk

ok1 = ok2 = ok5 = True
for name, W in bases.items():
    N, Dv = ND(W)
    Av, Bv = N + 2*Dv, N - 2*Dv
    ok5 &= gcd(Av, Dv) == 1 and gcd(Bv, Dv) == 1 and gcd(N, Dv) == 1
    # regime 1: every odd l in W, j<=3
    for l in [p for p in W if p != 2]:
        for j in (1, 2, 3):
            mod = l**j
            alpha = (1 - Dv) * pow((Av + Dv) % mod, -1, mod) % mod
            if alpha % l == 0: ok1 = False; break
            t, s = alpha, (alpha + 1) % mod
            if (Av*t + Dv*s - 1) % mod: ok1 = False   # x=1 solves eq.1 by construction
            v = (Bv*t + Dv*s) % mod
            if v % l == 0 or not is_sq_mod_odd_pp(v, l, j): ok1 = False
            yv = sqrt_mod_pp(v, l, j)
            if (yv*yv - v) % mod: ok1 = False
    # regime 2: 107 <= l <= 600, l !| 2D
    fracs = []
    for l in primerange(107, 601):
        if Dv % l == 0: continue
        found = 0; tried = 0; got = None
        inv4D = pow(4*Dv % l, -1, l); invD = pow(Dv % l, -1, l)
        for xx in range(1, l):
            for yy in range(1, l):
                if xx == yy or (xx + yy) % l == 0: continue
                tried += 1
                mm = (xx*xx - yy*yy) * inv4D % l
                uu = (xx*xx - Av*mm) * invD % l
                dd = (uu*uu - 4*mm) % l
                if pow(dd, (l-1)//2, l) not in (0, 1): continue
                rt = next(t for t in range(l) if (t*t - dd) % l == 0)
                a_ = (uu + rt) * pow(2, -1, l) % l
                b_ = (uu - rt) * pow(2, -1, l) % l
                if a_ == 0 or b_ == 0: continue
                tt, ss = a_*b_ % l, (a_+b_) % l
                assert (Av*tt + Dv*ss - xx*xx) % l == 0 and (Bv*tt + Dv*ss - yy*yy) % l == 0
                found += 1
                if got is None: got = (xx, yy, a_, b_)
            if found and tried > 400: break
        if not got: ok2 = False; print(f"   REGIME-2 FAILURE l={l} base {name}")
        fracs.append(found / max(tried, 1))
    print(f"   {name}: regime-2 success-fraction avg {sum(fracs)/len(fracs):.3f} (Weil predicts ~0.5)")
print(f"2. regime-1 constructive solution, all odd l in W, j<=3: {'OK' if ok1 else 'FAIL'}")
print(f"3. regime-2 soluble for every l in [107,600] !| 2D, all bases: {'OK' if ok2 else 'FAIL'}")
print(f"5. gcd(A,D)=gcd(B,D)=gcd(N,D)=1 on all bases: {'OK' if ok5 else 'FAIL'}")

# ---------- 4: the 2-adic table ----------
odd_sq_32 = {t*t % 32 for t in range(1, 32, 2)}          # {1,9,17,25}
tab_ok = True
for A8 in (1, 3, 5, 7):
    for D8 in (2, 6):
        hit = any((A8*(a*b) + D8*(a+b)) % 8 == 1 for a in range(1, 8, 2) for b in range(1, 8, 2))
        if not hit: tab_ok = False; print(f"   TABLE FAILURE A={A8} D={D8} mod 8")
print(f"4a. table: for every (A mod 8, D mod 8) some odd (alpha,beta) gives common target == 1 mod 8: "
      f"{'OK' if tab_ok else 'FAIL'}")
m32_ok = True
for name, W in bases.items():
    N, Dv = ND(W); Av, Bv = N + 2*Dv, N - 2*Dv
    hit = any((Av*a*b + Dv*(a+b)) % 32 in odd_sq_32 and (Bv*a*b + Dv*(a+b)) % 32 in odd_sq_32
              for a in range(1, 32, 2) for b in range(1, 32, 2))
    cong = all((Av*a*b - Bv*a*b) % 8 == 0 for a in range(1, 8, 2) for b in range(1, 8, 2))
    if not (hit and cong): m32_ok = False
print(f"4b. direct mod-32 solubility + (At==Bt mod 8) on all test bases: {'OK' if m32_ok else 'FAIL'}")
