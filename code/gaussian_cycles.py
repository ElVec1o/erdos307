"""Two-cycles of unit-valued Leibniz derivatives over Z[i].

Verifies, exactly and from scratch, the sixteen Gaussian two-cycles (up to conjugation and
direction) reported in the paper's ordered-archimedean remark.  Each entry is one direction
of one cycle, given as (a-classes, units-code): the a-classes are canonical (first-quadrant)
Gaussian primes in increasing-norm order; the units-code is base 4, giving pi' = i^k for the
2nd, 3rd, ... prime (the first prime has pi' = 1).  The script recomputes a, the twisted
derivative b = a', factorises b over Z[i] independently (Cornacchia + round-trip check),
and exhaustively finds closing units with b' = a exactly.

Smallest cycle: a = (1+i)(2+7i)(6+11i) = -129-i (norm 16,642), b = 3(2+i)(1+2i)(6+5i)
= -75+90i (norm 13,725): a' = b with all pi' = 1 on a's primes; b' = a with pi' = i on
3, 2+i, 1+2i and pi' = 1 on 6+5i.  Seven prime classes, against the 59 forced over Z
(where even sign-twisted derivatives p' = +-1 provably retain the full barrier).
"""
from itertools import product as iproduct
from sympy import factorint

def gmul(a, b): return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])
def gadd(a, b): return (a[0]+b[0], a[1]+b[1])
def mul_i(a, k):
    for _ in range(k % 4):
        a = (-a[1], a[0])
    return a
def canon(z):
    x, y = z
    for _ in range(4):
        if x > 0 and y >= 0: return (x, y)
        x, y = -y, x
def norm(z): return z[0]*z[0] + z[1]*z[1]
def gdiv(a, b):
    n = norm(b)
    x = a[0]*b[0] + a[1]*b[1]; y = a[1]*b[0] - a[0]*b[1]
    return (x//n, y//n) if x % n == 0 and y % n == 0 else None

def cornacchia(p):
    for g in range(2, 200):
        r = pow(g, (p - 1)//4, p)
        if r*r % p == p - 1: break
    a, b = p, r
    while b*b > p: a, b = b, a % b
    x = b; y = int((p - x*x)**0.5)
    assert x*x + y*y == p
    return x, y

def gfactor_squarefree(z):
    """factor z into canonical Gaussian prime classes; None if not squarefree in Z[i]"""
    out = []
    for q, e in sorted(factorint(norm(z)).items()):
        q, e = int(q), int(e)
        if q == 2:
            if e >= 2: return None
            out.append((1, 1))
        elif q % 4 == 3:
            if e % 2 or e > 2: return None
            out.append((q, 0))
        else:
            if e >= 3: return None
            x, y = cornacchia(q)
            if e == 2:
                if z[0] % q == 0 and z[1] % q == 0: out.extend([(x, y), (y, x)])
                else: return None
            else:
                out.append((x, y) if gdiv(z, (x, y)) else (y, x))
    p = (1, 0)
    for c in out: p = gmul(p, c)
    assert canon(p) == canon(z), "round-trip failure"
    return out

# the sixteen cycles (one direction each), as found and cross-verified:
CYCLES = [
    ([(1,1),(2,7),(6,11)], 0),
    ([(1,1),(1,2),(1,4),(7,8)], 0),
    ([(1,1),(3,0),(25,28)], 7),
    ([(1,1),(1,2),(4,5),(8,5)], 20),
    ([(1,1),(1,2),(2,3),(10,1),(4,11)], 96),
    ([(1,2),(2,3),(12,7),(4,15)], 28),
    ([(1,1),(1,2),(3,0),(3,2),(15,38)], 92),
    ([(1,1),(1,2),(3,0),(4,1),(37,32)], 44),
    ([(1,1),(3,0),(1,4),(6,1),(17,10)], 195),
    ([(1,1),(1,2),(4,1),(170,3)], 28),
    ([(1,1),(3,0),(4,5),(62,55)], 3),
    ([(1,1),(1,2),(1,4),(10,3),(21,4)], 1),
    ([(1,1),(1,2),(28,5),(16,29)], 60),
    ([(1,1),(1,2),(2,5),(205,62)], 60),
    ([(1,1),(1,2),(10,1),(57,100)], 36),
    ([(1,1),(1,2),(3,2),(6,1),(58,13)], 144),
]

UN = ['1', 'i', '-1', '-i']
for idx, (acl, code) in enumerate(CYCLES, 1):
    a = (1, 0)
    for c in acl: a = gmul(a, c)
    cofs = [gdiv(a, c) for c in acl]
    d = cofs[0]; cc = code
    aunits = [0]
    for t in range(1, len(acl)):
        aunits.append(cc & 3)
        d = gadd(d, mul_i(cofs[t], cc & 3)); cc >>= 2
    bcl = gfactor_squarefree(d)
    assert bcl is not None and len(bcl) >= 2
    assert not (set(map(canon, acl)) & set(map(canon, bcl))), "supports not disjoint"
    terms = [gdiv(d, c) for c in bcl]
    closed = None
    for vs in iproduct(range(4), repeat=len(terms)):
        s = (0, 0)
        for v, t in zip(vs, terms): s = gadd(s, mul_i(t, v))
        if s == a:
            closed = vs; break
    assert closed is not None, "no closing units"
    print(f"{idx:2d}. omega ({len(acl)},{len(bcl)})  N(a)={norm(a)}  N(b)={norm(d)}")
    print(f"    a = prod{acl},  a-side pi' = {[UN[k] for k in aunits]}")
    print(f"    b = a' = {d},  b-classes {bcl},  b-side pi' = {[UN[v] for v in closed]}  -> b' = a exactly")

print("\nAll sixteen Gaussian two-cycles verified exactly (integer arithmetic throughout).")
print("Over Z, sign-twisted derivatives p'=+-1 provably retain the 59-prime barrier;")
print("over Z[i], fourth roots of unity close the analogous problem at seven primes.")
