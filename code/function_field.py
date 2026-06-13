"""Function-field lens verification: arithmetic derivative over F_q[t].
For monic f with factorization prod P_i^{e_i}: f'_arith := sum e_i * f / P_i  (coefficients in F_q).
Claims to verify exhaustively for small q, deg:
 (1) deg(f'_arith) <= deg(f) - 1 for all nonconstant f  (the degree-drop lemma)
 (2) hence NO 2-cycles f'=g, g'=f with f != g  (and no fixed points f'=f)
 (3) char-p quirk: (P^p)'_arith = 0."""
from sympy import GF, Poly, symbols, factor_list
t = symbols('t')

def check_field(q, maxdeg):
    K = GF(q)
    # enumerate monic polys of degree 1..maxdeg over F_q
    from itertools import product
    polys = []
    for d in range(1, maxdeg+1):
        for coeffs in product(range(q), repeat=d):
            c = [1] + list(coeffs)
            polys.append(Poly(c, t, domain=K))
    def ader(f):
        # arithmetic derivative via factorization
        fl = f.factor_list()
        const, facs = fl
        res = Poly(0, t, domain=K)
        for (P, e) in facs:
            if P.degree() == 0: continue
            res = res + e * f.quo(P)
        return res
    deg_ok = True; cycles = []; fixed = []
    table = {}
    for f in polys:
        df = ader(f)
        table[f.rep] = (f, df)
        if df.degree() is not None and df.degree() >= f.degree() and not df.is_zero:
            deg_ok = False
            print(f"  DEGREE VIOLATION: f={f.as_expr()}, f'={df.as_expr()}")
        if df == f and not f.is_zero:
            fixed.append(f.as_expr())
    # 2-cycles: f' = g, g' = f, f != g  (g must be monic to be in table; check directly)
    for f in polys:
        g = ader(f)
        if g.is_zero or g.degree() is None or g.degree() < 1: continue
        # make monic? arithmetic derivative needn't be monic; apply ader directly to g:
        gg = ader(g)
        if gg == f and g != f:
            cycles.append((f.as_expr(), g.as_expr()))
    print(f"F_{q}[t], deg<= {maxdeg}: degree-drop holds for all = {deg_ok}; fixed points: {len(fixed)}; 2-cycles: {len(cycles)}")
    return deg_ok, fixed, cycles

for q, md in [(2,7),(3,5),(5,4)]:
    check_field(q, md)

# char-p quirk: (P^p)' = 0
K=GF(2); P=Poly([1,1,1],t,domain=K)  # t^2+t+1 irreducible over F_2
f=P**2
fl=f.factor_list(); res=Poly(0,t,domain=K)
for (Q,e) in fl[1]:
    if Q.degree()>0: res = res + e*f.quo(Q)
print("char-2 quirk: (P^2)'_arith for irreducible P over F_2:", res.as_expr(), " (= 0 since e=p=2≡0)")
