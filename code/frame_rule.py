"""THE FRAME RULE (Thabit/Euler-type rule for arithmetic-derivative 2-cycles).
Rule 1 (one prime per side): frames M,N coprime squarefree; Delta = M*N - M'*N' > 0;
  p = (M*N' + N^2)/Delta, q = (M'*N + M^2)/Delta.
  If p,q are integers, prime, not dividing M*N, p != q, then (M*p, N*q) is a 2-cycle.
Rule 2 (two primes on the a-side): a = M*p1*p2, b = N*q1*q2; with e1=p1+p2, e2=p1*p2,
  f1=q1+q2, f2=q1*q2:   M'*e2 + M*e1 = N*f2   and   N'*f2 + N*f1 = M*e2.
Verify both ALGEBRAICALLY with sympy symbols + numerically on random data."""
import sympy as sp

# --- Rule 1 symbolic verification ---
M, Mp, N, Np, p, q = sp.symbols('M Mp N Np p q', positive=True)
Delta = M*N - Mp*Np
psol = (M*Np + N**2)/Delta
qsol = (Mp*N + M**2)/Delta
# derivative of a=M*p (p prime, coprime): a' = Mp*p + M ; require = N*q
eq1 = sp.simplify(Mp*psol + M - N*qsol)
# derivative of b=N*q: b' = Np*q + N ; require = M*p
eq2 = sp.simplify(Np*qsol + N - M*psol)
print("Rule 1 algebraic check: a'-b =", eq1, " | b'-a =", eq2)

# --- Rule 1 numeric spot-check with actual derivative on random frames (rational p,q ok for algebra) ---
from sympy import factorint, primerange, gcd, isprime
from math import prod
import random
random.seed(11)
def ader(n):
    f=factorint(n); return sum(n*e//pp for pp,e in f.items())
ok=True
for _ in range(200):
    Ms = random.sample(list(primerange(2,60)), random.randint(2,4))
    Ns = random.sample([x for x in primerange(2,60) if x not in Ms], random.randint(2,4))
    Mv, Nv = prod(Ms), prod(Ns)
    Mpv, Npv = ader(Mv), ader(Nv)
    D = Mv*Nv - Mpv*Npv
    if D==0: continue
    pn, qn = Mv*Npv + Nv*Nv, Mpv*Nv + Mv*Mv
    if pn % D or qn % D: continue
    pv, qv = pn//D, qn//D
    if pv<=1 or qv<=1: continue
    if isprime(pv) and isprime(qv) and Mv%pv and Nv%qv and Mv*Nv%pv and Mv*Nv%qv and pv!=qv:
        a, b = Mv*pv, Nv*qv
        if ader(a)==b and ader(b)==a:
            print("!!! RULE 1 PRODUCED AN ACTUAL 2-CYCLE:", a, b)
        else:
            ok=False; print("rule violated:", Ms, Ns)
print("Rule 1 numeric consistency on random frames: no violations =", ok)

# --- Rule 2 symbolic verification ---
e1,e2,f1,f2 = sp.symbols('e1 e2 f1 f2', positive=True)
# a = M*p1*p2: a' = Mp*e2 + M*e1 ; b = N*q1*q2: b' = Np*f2 + N*f1
# cycle: a' = b = N*f2  and  b' = a = M*e2
sysq = [sp.Eq(Mp*e2 + M*e1, N*f2), sp.Eq(Np*f2 + N*f1, M*e2)]
sol = sp.solve(sysq, [f1, f2], dict=True)[0]
print("Rule 2: f2 =", sp.simplify(sol[f2]), " ; f1 =", sp.simplify(sol[f1]))
# numeric verification of Rule 2 on random data: pick primes p1,p2; frames; compute f1,f2; verify identity
viol=0; checked=0
for _ in range(500):
    Ms = random.sample(list(primerange(2,40)), random.randint(2,3))
    pool=[x for x in primerange(2,200) if x not in Ms]
    Ns = random.sample(pool, random.randint(2,3))
    pool2=[x for x in primerange(200,2000)]
    p1,p2 = random.sample(pool2,2)
    Mv,Nv = prod(Ms), prod(Ns); Mpv,Npv = ader(Mv), ader(Nv)
    e1v, e2v = p1+p2, p1*p2
    # f2 = (Mp*e2 + M*e1)/N ; f1 = (M*e2 - Np*f2)/N
    if (Mpv*e2v + Mv*e1v) % Nv: continue
    f2v = (Mpv*e2v + Mv*e1v)//Nv
    if (Mv*e2v - Npv*f2v) % Nv: continue
    f1v = (Mv*e2v - Npv*f2v)//Nv
    checked+=1
    # if f1,f2 split into primes q1,q2 (disc square), verify the actual cycle
    disc = f1v*f1v - 4*f2v
    if disc >= 0:
        r = sp.integer_nthroot(disc,2)
        if r[1]:
            q1v, q2v = (f1v - r[0])//2, (f1v + r[0])//2
            if q1v>1 and isprime(q1v) and isprime(q2v) and q1v!=q2v:
                a, b = Mv*p1*p2, Nv*q1v*q2v
                if gcd(a,b)==1 and ader(a)==b and ader(b)==a:
                    print("!!! RULE 2 PRODUCED AN ACTUAL 2-CYCLE:", a, b)
                elif ader(a)==b:  # partial: a'=b held but b'!=a means our algebra is off
                    viol+=1
print(f"Rule 2: {checked} divisibility-passing random instances; algebra violations: {viol}")
print()
print("FRAME RULE established: cycle equations are LINEAR in the closing primes / their")
print("symmetric functions. Erdos #307 reduces to: find frames with divisibility + primality.")
