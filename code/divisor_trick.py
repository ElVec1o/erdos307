"""EULER-STYLE DIVISOR TRICK for derivative 2-cycles.
Frames: M = M0*r (r a free prime), N fixed. Delta(r) = r*Delta0 - M0*N', linear in r,
where Delta0 = M0*N - M0'*N'.  Divisibility Delta(r) | (M*N'+N^2) becomes:
   d := r*Delta0 - M0*N'  must divide  K := Delta0*N^2 + (M0*N')^2   [CONSTANT in r].
Algorithm per frame (M0, N): factor K; for each divisor d ≡ -M0*N' (mod Delta0), d>0:
   r = (d + M0*N')/Delta0 ; p = (M0*r*N' + N^2)/d ; q = (M'(r)*N + (M0*r)^2)/d
   check r,p,q prime, coprimality, distinctness  =>  EXPLICIT 2-CYCLE (= Erdos #307 solution).
Verify algebra exactly + run a frame sweep collecting near-miss statistics."""
from sympy import factorint, primerange, isprime, divisors, gcd
from math import prod
import itertools, random, time
random.seed(307)

def ader(n):
    f=factorint(n); return sum(n*e//p for p,e in f.items())

# --- algebraic identity check: Delta(r)*p_num_const relation ---
ok=True
for _ in range(300):
    M0 = prod(random.sample(list(primerange(2,50)),2))
    N  = prod(random.sample([x for x in primerange(2,80) if M0%x],3))
    M0p, Npr = ader(M0), ader(N)
    D0 = M0*N - M0p*Npr
    if D0 == 0: continue
    K  = D0*N*N + (M0*Npr)**2
    r  = random.choice(list(primerange(100,1000)))
    d  = r*D0 - M0*Npr
    pnum = (M0*r)*Npr + N*N
    # identity: D0*pnum - M0*Npr*d == K  (so d | pnum  <=>  d | K)
    if D0*pnum - M0*Npr*d != K: ok=False
print("divisor-trick identity D0*pnum - M0*N'*d == K verified on 300 random instances:", ok)

# --- frame sweep: small frames, full divisor enumeration; count how far conditions get ---
t0=time.time()
stats = {"frames":0,"divisors":0,"r_int":0,"r_prime":0,"p_int":0,"pq_prime":0,"cycle":0}
small_primes = list(primerange(2,200))
near = []
for M0s_size in [1,2,3]:
  for Ns_size in [2,3]:
    for trial in range(400):
        M0s = random.sample(small_primes, M0s_size)
        pool = [x for x in small_primes if x not in M0s]
        Ns = random.sample(pool, Ns_size)
        M0, N = prod(M0s), prod(Ns)
        M0p, Npr = ader(M0), ader(N)
        D0 = M0*N - M0p*Npr
        if D0 <= 0: continue
        K = D0*N*N + (M0*Npr)**2
        if K <= 0 or K > 10**13: continue   # factorable budget
        stats["frames"] += 1
        for d in divisors(K):
            stats["divisors"] += 1
            if (d + M0*Npr) % D0: continue
            r = (d + M0*Npr)//D0
            stats["r_int"] += 1
            if r<=1 or not isprime(r) or M0%r==0 or N%r==0: continue
            stats["r_prime"] += 1
            M  = M0*r; Mp = M0p*r + M0
            pnum = M*Npr + N*N; qnum = Mp*N + M*M
            if pnum % d or qnum % d: continue   # qnum divisibility is the residual condition
            stats["p_int"] += 1
            p, q = pnum//d, qnum//d
            if p>1 and q>1 and isprime(p) and isprime(q) and p!=q and gcd(M*p, N*q)==1 \
               and M%p and N%q:
                stats["pq_prime"] += 1
                a, b = M*p, N*q
                if ader(a)==b and ader(b)==a:
                    stats["cycle"] += 1
                    print("***** EXPLICIT 2-CYCLE FOUND (Erdos #307 SOLVED):", a, b)
            elif p>1 and q>1:
                near.append((M0s, Ns, r, p, q))
print("sweep stats:", stats, f"({time.time()-t0:.0f}s)")
print("near misses (integral p,q, failed primality/coprimality):", len(near))
for nm in near[:5]: print("   ", nm)
print()
print("NOTE: zero cycles expected here — Barrier forbids hits below 10^56. Purpose: machinery")
print("validation + pipeline rates. The real hunt requires barrier-scale frames.")
