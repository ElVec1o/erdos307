"""One-correction construction: sweep correction primes r ABOVE the feasibility threshold
r* = CB/g, plus a residue census of m = (-CB) mod g (the obstruction scale for integer r at
minimal numerator)."""
import random, time
from fractions import Fraction
from math import prod
from sympy import primerange, isprime, nextprime
random.seed(307)
PRIMES = list(primerange(2, 400))[:72]

def sums(idx):
    P=[p for p in PRIMES if idx[p]==0]; Q=[p for p in PRIMES if idx[p]==1]
    B=prod(P); D=prod(Q); A=sum(B//p for p in P); C=sum(D//q for q in Q)
    return P,Q,A,B,C,D

# regenerate partitions same as census.py (same seed & procedure, shortened)
def rand_idx():
    idx={p:random.choice([0,1]) for p in PRIMES}; idx[2]=0; return idx
def floateval(idx):
    s=sum(1.0/p for p in PRIMES if idx[p]==0); t=sum(1.0/p for p in PRIMES if idx[p]==1)
    return s,t
records=[]
t_end=time.time()+420
n=0
while time.time()<t_end and n<200:
    n+=1
    idx=rand_idx(); s,t=floateval(idx)
    cur=abs(1-s*t) if s*t<1 else 1; temp=0.05
    for step in range(4000):
        p=random.choice(PRIMES[1:]); old=idx[p]; new=random.choice([0,1,2])
        if new==old: continue
        idx[p]=new; s,t=floateval(idx)
        val=(1-s*t) if s*t<1 else 1.0
        if val<cur or random.random()<temp: cur=val
        else: idx[p]=old
        temp*=0.999
    P,Q,A,B,C,D=sums(idx)
    g=B*D-A*C
    if g>0 and len(P)>=2 and len(Q)>=2: records.append((float(Fraction(g,B*D)),dict(idx)))
records.sort(key=lambda r:r[0])
print(f"{len(records)} partitions regenerated; best eps={records[0][0]:.2e}")

# residue census: relative size of m=(-CB) mod g  (uniform => log10(m/g) ~ 0)
import math
logratios=[]
for epsf,idx in records:
    P,Q,A,B,C,D=sums(idx)
    g=B*D-A*C; CB=C*B
    m=(-CB)%g
    if m==0:
        print("  m=0: r exactly integer!", flush=True)
    else:
        logratios.append(math.log10(m/g))
logratios.sort()
print(f"residue census m=(-CB) mod g over {len(logratios)} partitions: "
      f"min log10(m/g)={logratios[0]:.2f}, 10th pct={logratios[len(logratios)//10]:.2f}, median={logratios[len(logratios)//2]:.2f}")
print("(uniform-heuristic expectation: median ~ -0.3; structure would show as anomalies)")

# best partition: sweep r in (r*, r*+band], exact u-check
epsf,idx=records[0]
P,Q,A,B,C,D=sums(idx)
g=B*D-A*C; CB=C*B
rstar=CB//g
print(f"\nbest partition: |P0|={len(P)} |Q0|={len(Q)} eps={epsf:.2e}, r* = CB/g ~ {rstar}")
r=int(rstar); tried=0; t0=time.time()
r=nextprime(r)
sols=[]
while tried<20000 and time.time()-t0<300:
    if r not in P and r not in Q:
        numu=r*g-CB
        if numu>0:
            denu=D*(A*r+B)
            tried+=1
            if denu%numu==0:
                u=denu//numu
                if isprime(u) and u not in P and u not in Q and u!=r:
                    print(f"*** SOLUTION r={r} u={u}"); sols.append((r,u))
    r=nextprime(r)
print(f"two-correction sweep above r*: {tried} primes tried, {len(sols)} solutions (expected 0; census purpose)")
