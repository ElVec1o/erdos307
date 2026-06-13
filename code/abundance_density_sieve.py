"""Density of prime-abundant n, and an exhaustive derivative-cycle sieve.
(1) Natural density of 'prime-abundant' n (sum of 1/p over p|n exceeds 1) -- the set qualifying
    for the cycle heuristics. Sieve-based, with a float margin.
(2) Exhaustive verification: no solution of n''=n with n not of the form p^p, up to N (sieve of
    arithmetic derivatives via smallest-prime-factor)."""
import numpy as np, time

N = 2*10**7
t0=time.time()
# smallest-prime-factor sieve
spf = np.arange(N+1, dtype=np.int64)
for i in range(2, int(N**0.5)+1):
    if spf[i]==i:
        sl = spf[i*i::i]
        sl[sl==np.arange(i*i, N+1, i)] = i
        spf[i*i::i] = sl
print(f"spf sieve done {time.time()-t0:.0f}s")

def factor(n):
    fs={}
    while n>1:
        p=int(spf[n]); e=0
        while n%p==0: n//=p; e+=1
        fs[p]=e
    return fs

# arithmetic derivative array via the prime-power sieve: D(n) = sum over prime powers p^e || n of e*(n/p)
t0=time.time()
import math
D = np.zeros(N+1, dtype=np.int64)            # n/p*e stays well within int64 for n <= 2e7
for p in range(2, N+1):
    if spf[p]==p:
        # for each multiple m of p: add (n/p)*v_p contribution incrementally:
        # standard: for prime powers q=p^e <= N: D(n) += n/p for each n divisible by p^e
        q=p
        while q<=N:
            D[q::q] += np.arange(q, N+1, q, dtype=np.int64)//p
            q*=p
print(f"derivative sieve done {time.time()-t0:.0f}s")

# exhaustive n''=n check (n>=2, excluding fixed points n'=n i.e. p^p, e.g. 4'=4, 27'=27)
t0=time.time()
sol=[]
for n in range(2, N+1):
    dn = D[n]
    if dn<=N and dn>=2 and D[dn]==n and dn!=n:
        sol.append((n,int(dn)))
print(f"solutions of n''=n, n'!=n, with both <= {N}: {sol}  ({time.time()-t0:.0f}s)")

# densities
t0=time.time()
# sum_{p|n} 1/p > 1  -- sieve a float array of reciprocal sums of distinct primes
R = np.zeros(N+1, dtype=np.float64)
sfmask = np.ones(N+1, dtype=bool)
for p in range(2, N+1):
    if spf[p]==p:
        R[p::p] += 1.0/p
        if p*p<=N: sfmask[p*p::p*p]=False
qual = R > 1.0 + 1e-12
border = np.abs(R-1.0) < 1e-9
print(f"density of prime-abundant n (sum 1/p|n > 1) below {N}: {qual[2:].sum()/ (N-1):.6f}")
print(f"    among squarefree: {(qual&sfmask)[2:].sum()/ sfmask[2:].sum():.6f}; borderline floats: {border.sum()}")
# density trend by dyadic ranges (does it stabilize?)
for lo in [10**5, 10**6, 10**7]:
    hi=min(2*lo, N)
    seg = qual[lo:hi]
    print(f"    density in [{lo},{hi}): {seg.sum()/len(seg):.6f}")
