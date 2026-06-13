"""Conditional mass and the local congruence lemma.
(1) For qualifying squarefree a, b=a': how does the mass M(b)=sum 1/q over q|b compare to the
    required 1/s? Distribution + tail probability.
(2) Verify the local congruence lemma: q | b=a'  <=>  sum_{p|a} p^{-1} ≡ 0 (mod q); and the mod-3
    counting form b1+2b2≡0 (mod 3) when 3|a."""
import numpy as np, time
from fractions import Fraction
N = 3*10**7
spf = np.arange(N+1, dtype=np.int64)
for i in range(2, int(N**0.5)+1):
    if spf[i]==i:
        sl = spf[i*i::i]
        sl[sl==np.arange(i*i, N+1, i)] = i
        spf[i*i::i] = sl

def factors(n):
    fs=[]
    while n>1:
        p=int(spf[n])
        fs.append(p)
        while n%p==0: n//=p
    return fs
def is_sf(n):
    while n>1:
        p=int(spf[n])
        if (n//p)%p==0: return False
        n//=p
        while n%p==0: return False
    return True
def sf_factors(n):
    fs=[]
    while n>1:
        p=int(spf[n]); fs.append(p); n//=p
        if n%p==0: return None
    return fs

t0=time.time()
import math, collections
samples=0; b_sf=0; tail_hits=0
gaps=[]; masses=[]; needed=[]
rng=np.random.default_rng(7)
cand = rng.integers(2, 2*10**7, size=4_000_000)
for n in cand:
    n=int(n)
    fs = sf_factors(n)
    if fs is None: continue
    s = sum(Fraction(1,p) for p in fs)
    if s <= 1: continue
    samples += 1
    b = sum(n//p for p in fs)         # = a' since squarefree
    fb = sf_factors(b) if b<=N else None
    if b<=N and fb is not None:
        b_sf += 1
        Mb = float(sum(1.0/q for q in fb))
        need = float(1/s)
        masses.append(Mb); needed.append(need); gaps.append(need-Mb)
        if Mb >= need: tail_hits += 1
    if samples>=120000: break
gaps=np.array(gaps); masses=np.array(masses)
print(f"{samples} qualifying squarefree a sampled; b=a' squarefree rate: {b_sf/samples:.3f}")
print(f"    mass M(b): mean={masses.mean():.4f}, median={np.median(masses):.4f}, max={masses.max():.4f}")
print(f"    required 1/s: mean={np.mean(needed):.4f}")
print(f"    P(M(b) >= 1/s) empirical = {tail_hits}/{len(gaps)} = {tail_hits/len(gaps):.5f}")
print(f"    gap (1/s - M(b)) percentiles: 1%={np.percentile(gaps,1):.4f} 10%={np.percentile(gaps,10):.4f} 50%={np.percentile(gaps,50):.4f}")
print(f"    ({time.time()-t0:.0f}s)")

# local congruence lemma verification on exact data
from sympy import isprime
ok_all=True; checked=0
for n in cand[:200000]:
    n=int(n)
    fs = sf_factors(n)
    if fs is None or len(fs)<2: continue
    b = sum(n//p for p in fs)
    fb = sf_factors(b) if b<=N else None
    if fb is None: continue
    for q in fb:
        inv_sum = sum(pow(p,-1,q) for p in fs if p%q) % q if all(p%q for p in fs) else None
        if inv_sum is not None and inv_sum != 0: ok_all=False
    checked+=1
    if checked>=3000: break
print(f"local lemma [q|a' => sum p^-1 ≡ 0 mod q] verified on {checked} cases: {ok_all}")
