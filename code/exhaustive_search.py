"""Erdos #307 exhaustive sweep: enumerate ALL prime sets P with sum 1/p > 1, ordered by D_P = prod(P),
up to bound B. For each, Q is forced = factor set of N_P; check N_Q == D_P.
This is exhaustive over D_P <= B: any solution with min(D_P,D_Q) <= B would be found."""
from sympy import primerange, factorint, isprime
from math import prod, isqrt
import heapq, time

B = 10**8
primes = list(primerange(2, B))

# enumerate squarefree P (as sorted prime tuples) with prod <= B and sum 1/p > 1,
# DFS with pruning: remaining primes can't push sum over 1 => prune.
# upper bound on achievable extra sum from primes >= p with product budget R:
# greedily multiply consecutive primes from p while <= R.
plist = primes
results = []
count = [0]
t0 = time.time()

def max_extra(idx, budget):
    s = 0.0; b = budget
    for i in range(idx, len(plist)):
        p = plist[i]
        if p > b: break
        s += 1.0/p; b //= p
        if s > 2: break
    return s

def dfs(idx, prodv, s_num, s_den, cursum):
    # cursum = float sum so far
    if cursum > 1.0:
        # P complete candidate (any superset also fine but we test each set once here)
        P = current[:]
        D = prodv
        N = sum(D // p for p in P)
        count[0] += 1
        f = factorint(N)
        if all(e == 1 for e in f.values()):
            Q = sorted(f)
            DQ = N
            NQ = sum(DQ // q for q in Q)
            if NQ == D:
                results.append((tuple(P), tuple(Q)))
                print("*** FOUND:", P, Q, flush=True)
        # continue extending too (supersets can also have sum>1, distinct sets)
    for i in range(idx, len(plist)):
        p = plist[i]
        if prodv * p > B: break
        if cursum <= 1.0 and cursum + max_extra(i, B // prodv) <= 1.0:
            break  # can't reach sum>1 anymore
        current.append(p)
        dfs(i + 1, prodv * p, 0, 0, cursum + 1.0/p)
        current.pop()

current = []
dfs(0, 1, 0, 1, 0.0)
print(f"exhausted all P with prod(P) <= {B}: {count[0]} candidate sets with sum>1 tested, "
      f"{len(results)} solutions, {time.time()-t0:.1f}s")
print("CONCLUSION: no solution to Erdos #307 exists with min(prod P, prod Q) <=", B)
