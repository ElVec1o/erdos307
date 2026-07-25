#!/usr/bin/env python3
"""Rigorous enclosure of  delta = P( sum_p X_p / p > 1 ),  X_p ~ Bernoulli(1/p) independent
(the limiting abundance density of prop:density; open problem (iii): certify digits).

METHOD (everything explicit):
  Split S = S1 + T at P1:  S1 = sum_{p<=P1} X_p/p  (enclosed numerically),  T >= 0 (tail).
  * ENVELOPES: maintain U >= F_{S1} >= L pointwise on a grid of step h, via the two-point
    convolution F_new(x) = (1-1/p) F(x) + (1/p) F(x - 1/p).  The shift 1/p is rounded DOWN
    (in bins) for U and UP for L; since cdfs are nondecreasing this preserves U >= F >= L.
    Total argument blur <= (#primes) * h, measured directly by the final U-L gap.
  * LOWER: T >= 0  =>  delta >= P(S1 > 1) >= 1 - U(1).       (one-sided, no tail loss)
  * UPPER: delta <= P(S1 > 1-a) + P(T >= a) <= (1 - L(1-a)) + exp(1.36 - P1*a),
    from Chernoff with lambda = P1:  log E[e^{lam T}] <= sum_{p>P1} (e^{lam/p}-1)/p
      <= lam*s2 + 0.72*lam^2*s3     (e^x - 1 <= x + 0.72 x^2 for 0 <= x <= 1; here x=lam/p<1)
      <= P1*(1/P1) + 0.72*P1^2/(2*P1^2) = 1.36,
    using s2 = sum_{p>P1} p^-2 < sum_{n>P1} 1/(n(n-1)) = 1/P1  and  s3 < 1/(2 P1^2).
  * FLOAT SLACK: all envelope ops are float64; accumulated relative error < #primes * 3e-16;
    an absolute slack of 1e-9 is added on each side (orders above the true float error).

Checks: the inequality e^x-1 <= x+0.72x^2 on [0,1]; monotonicity of U,L; U >= L;
        a fast tier (P1=3000) for stability; the full tier (P1=30000, h=1e-7).
"""
import numpy as np
from sympy import primerange
from math import exp, log
import sys, time

# ---------- explicit-constant check: e^x - 1 <= x + 0.72 x^2 on [0,1] ----------
xs = np.linspace(0, 1, 100001)
worst = np.max(np.exp(xs) - 1 - xs - 0.72 * xs * xs)
assert worst <= 0, worst
print(f"constant check: max(e^x-1-x-0.72x^2) on [0,1] = {worst:.2e} <= 0  OK")

def enclose(P1, h, a):
    primes = list(primerange(2, P1 + 1))
    R = sum(1.0 / p for p in primes) + 0.2          # grid range with headroom
    n = int(R / h) + 2
    U = np.ones(n, dtype=np.float64)                # cdf of delta_0: F(x)=1, x>=0
    L = np.ones(n, dtype=np.float64)
    t0 = time.time()
    for idx, p in enumerate(primes):
        q = 1.0 / p
        s_dn = int(1.0 / (p * h))                   # floor
        s_up = s_dn + (0 if abs(s_dn * p * h - 1.0) < 1e-12 else 1)
        for arr, s in ((U, s_dn), (L, s_up)):
            if s >= n:
                arr *= (1.0 - q)                    # shifted part falls off the grid (F=0)
                continue
            head = arr[: n - s].copy()
            arr[s:] = (1.0 - q) * arr[s:] + q * head
            arr[:s] *= (1.0 - q)
        if idx % 500 == 0:
            print(f"  conv {idx}/{len(primes)}  {time.time()-t0:.0f}s", flush=True)
    i1 = round(1.0 / h)
    ia = round((1.0 - a) / h)
    slack = 1e-9
    tail = exp(1.36 - P1 * a)
    lo = (1.0 - U[i1]) - slack
    hi = (1.0 - L[ia]) + tail + slack
    # sanity: envelopes monotone (sampled), ordered
    ii = np.linspace(0, n - 1, 2000).astype(int)
    assert np.all(np.diff(U[ii]) >= -1e-12) and np.all(np.diff(L[ii]) >= -1e-12)
    assert np.all(U[ii] >= L[ii] - 1e-15)
    mid = 1.0 - 0.5 * (U[i1] + L[i1])
    print(f"P1={P1} h={h:g} a={a:g}: delta in [{lo:.5f}, {hi:.5f}]  width {hi-lo:.2e}  "
          f"(midpoint~{mid:.5f}, tail term {tail:.1e}, {time.time()-t0:.0f}s)")
    return lo, hi

if sys.argv[1:] and sys.argv[1] == "full":
    enclose(30000, 1e-7, 1e-3)
else:
    enclose(3000, 1e-6, 3e-3)   # fast tier
