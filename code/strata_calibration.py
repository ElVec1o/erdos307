#!/usr/bin/env python3
"""Wall-4 pass: calibrate the exact-coincidence heuristic on the deviation strata.

The census (prop:halfplane) found 23 integral-deviation pairs with ab <= 1e7. The
average-case model prices each candidate (a, s) -> b = a' - as at P[b | b'-a] ~ 1/b.
Running the IDENTICAL enumeration (same filters: b squarefree, coprime, in range,
b != a) with 1/b in place of the exact test yields the model's expected count E.

  E vs observed 23  — the transfer test wall 4 is about, run where truth is checkable.

Also: per-height comparison (counts up to 1e4, 1e5, 1e6, 1e7 — the log-law), and the
same calibration for the single-variable chain equation a'' + a' = a (observed 4).
"""
from math import isqrt, gcd, log
LIM = 10**7
spf = list(range(LIM + 1))
for i in range(2, isqrt(LIM) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j: spf[j] = i

def sf_deriv(n):
    if n > LIM: return None
    ps, m = [], n
    while m > 1:
        p = spf[m]; m //= p
        if m % p == 0: return None
        ps.append(p)
    return sum(n // p for p in ps)

# ---------- pair calibration: identical enumeration, 1/b vs exact ----------
E = 0.0; obs = 0
E_at = {10**4: 0.0, 10**5: 0.0, 10**6: 0.0, 10**7: 0.0}
obs_at = {10**4: 0, 10**5: 0, 10**6: 0, 10**7: 0}
for a in range(2, 3164):
    da = sf_deriv(a)
    if da is None: continue
    b = da % a or a
    while b <= LIM // a:
        if b != a and b > 1 and gcd(a, b) == 1:
            db = sf_deriv(b)
            if db is not None:
                # model price for the second exact condition b | b' - a
                for X in E_at:
                    if a * b <= X: E_at[X] += 1.0 / b
                E += 1.0 / b
                s, r1 = divmod(da - b, a)
                t, r2 = divmod(db - a, b)
                if r1 == 0 and r2 == 0:
                    obs += 1
                    for X in obs_at:
                        if a * b <= X: obs_at[X] += 1
        b += a
print("PAIR CALIBRATION (integral-deviation pairs; identical filters, 1/b price):")
print(f"  model E = {E:.1f}   observed = {obs}   ratio obs/E = {obs/E:.2f}")
for X in sorted(E_at):
    print(f"  ab <= 1e{len(str(X))-1}:  E = {E_at[X]:6.1f}   observed = {obs_at[X]}")

# ---------- chain equation a''+a'=a: price 1/spread of a'' ----------
E2 = 0.0; obs2 = 0
for a in range(6, LIM + 1):
    da = sf_deriv(a)
    if da is None or da < 2: continue
    dda = sf_deriv(da)
    if dda is None: continue
    # exact test
    if dda + da == a and gcd(a, da) == 1: obs2 += 1
    # model: target a - da must be hit by a''; price ~ 1/(typical spread of a'' at this size)
    # spread of n' for n ~ da is ~ da (values n' range over [~2 sqrt n, n log log n]) — price 1/da
    if 0 < a - da: E2 += 1.0 / da
print(f"\nCHAIN CALIBRATION (a''+a'=a): model E = {E2:.1f}   observed = {obs2}   "
      f"ratio obs/E = {obs2/E2:.2f}")
print(f"  (log-law check: observed {obs2} in [2,1e7], c = {obs2/log(LIM):.2f} per log)")
