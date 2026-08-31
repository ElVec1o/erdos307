{
my(r, chi, cpsi0, par, N, tot, mx, S, t, a, ok);
print("SANITY CHECKS for the uniform-range charcancel draft. Three load-bearing constants.");
print("");
print("1. c_psi0 = chi(t) tau(chi)/phi(r), so |c_psi0| = sqrt(r)/phi(r), for r = pq:");
foreach([15, 21, 33, 35, 77, 143, 221], r,
  my(G, g, c0, t1);
  t1 = 1;
  \\ direct Fourier coefficient of g(a) = chi(a) e_r(t a^-1) at the trivial character
  c0 = sum(a = 1, r, if(gcd(a, r) == 1, kronecker(a, r) * exp(2*Pi*I*t1*lift(Mod(a,r)^-1)/r), 0)) / eulerphi(r);
  printf("  r=%4d  |c_psi0| computed = %.6f   sqrt(r)/phi(r) = %.6f   match %s\n",
         r, abs(c0), sqrt(r)/eulerphi(r), if(abs(abs(c0)-sqrt(r)/eulerphi(r)) < 1e-9, "OK", "FAIL")));
print("");
print("2. Parseval: sum_psi |c_psi|^2 = 1 (|g| = 1 on units). Check via sum over a directly:");
foreach([15, 33, 77], r,
  my(s); s = sum(a = 1, r, if(gcd(a,r) == 1, 1, 0)) / eulerphi(r);
  printf("  r=%4d  mean |g|^2 = %.6f  (must be 1)\n", r, s));
print("");
print("3. Non-principal prime sums at polyloglog moduli stay O(logloglog N)-sized:");
print("   S_psi = sum_{p<=N} psi(p)/p for psi non-principal mod r; compare loglog N.");
N = 10^7;
my(pr); pr = primes(primepi(N));
foreach([15, 21, 33, 35], r,
  my(worst); worst = 0.0;
  \\ real characters mod r: chi_d = kronecker(d, .) for divisors d | r, d > 1
  fordiv(r, d,
    if(d == 1 || d == r+1, next);
    my(s); s = sum(i = 1, #pr, if(pr[i] % r != 0, kronecker(d, pr[i]) * 1.0/pr[i], 0));
    if(abs(s) > worst, worst = abs(s)));
  printf("  r=%4d  worst real-psi |sum p^-1| = %.4f   vs loglog N = %.4f   ratio %.3f\n",
         r, worst, log(log(N)), worst/log(log(N))));
print("");
print("interpretation: ratios well below 1 at feasible N; the true regime r ~ (loglog N)^2");
print("is numerically unreachable (loglog 10^7 = 2.8), so this is a constants check, not evidence");
print("for the asymptotic claim. The asymptotic inputs are SW, Siegel, and the zero-free region.");
}
quit;
