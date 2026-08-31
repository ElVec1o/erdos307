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
print("part 3 (non-principal prime sums) lives in uniform_nonprincipal_check.gp");
}
quit;
