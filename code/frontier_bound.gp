/* The near-miss frontier obeys a double-logarithmic law (prop:frontier).
 *
 * For squarefree a, rigidity gives gcd(a,a') = 1, so U = supp(a) u supp(a') consists of
 * |U| = omega(a) + omega(a') distinct primes and prod_{p in U} p divides a a'. AM-GM gives
 *     sum_{p in U} 1/p = sigma(a) + sigma(a') >= 2 sqrt(r),   r = sigma(a) sigma(a'),
 * and the sum is at most T_|U| by extremality of the smallest primes, so r <= (T_|U| / 2)^2.
 * For the size, Pi_|U| <= a a' = a^2 sigma(a) <= X^2 sigma_max(X), which bounds |U| by n(X).
 * Hence R(X) = max{r(a) : a <= X} <= (T_{n(X)} / 2)^2, unconditionally.
 *
 * The bound tracks the measured frontier of prop:nearmiss from above at every decade, and by
 * Mertens T_{n(X)} = loglog(X^2 sigma_max) + M + o(1), so
 *     R(X) <= (1/4)(loglog X^2 + M + o(1))^2,
 * a doubly logarithmic law. That is why the measured frontier crawls and why extrapolating its
 * per-decade advance is worthless. The bound reaches 1 exactly when T_n >= 2, i.e. n >= 59, i.e.
 * X >= 2.0942e56 -- the constant of thm:barrier, recovered from the frontier side by an independent
 * route and agreeing to all printed digits.
 *
 * Run:  gp -q -f frontier_bound.gp
 */

\p 30
{
my(obs, T, P, wmax, smax, nmax, bound, e);
print("QUANTITATIVE FRONTIER BOUND.");
print("r = sigma(a)sigma(a'); U = supp(a) u supp(a') disjoint by rigidity.");
print("AM-GM: sum_{p in U} 1/p = sigma(a)+sigma(a') >= 2 sqrt(r), and the sum is <= T_|U|,");
print("so    r <= (T_|U| / 2)^2.");
print("Size:  D = a a' = a^2 sigma(a) <= X^2 sigma_max(X), and D >= Pi_|U|, so |U| <= n_max(X).");
print("Hence  R(X) := max{ r(a) : a <= X }  <=  (T_{n_max(X)} / 2)^2.");
print("");
obs = [0.333, 0.345, 0.502, 0.502, 0.536, 0.554];
print("  X     | omega_max | sigma_max | n_max | T_nmax  |  BOUND   | observed max r");
for(e = 2, 12,
  my(X); X = 10^e;
  wmax = 0; P = 1;
  while(P*prime(wmax+1) <= X, wmax++; P *= prime(wmax));
  smax = sum(i = 1, wmax, 1.0/prime(i));
  nmax = 0; P = 1;
  while(P*prime(nmax+1) <= X^2*smax, nmax++; P *= prime(nmax));
  T = sum(i = 1, nmax, 1.0/prime(i));
  bound = (T/2)^2;
  printf("  10^%-2d |    %2d     |  %.4f   |  %2d   | %.5f | %.5f  | %s\n",
     e, wmax, smax, nmax, T, bound,
     if(e <= 7, Str(obs[e-1]), "  --"));
);
print("");
print("The bound is unconditional and tracks the empirical frontier from above.");
print("It also gives the growth rate: n_max(X) ~ the count of primes with Pi_n <= X^2,");
print("so T_{n_max} ~ loglog(X^2) + M and R(X) ~ ((loglog X^2 + M)/2)^2: the frontier can only");
print("climb like (loglog X)^2/4. Reaching r = 1 needs T_n >= 2, i.e. n >= 59, i.e.");
my(P59); P59 = prod(i=1,59,prime(i));
printf("   X^2 sigma_max >= Pi_59 = %.4e,  so X >= %.4e\n", 1.0*P59, sqrt(1.0*P59/2.0));
}
quit;
