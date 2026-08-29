/* The cost of a near-miss: thm:barrier as a function of r (cor:cost).
 *
 * For squarefree a with r = r(a) = sigma(a)sigma(a'), rigidity makes
 * U = supp(a) u supp(a') a set of omega(a)+omega(a') distinct primes, and AM-GM gives
 *      sum_{p in U} 1/p = sigma(a) + sigma(a') >= 2 sqrt(r).
 * Extremality of the smallest primes caps that sum at T_|U|, so with
 *      n(r) := min{ n : T_n >= 2 sqrt(r) }
 * every a with r(a) >= r has |U| >= n(r), hence a a' >= Pi_{n(r)} and, exactly as in thm:barrier,
 *      min(a, a') >= sqrt( Pi_{n(r)} / T_{n(r)} ).
 * At r = 1 this returns n = 59 and 2.0929e56, the constant of thm:barrier, so the general form
 * contains the barrier as its endpoint.
 *
 * The table shows why the frontier crawls: each increment in r costs exponentially in the product.
 * The swept record r = 0.554 needs only a >~ 1.0e4, which is why it is visible below 10^7; r = 0.9
 * already needs a >~ 4.4e30 and r = 0.99 needs a >~ 4.7e52.
 *
 * Run:  gp -q -f nearmiss_cost.gp
 */

\p 30
{
my(rs, n, T, P);
print("    r      | n(r) |     Pi_{n(r)}      |  T_{n(r)}  | min(a,a') >=");
rs = [0.3, 0.4, 0.5, 0.554, 0.6, 0.7, 0.8, 0.9, 0.95, 0.99, 0.999, 1.0];
foreach(rs, r,
  n = 1; T = 0;
  while(T < 2*sqrt(r), T += 1.0/prime(n); n++);
  n = n - 1;
  T = sum(i = 1, n, 1.0/prime(i));
  P = prod(i = 1, n, prime(i));
  printf("  %-8.5f |  %3d | %18.4e |  %.6f  | %.4e\n", r, n, 1.0*P, T, sqrt(1.0*P/T));
);
print("");
print("At r = 1: n = 59 and min(a,a') >= 2.0929e56, recovering thm:barrier exactly.");
}
quit;
