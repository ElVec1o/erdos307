/* The mass window and the forced core (prop:window).
 *
 * For a two-cycle with |U| = n, the masses are positive with product 1 and sum at most T_n, so both
 * lie between the roots of z^2 - T_n z + 1: sigma in [1/t_n, t_n]. At n = 59 that window is
 * [0.952682, 1.049668] -- each member's mass is pinned within five per cent of 1. Requiring
 * T_k >= 1/t_n for the smaller member reproduces prop:split's thresholds exactly (k >= 3 for
 * n <= 68, k >= 2 from n = 69, k >= 1 at n = 1413).
 *
 * Forcing: if p is absent from U then the n primes carry at most T_{n+1} - 1/p, and sigma(U) > 2
 * needs 1/p < T_{n+1} - 2. So every prime with 1/p >= T_{n+1} - 2 lies in U. At n = 59 that is
 * every prime up to 167, 39 of the 59.
 *
 * This accounts for the level-59 enumeration count. The 39 forced primes carry mass 1.91162, so the
 * remaining 20 must supply more than 0.08838 from primes above 167, and the twenty smallest such
 * primes reach exactly that at 277. The free part is a choice of 20 primes from a narrow band,
 * which is why the admissible count is 49,961 rather than astronomical.
 *
 * Run:  gp -q -f forced_core.gp
 */

\p 20
{
my(n, T1, thr, p, cnt, last);
print("FORCED PRIMES. If a prime p is absent from U with |U| = n, the largest mass U can carry");
print("is T_{n+1} - 1/p (the first n+1 primes, minus p). Since sigma(U) > 2 this needs");
print("     1/p < T_{n+1} - 2,");
print("so every prime p with 1/p >= T_{n+1} - 2 must LIE IN U.");
print("");
print("    n   |  T_{n+1} - 2  | forced: all p <= | count");
for(n = 59, 72,
  T1 = sum(i = 1, n+1, 1.0/prime(i));
  thr = T1 - 2.0;
  if(thr <= 0, next);
  last = 0; cnt = 0;
  forprime(q = 2, 100000, if(1.0/q >= thr, last = q; cnt++, break));
  printf("  %5d |   %.6f    |      %5d       |  %3d\n", n, thr, last, cnt);
);
print("");
print("At n = 59 every prime up to 167 is forced -- 39 of the 59 -- so two thirds of the");
print("support is determined before any search begins. The forcing decays as n grows and");
print("is empty once T_{n+1} - 2 exceeds 1/2, i.e. once n+1 primes can carry mass 2.5.");
}
quit;
\p 20
{
my(T39, rest, need, n, s, cnt, maxp);
T39 = 0.0; cnt = 0;
forprime(p = 2, 167, T39 += 1.0/p; cnt++);
print("At |U| = 59 the forced core is every prime <= 167: ", cnt, " primes, mass ", T39);
need = 2.0 - T39;
print("The remaining ", 59-cnt, " primes are all > 167 and must supply mass > ", need);
printf("  average reciprocal needed: %.6f, i.e. average prime about %.0f\n", need/(59-cnt), (59-cnt)/need);
s = 0.0; maxp = 0;
forprime(p = 173, 100000,
  s += 1.0/p; maxp = p;
  if(s >= need, break));
my(k); k = 0; forprime(p = 173, maxp, k++);
print("  the ", 59-cnt, " must be drawn from a short window: the smallest ", k,
      " primes above 167 already reach that mass, at p = ", maxp);
print("");
print("So the level-59 support is 39 forced primes plus 20 chosen from a narrow band,");
print("which is why the admissible count is only 49,961 rather than astronomically many.");
print("The same accounting at level 60 forces 27 primes and leaves 33 free, and the");
print("forcing has decayed to 9 primes by level 68 -- the window prop:split says a level");
print("search must cross.");
}
quit;
