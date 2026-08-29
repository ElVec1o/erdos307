/* The free band, and why exactly one level is finite (prop:band).
 *
 * If q = max(U) and |U| = n, the other n-1 primes carry at most T_{n-1}, so sigma(U) > 2 forces
 *      q < 1/(2 - T_{n-1})     whenever T_{n-1} < 2.
 *
 * For n <= 58 no admissible support exists at all (T_n < 2). For n = 59 the hypothesis holds,
 * T_58 = 1.998740, so q < 793.68 and max(U) <= 787. For n >= 60 it fails, T_59 = 2.002350 > 2, and
 * there is no bound: appending any prime whatever to the first 59 leaves an admissible support.
 *
 * So the level-by-level enumeration is finite at 59 and infinite from 60, and the entire switch is
 * the single fact T_58 < 2 < T_59. This is prop:levelbarrier in its sharpest form.
 *
 * With prop:window the level is closed from both sides: U contains all 39 primes <= 167 and lies
 * inside the 138 primes <= 787, so the free part chooses 20 from the 99 candidates in (167, 787].
 * That is C(99,20) = 4.288e20 unconstrained; the mass condition cuts it to 49,961, a factor of
 * 8.6e15. The level-59 computation is an exact traversal of a doubly pinned set, not a brute force.
 *
 * Run:  gp -q -f free_band.gp
 */

\p 25
{
my(T57, T58, T59, b, q, cnt, lo, hi);
T57 = sum(i = 1, 57, 1.0/prime(i));
T58 = sum(i = 1, 58, 1.0/prime(i));
T59 = sum(i = 1, 59, 1.0/prime(i));
print("UPPER BOUND ON THE LARGEST PRIME. If q = max(U) and |U| = n, the other n-1 primes");
print("carry at most T_{n-1}, so sigma(U) > 2 forces 1/q > 2 - T_{n-1}, i.e.");
print("     q < 1/(2 - T_{n-1})   whenever T_{n-1} < 2.");
print("");
printf("  T_57 = %.9f   T_58 = %.9f   T_59 = %.9f\n", T57, T58, T59);
print("");
b = 1.0/(2.0 - T58);
printf("  level 59: T_58 = %.9f < 2, so max(U) < %.4f, hence max(U) <= %d\n",
   T58, b, precprime(floor(b)));
printf("  level 60: T_59 = %.9f > 2, so the inequality is vacuous: NO upper bound.\n", T59);
print("");
print("  This is the exact mechanism of prop:levelbarrier. The enumeration is finite at");
print("  level 59 and infinite from level 60, and the switch is the single fact T_58 < 2 < T_59.");
print("");
lo = 0; hi = 0;
forprime(p = 2, 167, lo++);
forprime(p = 2, precprime(floor(b)), hi++);
print("  So at level 59 the support satisfies:");
print("     U contains all ", lo, " primes <= 167   (forced core)");
print("     U is contained in the ", hi, " primes <= ", precprime(floor(b)));
print("     the free part is 59 - ", lo, " = ", 59-lo, " primes chosen from ", hi-lo,
      " candidates in (167, ", precprime(floor(b)), "]");
printf("  Unconstrained that would be C(%d,%d) = %.3e choices; the mass condition cuts it to 49,961.\n",
   hi-lo, 59-lo, binomial(hi-lo, 59-lo)*1.0);
}
quit;
