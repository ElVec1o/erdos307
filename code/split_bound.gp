/* The barrier stratified by the smaller support (prop:split).
 *
 * For a two-cycle sigma(a)sigma(b) = 1 with disjoint supports. Writing T = T_|U| for the largest
 * mass |U| primes can carry, sigma(a) + sigma(b) <= T and sigma(a) <= T_k where k = omega(a). Since
 * x(T-x) increases for x <= T/2, the largest achievable product is m(T-m) with m = min(T_k, T/2),
 * so feasibility needs m(T-m) >= 1.
 *
 * For k >= 3, T_k >= 31/30 > T/2 in range, so m = T/2 and the condition is just T >= 2: the general
 * barrier |U| >= 59, which is attained. For k <= 2 the member is too small to carry half the mass,
 * m = T_k, and the condition T >= T_k + 1/T_k bites:
 *      k = 1  ->  |U| >= 1413        (a is a prime p, so sigma(b) = p >= 2 on primes != p)
 *      k = 2  ->  |U| >= 69          (best case a = 6, so sigma(b) >= 6/5 on primes >= 5)
 *
 * This contains Kovic (2012) Prop. 16 -- no two-cycle has both members a product of two primes --
 * and extends it: EITHER member having two prime factors forces |U| >= 69, and either having one
 * forces |U| >= 1413. With prop:close59 giving |U| >= 60, the window 60 <= |U| <= 68 that any
 * level-by-level search must cross admits only splits with both omega >= 3.
 *
 * Run:  gp -q -f split_bound.gp
 */

\p 20
{
my(k, Tk, acc, n, ok, m, cap);
print("SPLIT CONSTRAINT, corrected. sigma(a)sigma(b) = 1, supports disjoint, omega(a) = k.");
print("With T = T_{k+s} the total available mass, sigma(a) <= T_k and sigma(a)+sigma(b) <= T,");
print("so the largest possible product is m(T - m) with m = min(T_k, T/2) -- balance if a can");
print("carry half the mass, otherwise a as large as it can be. Feasibility needs m(T-m) >= 1.");
print("");
print("   k  |   T_k    | least s | k+s  | binding case");
cap = 3000000;
for(k = 1, 8,
  Tk = sum(i = 1, k, 1.0/prime(i));
  acc = Tk; n = k; ok = 0;
  while(n < cap,
    n++; acc += 1.0/prime(n);
    m = if(Tk < acc/2, Tk, acc/2);
    if(m*(acc - m) >= 1.0, ok = n - k; break);
  );
  if(ok > 0,
    my(T2, m2);
    T2 = 0.0; forprime(p = 2, prime(k+ok), T2 += 1.0/p);
    m2 = if(Tk < T2/2, "a-capped", "balanced");
    printf("   %2d | %.6f | %7d | %4d | %s\n", k, Tk, ok, k+ok, m2),
    printf("   %2d | %.6f | > %d | -- |\n", k, Tk, cap));
);
print("");
print("So the constraint bites only for k = 1 and k = 2. Conclusion:");
print("  min(omega(a),omega(b)) = 1  =>  |U| >= 1413");
print("  min(omega(a),omega(b)) = 2  =>  |U| >= 69");
print("  min(omega(a),omega(b)) >= 3 =>  |U| >= 59  (the general barrier, and it is attained)");
}
quit;
