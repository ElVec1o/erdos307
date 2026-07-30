/* rho_verify.gp -- independent EXACT verification of the rho witness.
 *
 * Claim. Let a = prod of the primes 5 <= p <= 163. Then a is squarefree, sigma(a) > 1, a' is
 * squarefree, and sigma(a')/sigma(a) > 1 - 1/(eU) for the measured upper demand U, so the route
 * "prove rho < 1 - 1/(eU), hence conj:lyap" cannot work.
 *
 * Everything below is exact rational or exact integer arithmetic. The only inexact quantity is e,
 * which is bounded by an explicit rational. Rule 7.
 *
 * Usage: gp -q -f rho_verify.gp
 */

P = primes([5, 163]);
a = prod(i = 1, #P, P[i]);
ap = sum(i = 1, #P, a / P[i]);                     /* arithmetic derivative, exact */

print("=== the witness ===");
print("a  = prod of the ", #P, " primes in [5,163]");
print("a  = ", a);
print("a' = ", ap);
print("digits: a has ", #digits(a), ", a' has ", #digits(ap));
print("");

print("=== checks that need no factorisation ===");
print("a squarefree (product of distinct primes): ", if(issquarefree(a), "YES", "NO"));
print("gcd(a,a') = ", gcd(a, ap), "   (thm:structure predicts 1)");
sa = sum(i = 1, #P, 1/P[i]);                       /* EXACT rational */
print("sigma(a) = ", sa, "  = ", 1.0 * sa);
print("rigidity check, sigma(a) = a'/a exactly: ", if(sa == ap/a, "YES", "NO"));
print("sigma(a) > 1 exactly: ", if(sa > 1, "YES", "NO"), "   (rho quantifies over sigma(n) > 1)");
print("");

print("=== factorisation of a' ===");
f = factor(ap);
print(f);
print("product of factors equals a': ", if(factorback(f) == ap, "YES", "NO"));
print("all exponents 1, so a' is squarefree: ", if(vecmax(f[,2]) == 1, "YES", "NO"));
print("issquarefree(a') agrees: ", if(issquarefree(ap), "YES", "NO"));
sap = sum(i = 1, #f~, 1/f[i,1]);                   /* EXACT rational */
print("sigma(a') = ", sap, "  = ", 1.0 * sap);
print("");

print("=== the refutation, in exact arithmetic ===");
ratio = sap / sa;                                   /* EXACT rational */
print("rho >= sigma(a')/sigma(a) = ", ratio, "  = ", 1.0 * ratio);
/* the route gives L <= 1/(e(1-rho)); it is useful only if that is below the upper demand U.
   Bound e above by 2.7182818286 (exact rational), which makes 1/(e(1-rho)) a LOWER bound. */
EUP = 27182818286/10000000000;
Lbound = 1 / (EUP * (1 - ratio));
print("so the route's bound is L <= 1/(e(1-rho)), which is at least ", 1.0 * Lbound);
print("");
print("the measured upper demand U (code/lyap_battery.rs, n <= 4e8) is at most 1.250828,");
print("and every single n gives an upper bound on U, so U <= 1.250828 is a finite exact check.");
print("route needs 1/(e(1-rho)) < U, i.e. ", 1.0 * Lbound, " < 1.250828 ?  ", if(Lbound < 1250828/1000000, "yes", "NO -- the route yields nothing"));
print("");
print("equivalently, the route needs rho < 1 - 1/(eU); with U = 1.250828 that threshold is");
ELO = 2718281828/1000000000;
thr = 1 - 1/(ELO * (1250828/1000000));
print("  1 - 1/(eU) <= ", 1.0 * thr, "   while rho >= ", 1.0 * ratio, ".");
print("exact comparison rho > threshold: ", if(ratio > thr, "YES, route REFUTED", "no"));
print("");

print("=== the sweep's rho, for contrast ===");
print("paper reports rho = 0.519746 measured over n <= 4e8, 'stable across the range'.");
print("every n <= 4e8 with sigma(n) > 1 is even, so the sweep never sampled an odd n.");
print("a here is odd, w(a) = ", #P, " is even, hence a' is a sum of an even number of odd terms:");
print("  a' even: ", if(ap % 2 == 0, "YES", "NO"), ",  a' divisible by 3: ", if(ap % 3 == 0, "YES", "NO"));
print("that is the forcing criterion (F): sum_{p|a} p^{-1} = 0 mod w.");
r2 = lift(sum(i = 1, #P, Mod(P[i], 2)^(-1)));
r3 = lift(sum(i = 1, #P, Mod(P[i], 3)^(-1)));
print("  sum p^{-1} mod 2 = ", r2, ",  mod 3 = ", r3, "   (both 0, so 6 | a')");
quit;
