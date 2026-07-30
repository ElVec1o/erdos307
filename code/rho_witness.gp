/* rho_witness.gp -- a fully verified counterexample to the route "prove rho < 1 - 1/(eU),
 * hence conj:lyap" of the paragraph after Conjecture conj:lyap.
 *
 * That route needs rho = sup{sigma(n')/sigma(n) : sigma(n) > 1} to be below 1 - 1/(eU), where U is
 * a lower bound on the upper demand; with the measured U = 1.274 the threshold is 0.711.
 *
 * We exhibit a squarefree a with sigma(a) > 1 and sigma(a')/sigma(a) far above 0.711, with a'
 * COMPLETELY FACTORED, so that a' is verified squarefree and sigma(a') is exact. Then a lies in the
 * class conj:lyap quantifies over, and the route is dead.
 *
 * Mechanism: for squarefree a and a prime w not dividing a,
 *      w | a'  <==>  sum_{p|a} p^{-1} = 0 (mod w).                                  (F)
 * Take W = {2,3} forced into a', and a built from primes in [5,X]. Reaching sigma(a) > 1 without
 * 2 and 3 needs X of order 123 only, so a has about 50 digits and a' can be factored outright.
 * Removals used to satisfy (F) are taken from the LARGEST pool primes, so they cost almost no mass.
 *
 * Usage: gp -q -f rho_witness.gp
 */

W = [2, 3];
M = 6;
SIGW = 1.0/2 + 1.0/3;          /* 0.8333..., the mass forced into a' */
UMEAS = 1.274;                 /* measured upper demand, paper line "against a measured upper demand" */
THRESH = 1 - 1/(exp(1) * UMEAS);

mass(v) = sum(i = 1, #v, 1.0/v[i]);
dsum(v) = my(N = prod(i = 1, #v, v[i])); sum(i = 1, #v, N / v[i]);
resid(v) = lift(chinese(sum(i = 1, #v, Mod(v[i], 2)^(-1)), sum(i = 1, #v, Mod(v[i], 3)^(-1))));

/* sigma from a full factorisation matrix, plus a squarefreeness flag */
sigma_exact(f) = [sum(i = 1, #f~, 1.0/f[i,1]), vecmax(f[,2]) == 1];

{
  print("Target: squarefree a with sigma(a) > 1, a' fully factored, sigma(a')/sigma(a) > ", THRESH);
  print("(threshold 1 - 1/(e*U) at the paper's measured U = ", UMEAS, ")");
  print("");
  my(best = 0, bestdig = 10^9);
  for(xi = 100, 260,
    if(!isprime(xi), next);
    my(pool = primes([5, xi]), n = 0, C, cand, keep, a, ap, f, se, sa, ratio);
    n = #pool;
    C = resid(pool);
    /* removal sets of size <= 2 drawn from the top 25 primes, cheapest in mass */
    my(top = vector(min(25, n), i, n - i + 1), found = 0, D = 0);
    if(C == 0, D = []; found = 1);
    if(!found,
      for(i = 1, #top,
        if(lift(chinese(Mod(pool[top[i]], 2)^(-1), Mod(pool[top[i]], 3)^(-1))) == C,
           D = [top[i]]; found = 1; break)
      )
    );
    if(!found,
      for(i1 = 1, #top - 1,
        if(found, break);
        for(i2 = i1 + 1, #top,
          my(s = lift(chinese(Mod(pool[top[i1]], 2)^(-1) + Mod(pool[top[i2]], 2)^(-1),
                              Mod(pool[top[i1]], 3)^(-1) + Mod(pool[top[i2]], 3)^(-1))));
          if(s == C, D = [top[i1], top[i2]]; found = 1; break)
        )
      )
    );
    if(!found, next);
    keep = select(i -> !setsearch(Set(D), i), vector(n, i, i));
    keep = vector(#keep, i, pool[keep[i]]);
    sa = mass(keep);
    if(sa <= 1.0, next);                      /* rho quantifies over sigma(n) > 1 only */
    a = prod(i = 1, #keep, keep[i]);
    ap = dsum(keep);
    for(j = 1, #W, if(ap % W[j] != 0, error("forcing failed at ", W[j])));
    if(#digits(a) > 120, next);               /* keep a' factorable */
    print("  X = ", xi, "  w(a) = ", #keep, "  digits(a) = ", #digits(a),
          "  sigma(a) = ", sa, "   factoring a' (", #digits(ap), " digits)...");
    f = factor(ap);
    se = sigma_exact(f);
    ratio = se[1] / sa;
    printf("     sigma(a') = %.6f (exact, %d prime factors)  squarefree: %s   ratio = %.6f%s\n",
           se[1], #f~, if(se[2], "YES", "NO"), ratio,
           if(ratio > THRESH && se[2], "   <== kills the rho route", ""));
    if(ratio > THRESH && se[2] && #digits(a) < bestdig,
       best = [xi, keep, a, ap, sa, se[1], ratio, f]; bestdig = #digits(a));
  );

  print("");
  if(best == 0,
    print("no verified witness found in the scanned range")
  ,
    print("=== SMALLEST VERIFIED WITNESS ===");
    print("X = ", best[1], ",  a = product of the ", #best[2], " primes in [5,", best[1],
          "] minus ", #primes([5,best[1]]) - #best[2], " of the largest");
    print("primes of a: ", best[2]);
    print("a  = ", best[3]);
    print("a' = ", best[4]);
    print("factorisation of a': ", best[8]);
    printf("sigma(a)  = %.9f   (> 1, so a is in the class rho quantifies over)\n", best[5]);
    printf("sigma(a') = %.9f   (exact: a' is fully factored and squarefree)\n", best[6]);
    printf("sigma(a')/sigma(a) = %.9f\n", best[7]);
    printf("paper's route needs rho < 1 - 1/(e*U) = %.6f with U = %.3f: REFUTED\n", THRESH, UMEAS);
    printf("the bound L <= 1/(e(1-rho)) it would give is >= %.6f, against U <= %.3f\n",
           1/(exp(1)*(1 - best[7])), UMEAS);
    print("sanity: gcd(a,a') = ", gcd(best[3], best[4]), " (must be 1);  a' - a*sigma(a) = ",
          best[4] - round(best[3] * best[5]), " (rounding only)");
  );
}
quit;
