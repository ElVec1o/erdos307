\\ sector_tight.gp -- the sectors where the d-prime bound is tight, and how their number grows with the prime bound.

\\ The sectors where the d'-bound is tight (|U| = 60): what the forced-prime enumeration would cost there.
{ my(best = [], P = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]);
  print("d   omega(d)  d'   T=d/d'   excluded primes   min omega(e) by mass   |U|");
  forstep(mask = 1, 2^#P - 1, 1,
    my(S = [], d, dp, T, A, p, k, s, U);
    for(i = 1, #P, if(bittest(mask, i-1), S = concat(S, P[i])));
    if(#S < 3 || #S > 6, next);
    d = vecprod(S); dp = d * sum(i = 1, #S, 1/S[i]);
    if(dp == 0, next); T = d/dp; if(T <= 1 || T > 1.35, next);
    \\ mass bound: fewest primes avoiding supp(d) u supp(d') summing past T
    A = []; p = 2; while(#A < 3000, if(isprime(p) && d % p != 0 && dp % p != 0, A = concat(A, p)); p++);
    k = 1; s = 1.0/A[1]; while(s < T && k < #A, k++; s += 1.0/A[k]); if(s < T, next);
    if(d % 2 == 0 && k % 2 == 1, k++);   \\ parity: d even => e odd => omega(e) even
    U = 1 + #S + k;
    if(U <= 61, best = concat(best, [[U, d, #S, dp, 1.0*T, k]])));
  best = vecsort(best, 1);
  for(i = 1, min(12, #best), my(b = best[i]);
    printf("%-10d %d  %-10d %.6f   %-3d primes ex.   omega(e)>=%d   |U|>=%d\n", b[2], b[3], b[4], b[5], omega(b[2]*b[4]), b[6], b[1]));
  printf("\ntotal sectors with |U| <= 61 among %d-to-6-prime d from primes <= 47: %d\n", 3, #best);
}
quit;
