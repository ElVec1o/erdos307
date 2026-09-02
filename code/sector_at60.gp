\\ sector_at60.gp -- every sector d (squarefree, omega 1..8, primes <= 47) whose mass floor gives
\\ |P u Q| = 60 exactly, with the parameters to decide it by sector_kexclude.rs phase 1.

\\ Every sector d (squarefree, omega 1..8, primes <= 47) whose mass floor gives |P u Q| = 60 exactly,
\\ with run parameters for sector_kexclude phase 1.  No restriction on sigma(d).
nd(n) = my(f = factor(n)); sum(i = 1, #f~, n / f[i,1] * f[i,2]);
{ my(P = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47], ok1 = 0, need2 = 0);
  forstep(mask = 1, 2^#P - 1, 1,
    my(S = [], d, dp, T, A, p, k, s, U, N, ok);
    for(i = 1, #P, if(bittest(mask, i-1), S = concat(S, P[i])));
    if(#S < 1 || #S > 8, next);
    d = vecprod(S); dp = nd(d); T = d/dp;
    A = []; p = 2; while(#A < 1500, if(isprime(p) && d % p != 0 && dp % p != 0, A = concat(A, p)); p++);
    k = 0; s = 0; while(s < T && k < #A, k++; s += 1.0/A[k]); if(s < T, next);
    if(d % 2 == 0 && k % 2 == 1, k++);
    U = 1 + #S + k;
    if(U != 60, next);
    N = k; while(N < 1490 && sum(j=1,k-1,1/A[j]) + 1/A[N+1] >= T, N++);
    ok = (sum(j=1,k-1,1/A[j]) + 1/A[N+1] < T);
    if(ok, ok1++; printf("%d %d %d %d %d\n", d, dp, k, N, U), need2++));
  printf("# at exactly 60: phase-1 decidable %d, needing phase 2 %d\n", ok1, need2);
}
quit;
