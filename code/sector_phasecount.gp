\\ sector_phasecount.gp -- prices every rung of the sector ladder (prop:phasecount).  For each
\\ sector d and each target omega(e) = k, the enumeration is complete once j primes beyond the
\\ truncation become impossible, i.e. once S_{k-j} + j/A_{N+1} < d/dp; the number of phases
\\ required is that least j minus one.  Only phases 1 and 2 are implemented, so the reachable
\\ rungs are those needing at most 2 phases.
nd(n) = my(f = factor(n)); sum(i = 1, #f~, n / f[i,1]);
{ foreach([42, 47058, 2214502422], d,
  my(dp = nd(d), t = d/dp, allowed = List(), p = 2, S, K, w = omega(d));
  while(#allowed < 3000, if(isprime(p) && d % p != 0 && dp % p != 0, listput(allowed, p)); p++);
  allowed = Vec(allowed);
  S = vector(#allowed); S[1] = 1/allowed[1];
  for(i = 2, #allowed, S[i] = S[i-1] + 1/allowed[i]);
  K = 0; for(i = 1, #allowed, if(S[i] >= t, K = i; break));
  printf("\nd = %d,  omega(d) = %d,  d' = %d,  d/d' = %.12f\n", d, w, dp, t*1.);
  printf("  mass floor K = %d  ->  floor |P u Q| = 1 + %d + %d = %d\n", K, w, K, 1+w+K);
  printf("  kk   phases needed at N = 200 / 400 / 800 / 1600\n");
  for(kk = K, K+8,
    my(row = "");
    foreach([200, 400, 800, 1600], N,
      my(An1 = allowed[N+1], j = 0);
      for(jj = 1, 14, if(S[kk-jj] + jj/An1 < t, j = jj; break));
      row = Str(row, "  ", if(j == 0, ">14", Str(j-1))));
    printf("  %3d  %s   -> |P u Q| if excluded: %d\n", kk, row, 1 + w + kk + 2)));
}
quit;
