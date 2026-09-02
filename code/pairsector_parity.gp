\\ pairsector_parity.gp -- that T(R) is never exactly 2 for an odd-size squarefree base, so the
\\ pair-sector tail is always bounded and the sector is genuinely finite (Erdos307.mass_ne_two).

\\ Can T(R) = sum_{p in R} 1/p equal 2 exactly, for R a set of 59 distinct primes?
\\ T(R) = N/D with D = prod R, N = sum D/p.  Claim: N is ODD whenever |R| is odd, so N != 2D.
\\   - if 2 not in R: D odd, every D/p odd, |R| odd terms -> N odd.
\\   - if 2 in R: D/2 is odd (product of the odd primes); every other D/p is even -> N odd.
{ my(bad = 0, cnt = 0);
  print("Testing N = sum_{p|D} D/p mod 2 over random squarefree D with an ODD number of prime factors:");
  for(t = 1, 30000,
    my(k = 2*random(5) + 3, S = [], p, D, N);          \\ k odd, 3..11
    while(#S < k, p = prime(random(200)+1); if(!setsearch(Set(S), p), S = concat(S, p)));
    D = vecprod(S); N = sum(i = 1, #S, D / S[i]);
    cnt++; if(N % 2 != 1, bad++));
  printf("  %d random odd-size squarefree D: N odd in %d, N even in %d\n", cnt, cnt - bad, bad);
  print("  => N != 2D always, so T(R) != 2 exactly.  The pair-sector tail is therefore ALWAYS bounded.");
}
quit;
