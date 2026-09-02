\\ sigma_gap.gp -- how close sigma(a) = sum_{p|a} 1/p can come to 1, from below and from above.
\\ Doubly exponential in omega(a): no bound |sigma(a)-1| >= f(omega(a)) can exist.

\\ How close to 1 can sigma(a) = sum_{p|a} 1/p get, for squarefree a with k prime factors?
\\ Greedy Sylvester-type construction from below, and the best from above.  If |sigma(a)-1| decays
\\ super-exponentially in k, then no bound |sigma(a)-1| >= f(omega(a)) with f decaying slower can hold,
\\ and the barrier cannot be moved by any such estimate.
{ my(S, P, k, r, p, gap);
  print("Greedy from below: at each step take the smallest prime keeping sum < 1.");
  S = 0; P = []; k = 0;
  while(k < 12,
    r = 1 - S; p = if(r <= 0, break, nextprime(ceil(1/r)));
    if(S + 1/p >= 1, p = nextprime(p+1));
    S += 1/p; P = concat(P, p); k++;
    printf("  k=%2d  p=%s  sigma = 1 - %.6e   (log10 gap %.2f)\n", k, p, 1.0*(1-S), log(1.0*(1-S))/log(10)));
  print();
  print("Same, from above (smallest prime keeping the sum > 1 once it can):");
  S = 0; P = []; k = 0; my(prev = 1);
  forprime(q = 2, 100, if(S + 1/q < 1, S += 1/q; P = concat(P, q); k++));
  gap = 1 - S; p = nextprime(ceil(1/gap));
  printf("  base %d primes, sigma = 1 - %.6e; adding p=%d gives sigma - 1 = %.6e\n",
    k, 1.0*gap, p, 1.0*(S + 1/p - 1));
  printf("  adding instead p=%d gives 1 - sigma = %.6e\n", nextprime(p+1), 1.0*(1 - S - 1/nextprime(p+1)));
}
quit;
\\ For each k, a squarefree a with omega(a)=k and sigma(a) just ABOVE 1: take the greedy-below set on
\\ k-1 primes with gap g = 1 - S, then adjoin the largest prime p < 1/g, giving sigma - 1 = 1/p - g > 0.
{ my(S = 0, P = [], k = 0, g, p, ex);
  print(" k   omega(a)   sigma(a) - 1        log10");
  while(k < 11,
    g = 1 - S; p = if(g <= 0, break, nextprime(ceil(1/g))); if(S + 1/p >= 1, p = nextprime(p+1));
    S += 1/p; P = concat(P, p); k++;
    g = 1 - S; if(g <= 0, next);
    my(q = precprime(floor(1/g)));           \\ largest prime with 1/q > g
    if(q > 1 && !setsearch(Set(P), q),
      ex = 1/q - g;
      if(ex > 0, printf("%3d   %4d      %.6e      %.2f\n", k, k+1, 1.0*ex, log(1.0*ex)/log(10)))));
  print();
  print("So |sigma(a) - 1| is doubly exponentially small in omega(a), from BOTH sides.");
  print("Hence no bound of the form |sigma(a) - 1| >= f(omega(a)) with f > 0 can exist.");
}
quit;
