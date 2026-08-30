{
my(seeds, beam, nb, cap, mine, minstate, found, W);
cap = 3000; W = 24; found = 0; mine = -1;
\\ build many seeds: random subsets of the odd primes < 60 with s just under 1
seeds = List();
for(t = 1, 400,
  my(S); S = List();
  forprime(p = 3, 60, if(random(3) > 0, listput(S, p)));
  S = Vec(S);
  if(#S < 6, next);
  my(P, D); P = prod(i=1,#S,S[i]); D = sum(i=1,#S,P/S[i]);
  if(2*P - D > 0, listput(seeds, S)));
seeds = Vec(seeds);
print("seeds: ", #seeds);

for(si = 1, #seeds,
  my(B, P, D, e);
  B = seeds[si];
  P = prod(i=1,#B,B[i]); D = sum(i=1,#B,P/B[i]); e = 2*P - D;
  for(step = 1, 40,
    if(e <= 0, break);
    if(mine < 0 || e < mine, mine = e; minstate = [si, step, #digits(P)]);
    if((P+4) % e == 0,
      my(b); b = (P+4)/e;
      if(b % 2 == 1 && gcd(b,P) == 1 && !setsearch(Set(B), b),
        print("*** SOLUTION seed ", si, " step ", step, ", b_final ", #digits(b), " digits");
        found++);
      break);
    \\ choose b minimising the new e among the first few valid odd coprime candidates
    my(n, bb, bestb, beste2, k);
    n = (P \ e) + 1; if(n % 2 == 0, n++); if(n < 3, n = 3);
    bestb = 0; beste2 = -1; k = 0; bb = n;
    while(k < 40,
      if(gcd(bb, P) == 1 && !setsearch(Set(B), bb),
        my(e2); e2 = bb*e - P;
        if(e2 > 0 && (beste2 < 0 || e2 < beste2), beste2 = e2; bestb = bb);
        k++);
      bb += 2;
      if(bb > n + 400, break));
    if(bestb == 0, break);
    B = concat(B, [bestb]);
    D = bestb*D + P; P = P*bestb; e = 2*P - D;
    if(#digits(P) > cap, break)
  )
);
print("solutions: ", found);
print("smallest e ever reached: ", mine, "   (", #digits(mine), " digits)  at ", minstate);
}
quit;
