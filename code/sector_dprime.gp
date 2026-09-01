\\ The sector barrier WITH the d'-exclusion.
\\ e = d + q d' gives gcd(e,d) = gcd(e,d') = 1, so supp(e) avoids supp(d) u supp(d') in EVERY
\\ sector (Bado uses this only where d is primary pseudoperfect and d' = d-1).  With
\\ sigma(e) ~ 1/sigma(d) and, for d even, omega(e) even, this bounds |P u Q| = 1 + omega(d) + omega(e)
\\ sector by sector.  The minimum over all sectors is an independent route to the global barrier.
{
my(base, ns, m, i, d, sd, dp, E, tgt, k, s, p, om, bnd, best, crit);
base = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47];
ns = #base; best = 10^9; crit = List();
for(m = 1, 2^ns - 1,
  d = 1; sd = 0.0; om = 0;
  for(i = 1, ns, if(bitand(m, 1<<(i-1)), d *= base[i]; sd += 1.0/base[i]; om += 1));
  if(om > 7, next);                        \\ omega(d) >= 8 cannot beat 60: 1+8+K, K large
  dp = 0; for(i = 1, ns, if(bitand(m, 1<<(i-1)), dp += d/base[i]));
  E = Set(concat(factor(d)[,1]~, if(dp > 1, factor(dp)[,1]~, [])));
  tgt = 1/sd;
  \\ we only care about bounds <= 63, so stop as soon as k alone exceeds that
  k = 0; s = 0.0;
  forprime(p = 2, 10^5,
    if(setsearch(E, p), next);
    s += 1.0/p; k += 1;
    if(s >= tgt || k > 64 - om, break));
  if(s < tgt, next);
  if(d % 2 == 0 && k % 2 == 1, k += 1);
  bnd = 1 + om + k;
  if(bnd < best, best = bnd);
  if(bnd <= 63, listput(crit, [bnd, d, om, sd, k])));
printf("MINIMUM over these sectors: |P u Q| >= %d\n\n", best);
print("CRITICAL SECTORS (bound <= 63) -- the entire obstruction to a barrier above 60:");
print("  |PuQ|>=   d           omega(d)  sigma(d)    omega(e)>=   factorisation");
crit = vecsort(Vec(crit), 1);
for(i = 1, #crit,
  my(r = crit[i]);
  printf("  %5d     %-10d  %2d      %.6f    %5d       %s\n",
         r[1], r[2], r[3], r[4], r[5], strjoin(apply(x->Str(x), factor(r[2])[,1]~), "*")));
printf("\ncount with bound <= 63: %d\n", #crit);
}
quit;
