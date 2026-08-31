\\ Numerical test of lem:deficit.  The condition is sigma_p(m) = c mod p, where
\\ sigma_p(m) = sum_{l|m} l^{-1} mod p -- NOT m' = sum_{l|m} m/l.  For squarefree m coprime to p,
\\ m' = m sigma_p(m), so the two differ by the unit m and testing m' = c is a different condition.
\\ Note forsquarefree binds m as [n, factorization]: m[1] is the integer.  Comparing the VECTOR to
\\ 0 silently never fires, which is how an earlier version of this file ran with no gcd filter.
{
my(N, cnt, tot, n, f, i, s, inv, ratio, lo, hi, first);
N = 2*10^6;
print("one prime, c = 2:");
lo = 9; hi = 0; first = 1;
foreach([3,5,7,11,13,17,19,23,29,31], p,
  cnt = 0; tot = 0;
  forsquarefree(m = 2, N,
    n = m[1];
    if(n % p == 0, next);
    f = m[2]; s = Mod(0, p);
    for(i = 1, matsize(f)[1], s += Mod(f[i,1], p)^(-1));
    tot += 1;
    if(s == Mod(2, p), cnt += 1));
  ratio = cnt*p*1.0/tot;
  if(ratio < lo, lo = ratio); if(ratio > hi, hi = ratio);
  printf("  p=%2d  count=%7d  tot/p=%9.1f  ratio=%.4f\n", p, cnt, tot*1.0/p, ratio));
printf("  one-prime ratio range: [%.3f, %.3f]\n", lo, hi);
print("two primes, c = 2:");
lo = 9; hi = 0;
foreach([[3,5],[5,7],[7,11],[11,13],[17,19],[23,29]], pq,
  my(p = pq[1], q = pq[2]);
  cnt = 0; tot = 0;
  forsquarefree(m = 2, N,
    n = m[1];
    if(n % p == 0 || n % q == 0, next);
    f = m[2];
    my(sp = Mod(0, p), sq = Mod(0, q));
    for(i = 1, matsize(f)[1],
      sp += Mod(f[i,1], p)^(-1); sq += Mod(f[i,1], q)^(-1));
    tot += 1;
    if(sp == Mod(2, p) && sq == Mod(2, q), cnt += 1));
  ratio = cnt*p*q*1.0/tot;
  if(ratio < lo, lo = ratio); if(ratio > hi, hi = ratio);
  printf("  p=%2d q=%2d  count=%6d  tot/(pq)=%8.1f  ratio=%.4f\n", p, q, cnt, tot*1.0/(p*q), ratio));
printf("  two-prime ratio range: [%.3f, %.3f]\n", lo, hi);
}
quit;
