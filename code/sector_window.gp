\\ prop:barthreshold: sigma(U) = t + 1/t with t = sigma(a), and sigma(U) <= T_K for |U| = K.
\\ So |U| <= K forces t + 1/t <= T_K, i.e. t in an explicit window about 1.  ONE convention
\\ throughout: K counts ALL of U, exactly as barthreshold's T_n/t_n table does.  An earlier version
\\ of this script tabulated PS[B-1] against a label B, which mixed conventions and put the |U| <= 60
\\ window at T_59; the paper transcribed that and had to be corrected.
{
my(PS, tot, p, np, M, lo, hi, K);
np = 0; tot = 0.0; PS = List();
forprime(p = 2, 10^6, tot += 1.0/p; listput(PS, tot); np += 1);
print("  |U| <= K   T_K         admissible window for t = sigma(a)");
foreach([59, 60, 61, 62, 64, 66, 68, 70, 80, 100], K,
  M = PS[K];
  lo = (M - sqrt(M^2 - 4))/2; hi = (M + sqrt(M^2 - 4))/2;
  printf("  %6d     %.7f   [%.6f , %.6f]\n", K, M, lo, hi));
print("");
print("and the reverse reading: min K with T_K >= s + 1/s, for a few sectors s = sigma(d)");
foreach([[2,"2"],[6,"2*3"],[42,"2*3*7"],[1806,"2*3*7*43"],[47058,"2*3*11*23*31"],[3,"3"]], pr,
  my(n = pr[1], s = 0.0, i, tt);
  foreach(factor(n)[,1]~, q, s += 1.0/q);
  tt = s + 1/s; K = 0;
  for(i = 1, np, if(PS[i] >= tt, K = i; break));
  if(K == 0,
    printf("  d = %-14s s = %.6f  s+1/s = %.6f  K > %d (pi(10^6)); Mertens estimate K ~ %.1e\n",
           pr[2], s, tt, np, exp(exp(tt - 0.2615))/exp(tt - 0.2615)),
    printf("  d = %-14s s = %.6f  s+1/s = %.6f  K = %d\n", pr[2], s, tt, K)));
}
quit;
