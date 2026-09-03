\\ lvl60check.gp -- verifies every arithmetic claim of prop:lvl60factor over all 49,961 admissible
\\ level-60 bases, enumerated here from scratch (the same DFS as tailkill.py / close59.py, so this
\\ script depends on no scratch file).  Checks: A_S odd, gcd(A_S, D_S) = 1, A_S of 114 digits, the
\\ range of sigma = N_S/D_S, and the maximum of x/A_S, which must be < 1 for the proposition.
\\ Runtime ~6 min in PARI/GP 2.17.4.

forced = select(isprime, vector(167, i, i));
pool   = select(p -> isprime(p), vector(787 - 167, i, i + 167));
thr    = 2 - sum(i = 1, #forced, 1 / forced[i]);
Dforced = vecprod(forced);
pf = vector(#pool, i, 1 / pool[i]);
suf = vector(#pool + 1); forstep(i = #pool, 1, -1, suf[i] = suf[i+1] + pf[i]);

count = 0; smin = 9; smax = 0; rmax = 0; bad = 0; dgmin = 999; dgmax = 0;

test(chosen) =
{ my(D = Dforced, S, N, A, sig, t, r);
  foreach(chosen, i, D *= pool[i]);
  S = concat(forced, vector(#chosen, j, pool[chosen[j]]));
  N = sum(i = 1, #S, D / S[i]);
  A = N + 2*D;
  count++;
  if(A % 2 == 0 || gcd(A, D) != 1, bad++);
  dgmin = min(dgmin, #Str(A)); dgmax = max(dgmax, #Str(A));
  sig = N * 1. / D;
  smin = min(smin, sig); smax = max(smax, sig);
  \\ prop:tailbound, alpha = 1: q <= t D with t = (sigma + sqrt(sigma^2 - 4))/2, so
  \\ x^2 = A q + D <= ((sigma+2) t + 1) D^2 and x/A = sqrt((sigma+2) t + 1) / (sigma+2).
  t = (sig + sqrt(sig^2 - 4)) / 2;
  r = sqrt((sig + 2) * t + 1) / (sig + 2);
  rmax = max(rmax, r);
}

dfs(i, need, cur, chosen) =
{ if(need == 0, if(cur > thr, test(chosen)); return);
  if(i + need > #pool + 1, return);
  if(cur + suf[i] - suf[i + need] <= thr, return);
  dfs(i + 1, need - 1, cur + pf[i], concat(chosen, [i]));
  dfs(i + 1, need, cur, chosen);
}

dfs(1, 20, 0, []);
printf("admissible level-60 bases : %d  (expected 49961)\n", count);
printf("A odd and coprime to D    : %d violations  (expected 0)\n", bad);
printf("digits of A               : min %d  max %d\n", dgmin, dgmax);
printf("sigma range               : (%.9f , %.9f]\n", smin, smax);
printf("max x/A over all bases    : %.6f   (prop:lvl60factor needs < 1)\n", rmax);
if(count == 49961 && bad == 0 && dgmin == 114 && dgmax == 114 && rmax < 1, print("VERIFIED: every claim of prop:lvl60factor holds over all 49,961 bases."), print("MISMATCH"));
quit;
