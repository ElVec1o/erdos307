\\ immune_decide.gp -- decides the 34 level-60 immune families outright (prop:immunedecide).
\\
\\ Immunity means A_S = N_S + 2 D_S is prime, and that is exactly what makes the family tractable.
\\ A solution forces x^2 = A_S q + D_S with x = a + b, and prop:tailbound gives q <= t D_S with
\\ t ~ 1.02 while A_S = (sigma + 2) D_S ~ 4 D_S, so x < 2.281 D_S < A_S (verified over all 49,961
\\ bases by lvl60check.gp). Hence x is one of the TWO square roots of D_S modulo the prime A_S,
\\ computable by Tonelli-Shanks, and each root yields a single candidate tail prime
\\ q = (x^2 - D_S)/A_S. Testing both settles the family in polynomial time, against the 2^58
\\ divisor search of prop:tailbound. All 34 come back EMPTY.
\\
\\ The primality of A_S and B_S is unconditional by the APR-CL run of immune_prove.gp and the
\\ ECPP certificates in data/certs/immune_ecpp.txt, so the verdict here is [P], not [C].
\\
\\ Run:  gp -q -f immune_decide.gp
default(parisize, 800000000);
P    = primes([2,800]);
T58  = sum(i=1, 58, 1/P[i]);
forc = select(x -> x <= 167, P);
pool = select(x -> x > 167 && T58 + 1/x > 2, P);
np   = #pool;
kk   = 59 - #forc;
thr  = 2 - sum(i=1, #forc, 1/forc[i]);
pf   = vector(np, i, 1/pool[i]);
cum  = vector(np+1); cum[1] = 0;
for(i=1, np, cum[i+1] = cum[i] + pf[i]);
printf("forced %d, pool %d, choose %d, threshold %s\n", #forc, np, kk, thr);

bases = List();
dfs(i, need, cur, chosen) = {
  if(need == 0, if(cur > thr, listput(bases, chosen)); return());
  if(i + need > np + 1, return());
  if(cur + (cum[min(i+need, np+1)] - cum[i]) <= thr, return());
  dfs(i+1, need-1, cur + pf[i], concat(chosen, [i]));
  dfs(i+1, need,   cur,          chosen);
};
dfs(1, kk, 0, []);
printf("admissible bases: %d   (expected 49961)\n", #bases);

\\ find the immune ones: A_S and B_S both BPSW probable primes
\\ NOTE: gp needs braces around any multi-line statement in a script file.
imm = List(); jkill = 0;
{
for(j=1, #bases,
  S = concat(forc, vector(#bases[j], t, pool[bases[j][t]]));
  D = prod(t=1, #S, S[t]);
  N = sum(t=1, #S, D \ S[t]);
  A = N + 2*D; B = N - 2*D;
  if(ispseudoprime(A) && ispseudoprime(B), listput(imm, [S, A, B, kronecker(D, A), kronecker(D, B)]));
  if(kronecker(D, A) == -1, jkill++);
);
}
printf("Jacobi certificate (D_S|A_S) = -1 kills: %d   (paper: 31219)\n", jkill);
printf("both A_S and B_S BPSW-prime: %d\n", #imm);
nimm = 0; for(j=1, #imm, if(imm[j][4] == 1, nimm++));
printf("of those, IMMUNE ((D_S|A_S) = +1): %d   (paper: 34)\n\n", nimm);


\\ decide each immune family by the two square roots of D_S modulo A_S

nimm2 = 0; dead = 0; alive = 0;
{
for(j=1, #imm,
  if(imm[j][4] != 1, next);          \\ (D_S|A_S) = -1 is already a Jacobi kill, not immune
  nimm2++;
  S = imm[j][1]; A = imm[j][2]; B = imm[j][3];
  D = prod(t=1, #S, S[t]);
  s = lift(sqrt(Mod(D, A)));
  ok = 0;
  foreach([s, A - s], x,
    if(x^2 <= D, next);
    q = (x^2 - D) / A;
    if(denominator(q) != 1, next);
    if(q <= 787, next);                     \\ q must be a new prime beyond the base pool
    if(!ispseudoprime(q), next);
    if(issquare(B*q + D), ok++);            \\ the companion square condition
  );
  if(ok == 0, dead++, alive++; printf("  family %d: SURVIVING CANDIDATE\n", j));
);
}
printf("\nimmune families examined                : %d\n", nimm2);
printf("  decided EMPTY by the two-candidate test : %d\n", dead);
printf("  with a surviving candidate              : %d\n", alive);
{ if(alive == 0 && nimm2 == 34,
  printf("\n=> all 34 immune level-60 families are EMPTY [P] (prop:immunedecide).\n")); }
quit;
