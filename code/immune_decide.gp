\\ immune_decide.gp -- decides the level-60 immune families (A_S and B_S both BPSW prime) in polynomial
\\ time.  A_S prime means x^2 = D_S mod A_S has two roots, and prop:tailbound forces x < A_S, so there
\\ are exactly two candidate tail primes per family.  All 34 come back empty.

\\ HILBERT MOVE: the immune families have A_S PRIME, so the both-squares problem is polynomial, not 2^58.
\\ A q + D = x^2 forces x^2 = D (mod A); A prime so the two roots +-s are computable by Tonelli-Shanks.
\\ Writing x = s + kA gives q = A k^2 + 2 s k + c.  But q <= t D ~ 1.05 D by prop:tailbound while A ~ 4D,
\\ so k = 0 and x = s: only TWO candidate q per family.  Decide each by testing them.
{ my(f = fileopen("/tmp/sels.txt"), line, forced = [], p = 2, n = 0, imm = 0, alive = 0, dead = 0);
  while(p <= 167, if(isprime(p), forced = concat(forced, p)); p++);
  while((line = filereadstr(f)) != 0,
    my(t = strsplit(line, "|"), base = t[1], sel = apply(eval, strsplit(t[2], ",")),
       S = concat(forced, sel), D, N, A, B, s, q, ok);
    D = vecprod(S); N = sum(i = 1, #S, D / S[i]); A = N + 2*D; B = N - 2*D;
    if(!ispseudoprime(A) || !ispseudoprime(B), next);
    imm++;
    \\ square roots of D mod A
    if(kronecker(D, A) != 1, printf("base#%s: (D|A) != 1, already killed\n", base); next);
    s = lift(sqrt(Mod(D, A)));
    ok = 0;
    foreach([s, A - s], x,
      if(x^2 <= D, next);
      q = (x^2 - D) / A;
      if(denominator(q) != 1, next);
      if(q <= 787, next);
      if(!ispseudoprime(q), next);
      \\ second condition: B q + D must be a perfect square
      if(issquare(B*q + D), ok++; printf("  base#%s: SURVIVING CANDIDATE q with %d digits\n", base, #Str(q))));
    if(ok == 0, dead++, alive++));
  fileclose(f);
  printf("\nimmune families examined: %d\n", imm);
  printf("  decided EMPTY by the two-candidate test : %d\n", dead);
  printf("  with a surviving candidate              : %d\n", alive);
}
quit;
