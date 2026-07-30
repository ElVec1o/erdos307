/* lyap_refute.gp -- search for a VERIFIED counterexample to conj:lyap.
 *
 * conj:lyap asks for some lambda > 0 with
 *      log sigma(n) < lambda (sigma(n) - sigma(n'))                                  (*)
 * for every squarefree n with n' squarefree. If a single such n has
 *      sigma(n) > 1   and   sigma(n') > sigma(n),
 * then the left side of (*) is positive and the right side is negative for every lambda > 0, so (*)
 * fails there for all lambda at once and conj:lyap is FALSE. (sigma(n') = sigma(n) is impossible by
 * lem:sigmainj, so the inequality is automatically strict.)
 *
 * Construction. Force W = {2,3,5} into n' by the criterion
 *      w | n'  <==>  sum_{p|n} p^{-1} = 0 (mod w),                                   (F)
 * and build n from primes >= 7 with sigma(n) just above 1. Then sigma(n') >= sigma(W) = 31/30 and
 * sigma(n) < 31/30 gives sigma(n') > sigma(n). Reaching sigma(n) > 1 without 2, 3, 5 needs primes to
 * about 358, so n has roughly 145 digits; n' then has a chance of being (small primes) x (one large
 * prime), which is what makes squarefreeness of n' VERIFIABLE rather than assumed.
 *
 * A lower bound on sigma(n') suffices for the refutation, but squarefreeness of n' does not: that is
 * why the cofactor after trial division must come out prime.
 *
 * Usage: gp -q -f lyap_refute.gp
 */

W = [2, 3, 5];
MW = 30;
SIGW = 1/2 + 1/3 + 1/5;        /* 31/30, exact */
TRIAL = 100000;

mass(v) = sum(i = 1, #v, 1/v[i]);                         /* exact rational */
dsum(v) = my(N = prod(i = 1, #v, v[i])); sum(i = 1, #v, N / v[i]);
crt3(x) = lift(chinese(chinese(Mod(x, 2)^(-1), Mod(x, 3)^(-1)), Mod(x, 5)^(-1)));
crtsum(v) = my(s2 = sum(i=1,#v,Mod(v[i],2)^(-1)), s3 = sum(i=1,#v,Mod(v[i],3)^(-1)), s5 = sum(i=1,#v,Mod(v[i],5)^(-1))); lift(chinese(chinese(s2, s3), s5));

/* trial-divide m; return [sigma_lower (exact rational), cofactor, squarefree_so_far] */
peel(m) =
{
  my(s = 0, rem = m, sq = 1);
  forprime(p = 2, TRIAL,
    if(rem % p == 0,
      s += 1/p; rem /= p;
      if(rem % p == 0, sq = 0; while(rem % p == 0, rem /= p));
    );
  );
  [s, rem, sq];
}

{
  my(tested = 0, hits = 0, sqf = 0, best = 0);
  print("searching for n with sigma(n) > 1 < sigma(n'), n' squarefree and fully factored");
  print("n' must be SQUAREFREE: n odd makes every n/p odd, so n' is a sum of w(n) odd terms and");
  print("4 | n' is easy to hit by accident. Candidates with a repeated prime in n' are rejected.");
  print("");
  forprime(X = 353, 700,
    my(pool = primes([7, X]), n = 0, C, top, cands = List());
    n = #pool;
    C = crtsum(pool);
    top = vector(min(60, n), i, n - i + 1);        /* drop only large primes: minimal mass cost */
    /* every removal set of size 1, 2 or 3 from the top block satisfying (F) */
    for(i = 1, #top, if(crt3(pool[top[i]]) == C, listput(cands, [top[i]])));
    for(i1 = 1, #top - 1,
      for(i2 = i1 + 1, #top,
        if((crt3(pool[top[i1]]) + crt3(pool[top[i2]])) % MW == C, listput(cands, [top[i1], top[i2]]));
        for(i3 = i2 + 1, #top,
          if((crt3(pool[top[i1]]) + crt3(pool[top[i2]]) + crt3(pool[top[i3]])) % MW == C,
             listput(cands, [top[i1], top[i2], top[i3]]))
        )
      )
    );
    if(C == 0, listput(cands, []));
    for(ci = 1, #cands,
      my(D = cands[ci], keep, a, ap, sa, pl, sap);
      keep = select(i -> !setsearch(Set(D), i), vector(n, i, i));
      keep = vector(#keep, i, pool[keep[i]]);
      sa = mass(keep);
      if(sa <= 1 || sa >= SIGW, next);             /* need 1 < sigma(n) < sigma(W) */
      a = prod(i = 1, #keep, keep[i]);
      ap = dsum(keep);
      if(ap % MW != 0, error("forcing failed"));
      tested++;
      pl = peel(ap);
      if(pl[1] <= sa, next);                       /* need sigma(n') > sigma(n) already from the peel */
      hits++;
      if(pl[3] == 0, next);                        /* a repeated small prime: n' not squarefree */
      sqf++;
      if(ispseudoprime(pl[2]),
        sap = pl[1] + 1/pl[2];
        print("*** VERIFIED COUNTEREXAMPLE ***");
        print("  X = ", X, "  dropped ", #D, " large primes  w(n) = ", #keep);
        printf("  digits(n) = %d, digits(n') = %d, cofactor digits = %d\n",
               #digits(a), #digits(ap), #digits(pl[2]));
        printf("  sigma(n)  = %.9f\n", 1.0 * sa);
        printf("  sigma(n') = %.9f  (exact: cofactor is a BPSW probable prime)\n", 1.0 * sap);
        printf("  sigma(n') - sigma(n) = %.9f > 0 with sigma(n) > 1: (*) fails for every lambda\n",
               1.0 * (sap - sa));
        write("lyap_refute_witness.txt", "n primes: ", keep);
        write("lyap_refute_witness.txt", "n  = ", a);
        write("lyap_refute_witness.txt", "n' = ", ap);
        write("lyap_refute_witness.txt", "cofactor = ", pl[2]);
        write("lyap_refute_witness.txt", "sigma(n) = ", sa);
        write("lyap_refute_witness.txt", "sigma(n') = ", sap);
        best = 1; break(2);
      ,
        if(best == 0,
          printf("  near miss: X=%3d |D|=%d  sigma(n)=%.6f sigma(n')>=%.6f  cofactor %d digits composite\n",
                 X, #D, 1.0 * sa, 1.0 * pl[1], #digits(pl[2]))
        )
      );
    );
  );
  print("");
  print("candidates with sigma(n_) > sigma(n): ", hits, " of ", tested, " tested; ", sqf, " had n_ squarefree in the peeled part");
  if(best == 0, print("no candidate had a prime cofactor; n' squarefree not verifiable in this batch"));
}
quit;
