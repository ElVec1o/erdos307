/* nearmiss_above.gp -- the missing half of the near-miss frontier: an EXACT r(a) > 1.
 *
 * prop:nearmiss reports max r = 0.5535 and smallest |r-1| = 0.4465 from sweeping a <= 1e7.
 * nearmiss_tune.gp improves the defect to 7.92e-3, but only from BELOW: its acceptance window is
 *
 *      if(sa > TARGET || sa < TARGET - 0.02, next);          TARGET = 30/31
 *
 * which rejects every sigma(a) at or above 30/31, so r < 1 always. nearmiss_construct.gp does reach
 * r >= 1.07, but only as a LOWER bound: a' is trial-divided, never factored, so r is not decided.
 *
 * So no exact r > 1 is on record. This script supplies one. It is the same construction with the
 * window mirrored, sigma(a) in [30/31, 30/31 + 0.02], and the same exactness requirement that a'
 * factor completely (cofactor prime), so the reported r is exact and not a bound.
 *
 * Why it matters. r(a) = sigma(a)sigma(a') = a''/a, so r > 1 is exactly a'' > a. An exact witness
 * closes the frontier from above and puts a decided point in the region r >= 1, which thm:barrier
 * places above 10^112.9 and which sweeping cannot reach.
 *
 * Usage: gp -q -f nearmiss_above.gp
 */

MW = 30;
SIGW = 31/30;
TARGET = 30/31;
TRIAL = 200000;
MAXEVAL = 6000;

mass(v) = sum(i = 1, #v, 1/v[i]);
dsum(v) = my(N = prod(i = 1, #v, v[i])); sum(i = 1, #v, N / v[i]);
crt3(x) = lift(chinese(chinese(Mod(x, 2)^(-1), Mod(x, 3)^(-1)), Mod(x, 5)^(-1)));
crtsum(v) = my(s2 = sum(i=1,#v,Mod(v[i],2)^(-1)), s3 = sum(i=1,#v,Mod(v[i],3)^(-1)), s5 = sum(i=1,#v,Mod(v[i],5)^(-1))); lift(chinese(chinese(s2, s3), s5));

\\ Early exit on squarefreeness. Every caller rejects on pl[3] == 0, so once a repeated factor
\\ appears the candidate is already dead; the old form nevertheless finished the remaining primes up
\\ to TRIAL = 200000. Returning at once is equivalent and measured 2.18x faster on 1600 candidates
\\ (3024 ms to 1390 ms) with an identical count of exact witnesses.
\\
\\ A bound was also tried and is worse. Since r >= sa*s and s only grows, a candidate can be killed
\\ as soon as sa*s passes the ceiling; that runs 1.89x, i.e. slower than this, because the rational
\\ comparison costs more per division than it saves, and it drops candidates the plain form keeps.
\\ Recorded so it is not tried again.
peel(m) =
{
  my(s = 0, rem = m);
  forprime(p = 2, TRIAL,
    if(rem % p == 0,
      s += 1/p; rem /= p;
      if(rem % p == 0, return([0, 0, 0]));
    );
  );
  [s, rem, 1];
}

{
  my(best = 0, bestd = 1, evals = 0, exact = 0);
  print("tuning sigma(a) just ABOVE 30/31 = ", 1.0*TARGET, " against the forced sigma(a') >= 31/30, seeking an EXACT r > 1");
  print("prop:nearmiss frontier from sweeping: max r = 0.5535, smallest |r-1| = 0.4465");
  print("");
  forprime(X = 271, 900,
    my(pool = primes([7, X]), np0, extras, cands = List());
    np0 = #pool;
    extras = primes([X + 1, 4000]);
    /* candidate = drop a subset D (size <= 2) of the top 30, optionally add one extra prime */
    my(top = vector(min(30, np0), i, np0 - i + 1));
    for(i = 0, #top,
      for(j = 0, if(i == 0, 0, #top),
        my(D = if(i == 0, [], if(j == 0 || j <= i, [top[i]], [top[i], top[j]])));
        if(i > 0 && j > 0 && j <= i, next);
        for(k = 0, #extras,
          my(add = if(k == 0, [], [extras[k]]), keep, sa, res);
          keep = select(t -> !setsearch(Set(D), t), vector(np0, t, t));
          keep = concat(vector(#keep, t, pool[keep[t]]), add);
          sa = mass(keep);
          if(sa < TARGET || sa > TARGET + 0.02, next);
          if(crtsum(keep) != 0, next);
          listput(cands, keep);
        );
      );
    );
    for(ci = 1, #cands,
      if(evals >= MAXEVAL, break(2));
      my(keep = cands[ci], a, ap, sa, pl, sap, r, d);
      a = prod(i = 1, #keep, keep[i]);
      ap = dsum(keep);
      if(ap % MW != 0, error("forcing failed"));
      evals++;
      pl = peel(ap);
      if(pl[3] == 0, next);
      if(!ispseudoprime(pl[2]), next);
      exact++;
      sa = mass(keep);
      sap = pl[1] + 1/pl[2];
      r = sa * sap;
      d = abs(r - 1);
      if(d < bestd,
        bestd = d; best = [keep, a, ap, sa, sap, r, pl[2]];
        printf("  new best: w(a)=%d digits(a)=%d  sigma(a)=%.9f sigma(a')=%.9f  r=%.12f  |r-1|=%.3e\n",
               #keep, #digits(a), 1.0*sa, 1.0*sap, 1.0*r, 1.0*d);
      );
    );
  );
  print("");
  print("evaluated ", evals, " admissible candidates; ", exact, " had a' completely factored");
  if(best == 0,
    print("none exact")
  ,
    print("=== best near-miss ===");
    print("primes of a: ", best[1]);
    print("a  = ", best[2]);
    print("a' = ", best[3]);
    print("cofactor (prime) = ", best[7]);
    printf("sigma(a)  = %.12f\n", 1.0*best[4]);
    printf("sigma(a') = %.12f\n", 1.0*best[5]);
    printf("r = sigma(a)sigma(a') = %.12f\n", 1.0*best[6]);
    printf("relative defect |r-1| = %.6e   (sweep frontier: 0.4465)\n", 1.0*bestd);
    print("r > 1 : ", if(best[6] > 1, "yes", "no"));
    print("exact r = ", best[6]);
    write("nearmiss_tune_best.txt", "primes: ", best[1]);
    write("nearmiss_tune_best.txt", "a = ", best[2]);
    write("nearmiss_tune_best.txt", "ap = ", best[3]);
    write("nearmiss_tune_best.txt", "cofactor = ", best[7]);
    write("nearmiss_tune_best.txt", "r = ", best[6]);
  );
}
quit;
