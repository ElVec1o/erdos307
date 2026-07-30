/* nearmiss_construct.gp -- push the near-miss quantity r(a) = sigma(a) sigma(a') by CONSTRUCTION
 * rather than by sweeping.
 *
 * prop:nearmiss measures max r = 0.5535 over a <= 10^7, and notes that the region r >= 1 lies above
 * 10^112.9 by thm:barrier. A sweep cannot reach that region. A construction can, because for
 * squarefree a and a prime w not dividing a,
 *
 *      w | a'   <==>   sum_{p | a} p^{-1} = 0  (mod w),                            (F)
 *
 * since a' = sum_{p|a} a/p = a * sum_{p|a} p^{-1} (mod w). So: fix a set W of small primes to be
 * forced into a', build a from primes outside W, and impose (F) for every w in W. Then
 * sigma(a') >= sigma(W) unconditionally, while sigma(a) is whatever the pool supplies.
 *
 * Solving (F): let M = prod W. Give each pool prime p the CRT element c(p) in Z/M with
 * c(p) = p^{-1} mod w for each w. Removing a set D from the full pool shifts the residue by
 * -sum_{p in D} c(p), so we need sum_{p in D} c(p) = C, where C is the CRT element of the full
 * pool's residues. Sizes |D| <= 2 are searched by table lookup, O(|pool|).
 *
 * Every r reported is a rigorous LOWER bound: a' is trial-divided only, never factored, so the true
 * sigma(a') is at least the printed one, hence the true r is at least the printed one.
 *
 * Usage: gp -q -f nearmiss_construct.gp
 */

TRIALMAX = 100000;

mass(v) = sum(i = 1, #v, 1.0/v[i]);
/* arithmetic derivative of the squarefree number prod(v); "deriv" is a PARI built-in, hence dsum */
dsum(v) = my(N = prod(i = 1, #v, v[i])); sum(i = 1, #v, N / v[i]);

/* lower bound on sigma(m) by trial division; returns [sigma_lb, cofactor, found, sqfree_so_far] */
sigma_lower(m) =
{
  my(s = 0.0, rem = m, sqfree = 1, found = 0);
  forprime(p = 2, TRIALMAX,
    if(rem % p == 0,
      s += 1.0/p; found++; rem /= p;
      if(rem % p == 0, sqfree = 0; while(rem % p == 0, rem /= p));
    );
  );
  [s, rem, found, sqfree];
}

/* CRT element of Z/M reducing to r[j] mod W[j] */
crtvec(r, W) = my(x = Mod(r[1], W[1])); for(j = 2, #W, x = chinese(x, Mod(r[j], W[j]))); lift(x);

/* find a removal set D of size <= 2 inside pool making (F) hold for every w in W */
findD(pool, W) =
{
  my(M = prod(j = 1, #W, W[j]), C, c = vector(#pool), rep = vector(M), t);
  C = crtvec(vector(#W, j, lift(sum(i = 1, #pool, Mod(pool[i], W[j])^(-1)))), W);
  /* [1, D] on success (D possibly empty), [0, 0] on failure: gp evaluates [] == 0 as true, so an
     empty vector cannot itself be the failure sentinel */
  if(C == 0, return([1, []]));
  for(i = 1, #pool,
    c[i] = crtvec(vector(#W, j, lift(Mod(pool[i], W[j])^(-1))), W);
    if(c[i] == C, return([1, [i]]));
  );
  for(i = 1, #pool, if(rep[c[i] + 1] == 0, rep[c[i] + 1] = i));
  for(i = 1, #pool,
    t = (C - c[i]) % M;
    if(rep[t + 1] != 0 && rep[t + 1] != i, return([1, [i, rep[t + 1]]]));
  );
  [0, 0];
}

attempt(W, lo, hi) =
{
  my(pool, f, D, keep, a, ap, sa, sl);
  pool = select(p -> !setsearch(Set(W), p), primes([lo, hi]));
  f = findD(pool, W);
  if(f[1] == 0, return(0));
  D = f[2];
  keep = select(i -> !setsearch(Set(D), i), vector(#pool, i, i));
  keep = vector(#keep, i, pool[keep[i]]);
  a = prod(i = 1, #keep, keep[i]);
  ap = dsum(keep);
  for(j = 1, #W, if(ap % W[j] != 0, error("forcing failed at w = ", W[j])));
  sa = mass(keep);
  sl = sigma_lower(ap);
  [sa * sl[1], sa, sl[1], #keep, #digits(a), #digits(sl[2]), sl[4], #D];
}

{
  print("r(a) = sigma(a)*sigma(a') driven by construction.");
  print("prop:nearmiss sweep maximum over a <= 1e7 is 0.5535. Every r below is a rigorous LOWER");
  print("bound (a' trial-divided to ", TRIALMAX, " only, so the true sigma(a') is at least as large).");
  print("");
  print("  W forced into a'    pool range   |D|  w(a)  dig(a)  sigma(a)  sigma(a')>=    r >=   cofac dig");
  print("  --------------------------------------------------------------------------------------------");
  my(rows = [ [[2], 3, 60], [[2], 3, 400], [[2,3], 5, 400], [[2,3], 5, 1500],
              [[2,3,5], 7, 400], [[2,3,5], 7, 2000], [[2,3,5,7], 11, 4000],
              [[2,3,5,7,11], 13, 15000] ], t);
  for(i = 1, #rows,
    t = attempt(rows[i][1], rows[i][2], rows[i][3]);
    if(t == 0,
      printf("  %-18s [%5d,%6d]  -- no removal set of size <= 2\n",
             Str(rows[i][1]), rows[i][2], rows[i][3])
    ,
      printf("  %-18s [%5d,%6d] %3d %5d %7d %9.5f %10.5f %9.5f %8d%s\n",
             Str(rows[i][1]), rows[i][2], rows[i][3], t[8], t[4], t[5], t[2], t[3], t[1], t[6],
             if(t[1] >= 1.0, "   <== r >= 1", ""));
    );
  );
  print("");
  print("(dig = decimal digits; cofac dig = digits of the unfactored part of a', which can only");
  print(" raise sigma(a') further. |D| = number of pool primes dropped to satisfy (F).)");
}
quit;
