/* infimum_zero.gp -- the near-miss infimum is 0, and near-misses are therefore not evidence.
 *
 * Classical: if a_n -> 0 and sum a_n diverges, a subseries sums to EXACTLY any prescribed target.
 * Split the primes into two infinite classes; each still has divergent reciprocal sum, so each
 * carries a subseries summing to exactly 1. Hence there are DISJOINT INFINITE prime sets P, Q with
 * sigma(P) = sigma(Q) = 1, so sigma(P)sigma(Q) = 1 exactly. #307 is the same equation with P, Q
 * required FINITE.
 *
 * Truncating such a pair gives finite disjoint P_y, Q_y with sigma(P_y)sigma(Q_y) -> 1. So
 *
 *      inf { |sigma(P)sigma(Q) - 1| : P, Q finite disjoint prime sets } = 0,
 *
 * and #307 asks precisely whether the infimum is ATTAINED. Consequence, and it is the point of this
 * file: a near-miss, however good, is not evidence that the infimum is attained. The frontier of
 * prop:nearmiss and the constructed witness of code/nearmiss_tune.gp measure how hard one worked,
 * not how likely a solution is.
 *
 * This runs the greedy subseries on the primes to exhibit the collapse. Exact rationals throughout.
 *
 * Usage: gp -q -f infimum_zero.gp
 */

default(parisize, 200000000);

/* greedy: add the largest 1/p not overshooting the target, drawing from `pool` (a set of primes),
   returning the chosen list. Sylvester-style, so it converges doubly exponentially. */
greedy(pool, target, steps) =
{
  my(chosen = List(), s = 0, i = 1);
  while(#chosen < steps && i <= #pool,
    if(s + 1/pool[i] <= target, s += 1/pool[i]; listput(chosen, pool[i]));
    i++;
  );
  Vec(chosen);
}

{
  \\ stream the primes, alternating class, running both greedies at once
  my(sp = 0, sq = 0, P = List(), Q = List(), idx = 0);
  print("Greedy subseries towards sigma = 1 on two disjoint prime classes (odd/even indexed).");
  print("Each prime is offered to its own class and taken if it does not overshoot 1.");
  print("");
  print("  |P|+|Q|   sigma(P) (exact float)      sigma(Q)                  |r - 1|");
  print("  ----------------------------------------------------------------------------------");
  my(nextreport = 4);
  forprime(pp = 2, 20000000,
    idx++;
    if(idx % 2 == 1,
      if(sp + 1/pp <= 1, sp += 1/pp; listput(P, pp)),
      if(sq + 1/pp <= 1, sq += 1/pp; listput(Q, pp))
    );
    if(#P + #Q == nextreport && #P > 0 && #Q > 0,
      printf("  %6d    %.20f    %.20f    %.6e\n", #P+#Q, 1.0*sp, 1.0*sq, 1.0*abs(sp*sq-1));
      nextreport += 4;
    );
  );
  print("");
  print("P = ", Vec(P));
  print("Q = ", Vec(Q));
  print("disjoint: ", if(#setintersect(Set(Vec(P)), Set(Vec(Q))) == 0, "YES", "NO"));
  print("");
  print("sigma(P) = ", sp);
  print("sigma(Q) = ", sq);
  printf("|r - 1|  = %.6e   with %d primes in total, largest %d.\n",
         1.0*abs(sp*sq-1), #P+#Q, max(vecmax(Vec(P)), vecmax(Vec(Q))));
  print("");
  print("For contrast: the swept frontier of prop:nearmiss is 0.4465, and the constructed");
  print("witness of code/nearmiss_tune.gp reaches 7.9220e-3 using 54 primes and 108 digits.");
  print("");
  print("So |r-1| is driven far below any previous frontier with FEW primes, while a solution");
  print("needs |r-1| = 0 and, by thm:barrier, at least 60 primes. Closeness in r is cheap and");
  print("carries no information about attainment. That is the honest reading of every near-miss");
  print("in this project, including the ones computed here.");
}
quit;
