/* heuristic_location.gp -- where the expected-count heuristic puts the first two-cycle, and how
 * sensitively that location depends on the one constant nobody can measure.
 *
 * Model. r(a) = a''/a = sigma(a)sigma(a'), and a two-cycle is exactly r(a) = 1. If r has a limiting
 * density f on the admissible class (a and a' both squarefree), then P(a'' = a) = P(r in [1,1+1/a))
 * ~ f(1)/a, so the expected number of two-cycles with a <= X is
 *
 *      E(X) ~ f(1) * delta * log X,        delta = density of the admissible class.
 *
 * Two things follow, and they pull in opposite directions:
 *   (1) E(X) DIVERGES. The heuristic predicts infinitely many two-cycles, so any proof of the
 *       negative direction must explain why a divergent expected count yields zero solutions.
 *   (2) The first solution sits at X = exp(1/(delta f(1))), which is EXPONENTIAL in 1/f(1). So the
 *       location is not merely uncalibrated, it is exponentially sensitive to an unmeasurable
 *       constant: a factor 2 in f(1) squares the answer.
 *
 * delta is measured, not modelled: code/region_shape.rs found 3,721,148 admissible a below 10^7.
 *
 * Usage: gp -q -f heuristic_location.gp
 */

delta = 3721148 / 10000000.0;      /* measured density of the admissible class below 1e7 */
BARRIER = 112.9;                   /* log10 of the proved barrier on prod U (thm:barrier) */

print("admissible density delta = ", delta, "   (code/region_shape.rs, a <= 1e7)");
print("");
print("  f(1)        log X = 1/(delta f(1))     first two-cycle near 10^K, K =");
print("  ---------------------------------------------------------------------");
{
  my(fs = [0.05, 0.02, 0.0146, 0.01, 0.005, 0.002, 0.001, 0.0001]);
  for(i = 1, #fs,
    my(f = fs[i], lx = 1/(delta*f), k = lx/log(10));
    printf("  %-10.4f  %18.1f  %28.1f%s\n", f, lx, k,
           if(k < BARRIER, "   <-- below the proved barrier", ""));
  );
}
print("");
fmax = 1/(delta*BARRIER*log(10));
printf("The proved barrier is 10^%.1f. Consistency of the model with it needs f(1) < %.5f,\n", BARRIER, fmax);
print("which is soft evidence only: E(X) is an expectation, and observing no solution where");
print("E = 2 is an ordinary event, not a contradiction.");
print("");
print("Sensitivity: halving f(1) SQUARES the location.");
{
  my(f = 0.01, k1 = 1/(delta*f)/log(10), k2 = 1/(delta*f/2)/log(10));
  printf("  f(1) = %.3f gives 10^%.0f;  f(1) = %.4f gives 10^%.0f.\n", f, k1, f/2, k2);
}
print("");
print("So the honest reading is: the heuristic diverges, so YES is expected; but the scale at");
print("which it is expected is exp(1/(delta f(1))), and f(1) is exactly the quantity");
print("prop:nearmiss shows cannot be sampled. Nothing about the location is knowable at present.");
quit;
