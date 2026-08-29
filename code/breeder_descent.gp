/* The Newton descent on G, and its cost accounting (sec:breeder).
 *
 * Adjoining a prime w to M0 acts linearly on G = N*M0 - N'*M0':
 *     G -> w*G - M0*N',   so   |G_new| = |G| * |w - w*|,   w* = M0*N'/G = sigma(N)/eps.
 * G = 0 is exactly #307, so this is a Newton iteration for the problem, quadratic in eps.
 *
 * It fails for a sharp reason. Only w = floor(w*) or ceil(w*) can shrink |G| (need |w-w*| < 1),
 * so a step descends with probability ~ 2/log(w*). But a successful step gives
 *     w*_new = w* * w/theta ~ (w*)^2 / theta,
 * so log(w*) more than DOUBLES each step while log|G| falls by only |log theta| ~ 0.69.
 * Gain is 2^-k; survival probability is prod 2/log(w*_j) ~ 2^(-k^2/2).
 *
 * This script prints the accounting from the greedy frame N = 30, M0 = prod_{7<=p<=271} p,
 * where log|G| = 249 and w* = 428.2. Even 10^12 independent paths reach depth 8 and shrink |G|
 * by 256, against the 10^108 needed. See also code/breeder_supply.gp and prop:nearframe.
 *
 * Run:  gp -q -f breeder_descent.gp
 */

\p 30
{
my(lw, lG, surv, k, p, totshrink);
print("DESCENT ACCOUNTING for G_new = qG - 31M, |G_new| = |G|*|q - w*|, w* = 31M/G.");
print("A step shrinks |G| only if floor(w*) or ceil(w*) is prime: probability ~ 2/log(w*).");
print("After a successful step, w*' = w* * q/|theta| ~ w*^2/|theta|, so log w* MORE THAN DOUBLES.");
print("");
print(" k | log(w*)   | P(step) | P(survive k) | log|G| dropped | log|G| still needed");
lw = log(428.22); lG = log(10)*108; surv = 1.0; totshrink = 0;
for(k = 1, 12,
  p = 2/lw;
  surv = surv * p;
  totshrink = totshrink + 0.693;
  printf(" %2d | %9.2f | %7.5f | %12.3e | %14.2f | %10.2f\n",
         k, lw, p, surv, totshrink, lG - totshrink);
  lw = 2*lw + 0.693;
);
print("");
print("So |G| falls like 2^-k while survival falls like 2^(-k^2/2).");
print("Expected deepest reachable k with a beam of B paths is about where surv ~ 1/B:");
my(B);
for(e = 2, 12,
  B = 10^e;
  lw = log(428.22); surv = 1.0; k = 0;
  while(surv > 1.0/B && k < 40, k++; surv = surv*2/lw; lw = 2*lw + 0.693);
  printf("  beam/paths 10^%2d  ->  depth k ~ %2d  ->  |G| shrinks by 2^%d = %.3e  (need 10^108)\n",
         e, k, k, 2.0^k);
);
}
quit;
