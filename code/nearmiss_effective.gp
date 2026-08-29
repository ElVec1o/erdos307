/* An effective form of the approximation theorem, with a certified witness.
 *
 * Bado's Thm 10.2 states that for every Y and every eps there are disjoint finite prime sets
 * P, Q, all primes > Y, with 0 <= sigma(P)sigma(Q) - 1 < eps. The proof is a greedy accumulation
 * and is INEFFECTIVE: it exhibits no witness and gives no rate. Making it effective shows the
 * greedy is expensive. To land in [T, T+eta) using primes > Y one needs 1/p < eta, so the
 * accumulation starts above ~1/eta, and Mertens gives
 *      sum_{Y1 < p <= W} 1/p ~ loglog W - loglog Y1 = T   =>   W = Y1^(e^T).
 * Two stages with T ~ 1 put the largest prime at ~eps^(-e^2) = eps^(-7.389...), and the number of
 * primes at the same order. At eps = 1e-13 that is a largest prime near 10^94 and some 10^92 of
 * them: not a construction anyone can exhibit.
 *
 * A Newton ladder does the same job with a handful of primes. Take Q = {2,3,5}, so sigma(Q) = 31/30
 * and the target for P is 30/31. Start from a pool, then repeat: p <- nextprime(ceil(1/d)),
 * d <- d - 1/p, where d is the running deficit. Each rung squares the deficit,
 *      d_new = d - 1/p ~ t d^2,    t the local prime gap,
 * so the largest prime is ~eps^(-1/2) and the number of rungs is O(loglog(1/eps)).
 *
 * With the pool = primes 7..271 and nine rungs this gives 64 primes in P and 3 in Q, largest prime
 * 505 digits, and
 *      |sigma(P)sigma(Q) - 1| = 9.5748...e-1007,
 * computed in exact rational arithmetic. Every rung prime is PROVED prime by isprime (APR-CL), the
 * 505-digit one in about six seconds; the whole verification runs in under ten.
 *
 * Scope. This is an approximation result and nothing more. It does not approach a solution of #307:
 * a free pair of disjoint prime sets carries none of the rigidity that an exact hit requires, and by
 * prop:nearmiss the size of |sigma(P)sigma(Q) - 1| does not measure progress towards the integer
 * identity. What it does is make Thm 10.2 effective, exhibit a witness, and show that the greedy
 * route is doubly exponentially wasteful.
 *
 * Run:  gp -q -f nearmiss_effective.gp
 */

default(parisizemax, 4000000000);
\p 40
{
my(s, d, R, sP, sQ, prod, t0, k);
sQ = 1/2 + 1/3 + 1/5;
s = 0; forprime(q = 7, 271, s += 1/q);
d = 1/sQ - s;
R = List();
print("Q = {2,3,5},  sigma(Q) = 31/30;   target for P is 30/31");
print("pool = primes 7..271  (55 primes)");
printf("initial deficit d0 = %.6e\n\n", 1.0*d);
for(k = 1, 9,
  my(pk);
  pk = nextprime(ceil(1/d));
  listput(R, pk);
  d = d - 1/pk;
  printf("  rung %d: prime has %3d digits,  deficit -> %.6e\n", k, #digits(pk), 1.0*d);
);
sP = s + sum(i = 1, #R, 1/R[i]);
prod = sP*sQ;
print("");
print("|P| = ", 55 + #R, "   |Q| = 3   supports disjoint: ", vecmin(Vec(R)) > 271);
printf("sigma(P)sigma(Q) - 1 = %.6e   (exact rational, %d-digit numerator over %d-digit denominator)\n",
       1.0*(prod-1), #digits(numerator(prod-1)), #digits(denominator(prod-1)));
print("");
print("certifying every rung prime with APR-CL (isprime is a proof, not a test):");
for(i = 1, #R,
  t0 = getabstime();
  printf("  rung %d (%3d digits): isprime = %d   [%.1f s]\n",
         i, #digits(R[i]), isprime(R[i]), (getabstime()-t0)/1000.0);
);
print("");
print("truncations, for a reader who wants a smaller certificate:");
for(k = 4, 9,
  my(s2, prod2);
  s2 = 0; forprime(q = 7, 271, s2 += 1/q);
  s2 += sum(i = 1, k, 1/R[i]);
  prod2 = s2*sQ;
  printf("  %d rungs (largest %3d digits): |sigma(P)sigma(Q) - 1| = %.4e\n",
         k, #digits(R[k]), 1.0*abs(prod2-1));
);
}
quit;
