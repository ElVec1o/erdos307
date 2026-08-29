/* Audit of Kovic, J. Integer Seq. 15 (2012), Art. 12.3.8, Proposition 18.
 *
 * Kovic treats the two-cycle n' = m, m' = n for squarefree n = p_1...p_r, m = q_1...q_s.
 * His proof opens with two correct pairs of bounds, which after substituting n' = m, m' = n read
 *
 *   (A)  r*n/p_r < m < r*n/p_1        (B)  s*m/q_s < n < s*m/q_1
 *
 * and then asserts "Hence: p_1*q_s < r*s and q_1*p_r < r*s". Everything downstream rests on those
 * two: p_1 < r, q_1 < s, 2*max{p_r,q_s} < N^2/4, and hence r+s >= 34, the conditional 57 and 110,
 * and max{m,n} >= prod of the first 17 primes.
 *
 * Multiplying inequalities is sound only when the directions match:
 *   upper x upper  gives  p_1*q_1 < r*s
 *   lower x lower  gives  r*s     < p_r*q_s
 * Kovic's p_1*q_s pairs an UPPER bound on m with a LOWER bound on n; the directions do not compose.
 *
 * This script exhibits an explicit model -- squarefree, disjoint supports, r = s = 10 -- satisfying
 * all four of his displayed inequalities while both claimed consequences fail. It refutes the
 * INFERENCE, not the statement: no two-cycle is known, so no counterexample to r+s >= 34 exists to
 * be given, and none is claimed. The statement is unproven, not false; it is in fact true, as a
 * corollary of the barrier |U| >= 60 of this note, which is proved by an unrelated route.
 *
 * Run:  gp -q -f kovic_prop18_audit.gp
 */

\p 40
{
my(np, nq, n, m, r, s, p1, pr, q1, qs, ok);

np = [2, 5, 13, 37, 53, 73, 79, 89, 97, 101];
nq = [3, 7, 19, 31, 43, 59, 67, 71, 83, 103];
n = prod(i = 1, #np, np[i]);
m = prod(i = 1, #nq, nq[i]);
r = #np; s = #nq;
p1 = np[1]; pr = np[r]; q1 = nq[1]; qs = nq[s];

print("model");
print("  n = ", n, "   primes ", np);
print("  m = ", m, "   primes ", nq);
print("  r = ", r, "  s = ", s, "  p1 = ", p1, "  pr = ", pr, "  q1 = ", q1, "  qs = ", qs);
print("  n, m squarefree      : ", issquarefree(n) && issquarefree(m));
print("  supports disjoint    : ", #setintersect(Set(np), Set(nq)) == 0);
print("  all primes distinct  : ", #Set(concat(np, nq)) == r + s);
print("");

ok = (r*n/pr < m) && (m < r*n/p1) && (s*m/qs < n) && (n < s*m/q1);
print("Kovic's four displayed inequalities");
print("  r*n/p_r < m          : ", r*n/pr < m);
print("  m < r*n/p_1          : ", m < r*n/p1);
print("  s*m/q_s < n          : ", s*m/qs < n);
print("  n < s*m/q_1          : ", n < s*m/q1);
print("  ALL FOUR HOLD        : ", ok);
print("");

print("valid consequences (same-direction products)");
print("  p_1*q_1 < r*s        : ", p1*q1, " < ", r*s, "   -> ", p1*q1 < r*s);
print("  r*s < p_r*q_s        : ", r*s, " < ", pr*qs, "   -> ", r*s < pr*qs);
print("");

print("Kovic's claimed consequences");
print("  p_1*q_s < r*s        : ", p1*qs, " < ", r*s, "   -> ", p1*qs < r*s, "   FAILS");
print("  q_1*p_r < r*s        : ", q1*pr, " < ", r*s, "   -> ", q1*pr < r*s, "   FAILS");
print("");

print("structural reason the step is unrecoverable");
print("  the cycle says exactly  sigma(n) in (r/p_r, r/p_1)  and  sigma(m) = 1/sigma(n) in (s/q_s, s/q_1),");
print("  i.e. sigma(n) lies in  (r/p_r, r/p_1) cap (q_1/s, q_s/s).  That intersection is nonempty iff");
print("    q_1/s < r/p_1   <=>   p_1*q_1 < r*s      and      r/p_r < q_s/s   <=>   r*s < p_r*q_s,");
print("  and iff nothing else.  Kovic's p_1*q_s < r*s  <=>  q_s/s < r/p_1  compares the two UPPER");
print("  endpoints, a relation nonemptiness never constrains.");
print("");

print("arithmetic slips in the same proposition");
print("  Table 2 lists P_11 = 27; prime(11) = ", prime(11), "   (27 = 3^3 is not prime)");
print("  the 'product of the first 17 primes' is printed as");
print("    2*3*5*7*11*13*17*19*23*27*31*37*41*43*47*53*59 = ", 2*3*5*7*11*13*17*19*23*27*31*37*41*43*47*53*59);
print("  with 27 in place of 29; the actual primorial is  ", prod(i = 1, 17, prime(i)));
print("");

print("status of the surrounding results");
print("  Prop. 16 (no solution with both members a product of two primes) : proof sound");
print("  Prop. 17 (>= 9 primes, n > 3*5*...*29 = ", prod(i = 2, 10, prime(i)), ") : proof sound, but CONDITIONAL --");
print("    it assumes the SMALLER member is odd, and Kovic notes no estimate follows otherwise");
print("  computer search x'' = x, x < 10000                               : unconditional");
print("  Prop. 18                                                          : inference invalid");
print("");
print("  strongest valid UNCONDITIONAL prior bound is therefore the search bound 10^4;");
print("  this note gives |U| >= 60 and min(prod P, prod Q) >= 2.09e56, unconditionally, for both members.");
}
quit;
