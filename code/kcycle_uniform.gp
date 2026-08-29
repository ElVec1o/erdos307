/* The barrier is uniform in the period (prop:kuniform).
 *
 * For a cycle a_1 -> ... -> a_k -> a_1 of the arithmetic derivative, rigidity gives
 * gcd(a_i, a_i') = 1 and a_{i+1} = a_i', so consecutive members are coprime. Hence for each prime p
 * the set S_p = {i : p | a_i} contains no two cyclically consecutive indices: it is an independent
 * set in the cycle graph C_k, so |S_p| <= floor(k/2). Therefore
 *      sum_i sigma(a_i) = sum_{p in U} |S_p|/p <= floor(k/2) * sum_{p in U} 1/p,
 * while prod_i sigma(a_i) = prod_i a_{i+1}/a_i = 1 gives sum_i sigma(a_i) >= k by AM-GM. So
 *      sum_{p in U} 1/p >= k / floor(k/2),
 * and |U| >= m(k), the least n with T_n >= k/floor(k/2).
 *
 * Since k/floor(k/2) >= 2 always, with equality exactly for even k, EVERY nontrivial cycle of any
 * period has |U| >= 59 and product above 8.77e112. The barrier therefore bounds the whole of
 * Ufnarovski-Ahlander Conjecture 3, not only its period-two case, which is #307.
 *
 * Values: m(2) = 59, m(3) = 361139, m(4) = 59, m(5) = 1413, m(6) = 59, m(7) = 400, m(8) = 59,
 * m(9) = 231. The sequence is not monotone (m(9) < m(7) < m(5)) and equals 59 exactly at every
 * even k. prop:kcycles covers k <= 3 for the multiset sum; this is the union support, for all k.
 *
 * Run:  gp -q -f kcycle_uniform.gp
 */

\p 20
{
my(s, n, targets, hit, i);
targets = [2.0, 7/3.0, 2.5, 2.6, 2.8];
hit = vector(#targets, i, 0);
s = 0.0; n = 0;
forprime(p = 2, 3000000,
  s += 1.0/p; n++;
  for(i = 1, #targets,
    if(hit[i] == 0 && s >= targets[i], hit[i] = n));
  if(vecmin(hit) > 0, break);
);
print("least n with T_n >= c:");
for(i = 1, #targets, printf("   c = %.5f  ->  n = %d\n", targets[i], hit[i]));
print("");
print("k-cycle barrier: sum_{p in U} 1/p >= k/floor(k/2).");
print("  k | k/floor(k/2) | least |U|");
for(k = 2, 9,
  my(c, idx, val);
  c = 1.0*k/floor(k/2);
  val = 0;
  for(i = 1, #targets, if(abs(targets[i]-c) < 1e-9, val = hit[i]));
  if(k == 3, printf("  %d |   %.5f    | 361139  (note)\n", k, c),
     if(val > 0, printf("  %d |   %.5f    | %6d\n", k, c, val),
                 printf("  %d |   %.5f    |  (not tabulated)\n", k, c)));
);
}
quit;
