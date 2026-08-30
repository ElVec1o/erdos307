/* The derivative cannot outgrow its own support (prop:growth).
 *
 * For a squarefree orbit segment a_0 -> ... -> a_L with G = a_L/a_0 and U the union of the supports
 * over i < L, rigidity makes consecutive members coprime, so S_p = {i < L : p | a_i} is independent
 * in the PATH on L vertices and |S_p| <= ceil(L/2). With prod_{i<L} sigma(a_i) = G and AM-GM,
 *      sum_{p in U} 1/p >= (L/ceil(L/2)) G^(1/L),      G <= (ceil(L/2) T_|U| / L)^L,
 * so for even L the per-step growth rate satisfies G^(1/L) <= T_|U| / 2.
 *
 * At L = 2 this is cor:cost with G = r; at G = 1 it is prop:kuniform on the path. What it adds is
 * dynamical: it bounds the growth branch of Ufnarovski-Ahlander Conjecture 2. A squarefree orbit
 * doubling at every step needs about 4.3e16 distinct primes and a prime past 1.8e18.
 *
 * The squarefree hypothesis is essential and is not generic along orbits; it is automatic on
 * cycles by Ufnarovski-Ahlander, which is why the cycle rows of rem:dictionary carry no caveat.
 *
 * Run:  gp -q -f growth_bound.gp
 */

\p 20
{
my(gs, tg, hit, s, n, i, M);
M = 0.2614972128;
print("ORBIT GROWTH BOUND. For a_0 -> ... -> a_L squarefree, U = union of supports over i < L:");
print("  prod_{i<L} sigma(a_i) = a_L/a_0 = G, so AM-GM gives sum_{i<L} sigma(a_i) >= L G^(1/L).");
print("  S_p = {i < L : p | a_i} has no two consecutive indices (rigidity), so it is independent");
print("  in the PATH on L vertices and |S_p| <= ceil(L/2). Hence");
print("      sum_{p in U} 1/p  >=  (L/ceil(L/2)) G^(1/L),");
print("  and inverting, G <= (ceil(L/2) T_|U| / L)^L; for even L, G <= (T_|U| / 2)^L.");
print("");
print("So the per-step geometric growth rate g satisfies  g <= T_|U| / 2 :");
print("the derivative cannot outgrow half the Mertens mass of its own support.");
print("");
gs = [1.05, 1.1, 1.25, 1.5, 1.75, 2.0];
tg = vector(#gs, i, 2*gs[i]);
hit = vector(#gs, i, 0);
s = 0.0; n = 0;
forprime(p = 2, 30000000, s += 1.0/p; n++;
  for(i = 1, #gs, if(hit[i]==0 && s >= tg[i], hit[i] = n));
  if(vecmin(hit) > 0, break));
print("   growth g | needs T_|U| >= 2g |   |U| >= n(2g)   | largest prime >= about");
for(i = 1, #gs,
  my(lp);
  lp = exp(exp(tg[i] - M));
  if(hit[i] > 0,
    printf("    %.2f    |     %.2f          | %14d   | %.3e\n", gs[i], tg[i], hit[i], lp),
    printf("    %.2f    |     %.2f          | ~ pi(%.2e) = %.2e | %.3e\n",
       gs[i], tg[i], lp, lp/log(lp), lp));
);
print("");
print("So a doubling orbit (g = 2) needs a union support of about 4e16 primes.");
print("Sustained rapid growth is impossible for the arithmetic derivative on a small support.");
}
quit;
\p 25
{
my(s, n, gs, tg, hit, i, l2, lgX);
print("Sustaining growth rate g over a squarefree orbit needs T_|U| >= 2g, so |U| >= n(2g).");
print("With every member at most X: omega(a_i) <= log2 X and L <= log_g X, so");
print("     |U| <= L log2 X <= (log2 X)^2 log2(g)^{-1} ... rearranged,");
print("     log2 X  >=  sqrt( n(2g) * log2(g) ).");
print("");
gs = [1.10, 1.25, 1.50, 1.75, 2.00];
tg = vector(#gs, i, 2*gs[i]);
hit = vector(#gs, i, 0);
s = 0.0; n = 0;
forprime(p = 2, 30000000, s += 1.0/p; n++;
  for(i = 1, #gs, if(hit[i]==0 && s >= tg[i], hit[i] = n));
  if(vecmin(hit) > 0, break));
print("   rate g | needs T >= | n(2g)        | members must exceed");
for(i = 1, #gs,
  my(nn);
  if(hit[i] > 0, nn = 1.0*hit[i],
     nn = exp(exp(tg[i] - 0.2614972128)); nn = nn/log(nn));
  l2 = sqrt(nn * log(gs[i])/log(2));
  lgX = l2 * log(2)/log(10);
  printf("    %.2f  |    %.2f    | %.4e | 10^%.4g\n", gs[i], tg[i], nn, lgX);
);
print("");
print("So the transition is sharp. Growth at 1.10 needs only members past 10^2, which is");
print("attainable; 1.50 needs 10^138; doubling needs 10^(6.2e7). The arithmetic derivative");
print("can grow slowly at any scale and fast only at scales no computation reaches.");
}
quit;
