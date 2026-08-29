/* Supply-demand measurement for the bilinear breeder (sec:breeder, prop:nearframe).
 *
 * A frame (M0, N) proposes candidates through divisors d of K = G N^2 + c^2 with d = -c (mod G),
 * where G = N*M0 - N'*M0' and c = M0*N'. The supply is tau(K)/|G|; a productive frame needs it
 * well above 1. This script bins frames by |G| and reports, per bin, the best tau(K)/|G| and the
 * exact number of admissible divisors.
 *
 * Result: the ratio peaks at the SMALLEST frames (0.600 at log10|G| ~ 0.5, attained at
 * (M0,N) = (2,3) with G = 5) and decays monotonically -- 0.313, 0.214, 0.053, 0.0065, 0.0030 at
 * log10|G| ~ 1.5, 2.5, 3.5, 4.5, 5.0. It never reaches 1. Together with prop:nearframe, which
 * shows near-miss frames satisfy |G| >= a' and so are extremal in the wrong direction, this closes
 * the "steer G small" reading of the breeder.
 *
 * Run:  gp -q -f breeder_supply.gp
 */

\p 30
ader(n) = { my(f = factor(n)); n * sum(i = 1, #f~, f[i,2]/f[i,1]); }
{
my(bins, cnt, bestE, bestf, bestR, bestRf);
bins = vector(12, i, [0, 0, 0]);   /* [count, max tau/|G|, max actualdivs] */
bestE = 0; bestf = 0; bestR = 0; bestRf = 0;
forsquarefree(M = 2, 400,
  my(m0, M0p);
  m0 = M[1]; if(m0 < 2, next);
  M0p = ader(m0);
  forsquarefree(NN = 2, 400,
    my(N, Np, G, c, K, tk, ratio, b, adm, ds, E);
    N = NN[1]; if(N < 2 || gcd(m0, N) != 1, next);
    Np = ader(N);
    G = N*m0 - Np*M0p;
    if(G == 0, next);
    c = m0*Np; K = G*N^2 + c^2;
    if(K <= 0 || K > 10^13, next);
    tk = numdiv(K);
    ratio = 1.0*tk/abs(G);
    b = min(12, 1 + floor(log(1.0*abs(G))/log(10)*2));
    if(b < 1, b = 1);
    bins[b][1]++;
    if(ratio > bins[b][2], bins[b][2] = ratio);
    if(ratio > bestR, bestR = ratio; bestRf = [m0, N, G, tk]);
    /* exact admissible divisor count */
    ds = divisors(K); adm = 0;
    for(i = 1, #ds,
      my(d); d = ds[i];
      if((d + c) % G == 0 && (K/d + c) % G == 0 && (d+c)/G > 1 && (K/d+c)/G > 1, adm++);
    );
    if(adm > bins[b][3], bins[b][3] = adm);
    if(adm > 0,
      E = adm / (log(1.0*abs(K))^3);
      if(E > bestE, bestE = E; bestf = [m0, N, G, adm]);
    );
  );
);
print("bin (by log10|G|, half-decade) : count, max tau(K)/|G|, max exact admissible divisors");
for(i = 1, 12,
  if(bins[i][1] > 0,
    print("  log10|G| ~ ", (i-1)/2.0, " : n=", bins[i][1],
          "  max tau/|G| = ", bins[i][2], "  max adm = ", bins[i][3]);
  );
);
print("");
print("best tau(K)/|G| overall : ", bestR, " at (M0,N,G,tau) = ", bestRf);
if(bestf != 0, print("best E (adm/log^3 K)    : ", bestE, " at (M0,N,G,adm) = ", bestf));
}
quit;
