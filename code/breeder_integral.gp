/* Integrality of q in the bilinear breeder (prop:bde, prop:bdeint).
 *
 * Fix coprime squarefree M0, N and seek a two-cycle a = M0*r*p, b = N*q. With
 * G = N*M0 - N'*M0', c = M0*N', K = G*N^2 + c^2, each divisor d of K with d = -c (mod G)
 * proposes r = (d+c)/G, p = (K/d+c)/G, and then q = (M0*r*p - N)/N'.
 *
 * That last expression is a quotient by N', which at the barrier is astronomical, so one might
 * expect a candidate to be usable only when N' happens to divide M0*r*p - N. It is automatic:
 * the bilinear equation is equivalent to G*r*p - c*(r+p) = N^2, which rearranges to
 * N*(a - N) = N'*a', and gcd(N, N') = 1 for squarefree N forces N | a', so q = a'/N in Z.
 *
 * This script is the empirical side of that: it scans frames, collects every admissible divisor
 * candidate, and reports how many have integral q. Result over 51,132 frames: 9 candidates,
 * 9 integral, 0 not. Proved in prop:bdeint and lean/Erdos307/Breeder.lean.
 *
 * Run:  gp -q -f breeder_integral.gp
 */

\p 40
ader(n) = { my(f = factor(n)); n * sum(i = 1, #f~, f[i,2]/f[i,1]); }
{
my(tot, integral, nonint, frames, hits, LIM);
tot = 0; integral = 0; nonint = 0; frames = 0; hits = 0; LIM = 3000;
forsquarefree(M0 = 2, 300,
  my(m0 = M0[1]);
  if(m0 < 2, next);
  forsquarefree(NN = 2, 600,
    my(N, M0p, Np, G, c, K, ds);
    N = NN[1];
    if(N < 2 || gcd(m0, N) != 1, next);
    M0p = ader(m0); Np = ader(N);
    G = N*m0 - Np*M0p;
    if(G <= 0, next);
    c = m0*Np; K = G*N^2 + c^2;
    if(K > 10^14, next);
    frames++;
    ds = divisors(K);
    for(i = 1, #ds,
      my(d, r, p, q);
      d = ds[i];
      if((d + c) % G != 0, next);
      if((K/d + c) % G != 0, next);
      r = (d + c)/G; p = (K/d + c)/G;
      if(r <= 1 || p <= 1, next);
      tot++;
      q = (m0*r*p - N)/Np;
      if(denominator(q) == 1,
        integral++;
        if(hits < 12,
          hits++;
          print("  M0=", m0, " N=", N, " G=", G, " r=", r, " p=", p, " q=", q,
                "  [r,p,q prime? ", isprime(r), ",", isprime(p), ",", if(q>1,isprime(q),0), "]");
        ),
        nonint++);
    );
  );
);
print("");
print("frames scanned                      : ", frames);
print("admissible divisor candidates (r,p) : ", tot);
print("  with q an INTEGER                 : ", integral);
print("  with q NOT an integer             : ", nonint);
if(tot > 0, print("  integer-q rate                    : ", 1.0*integral/tot));
}
quit;
