\\ The inverse-phase prime sum S(X,p,s,tau) = sum_{l<=X prime} e_p(s*l^{-1}) l^{-1-i tau}.
\\ The phase depends only on l mod p, so the sum reorganises with NO loss as
\\   S = sum_{a != 0} e_p(s a^{-1}) * sum_{l = a (p), l<=X} l^{-1-i tau},
\\ and sum_{a != 0} e_p(s a^{-1}) = -1.  Hence at tau = 0, by Mertens in progressions,
\\   S(X,p,s,0) = -(loglog X)/(p-1) + c(p,s) + o(1).
\\ Two things are measured here: that drift, and max_s |S|, which is what the paper's
\\ sqrt(p) coefficient mass is supposed to bound.
{
my(X1, X2, S1, S2, drift, best, v, l, a);
print("drift (S(10^7)-S(10^5))/(loglog 10^7 - loglog 10^5)   vs   -1/(p-1):");
foreach([[5,1],[5,2],[7,1],[7,3],[11,2],[13,2],[101,1],[101,3]], ps,
  my(p = ps[1], s = ps[2]);
  S1 = 0.0; S2 = 0.0;
  forprime(l = 2, 10^7,
    if(l == p, next);
    a = lift(Mod(s,p) * Mod(l,p)^(-1));
    v = exp(2*Pi*I*a/p)/l;
    if(l <= 10^5, S1 += v);
    S2 += v);
  drift = (S2 - S1)/(log(log(10.0^7)) - log(log(10.0^5)));
  printf("  p=%4d s=%d   measured %9.6f %+9.6fi     predicted %9.6f\n",
         p, s, real(drift), imag(drift), -1.0/(p-1)));
print("");
print("max_s |S(10^6,p,s,0)|  vs  sqrt(p)  --  the mass the character expansion pays:");
foreach([13, 101, 503, 1009, 2003], p,
  my(acc = vector(p, i, 0.0), r, t);
  forprime(l = 2, 10^6,
    if(l == p, next);
    r = lift(Mod(l,p)^(-1));
    acc[r+1] += 1.0/l);
  best = 0.0;
  for(s = 1, p-1,
    S1 = 0.0;
    for(r = 1, p-1, S1 += acc[r+1] * exp(2*Pi*I*lift(Mod(s*r,p))/p));
    if(abs(S1) > best, best = abs(S1)));
  printf("  p=%5d   max_s |S| = %7.4f     sqrt(p) = %7.2f\n", p, best, sqrt(p)));
}
quit;
