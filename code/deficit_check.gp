\\ Remark "What the constant c_r is and is not": the measured quantities at r = 5.
\\ h_t is Halasz's multiplicative function: h_t(p) = chi(p) e_r(t p^{-1}) for p not dividing r,
\\ and h_t(p) = 0 for p | r.  Both sums below therefore run over ALL p <= X; the primes p | r
\\ contribute (1 - 0)/p = 1/p to M.  Dropping them is the natural slip and shifts every number.
\\   M(X) = sum_{p<=X} (1 - Re h_t(p))/p   at tau = 0
\\   S(X) = sum_{p<=X} 1/p
\\   deficit = c_r S(X) - M(X),   c_r = 1 - sqrt(r)/phi(r)
{
my(r, cr, dr, S, M1, M2, hp, X, k, pm, pS, first);
r = 5; cr = 1 - sqrt(5)/4.0; dr = 1 + sqrt(5)/4.0;
S = 0.0; M1 = 0.0; M2 = 0.0; k = 4; X = 10^4; pm = 0.0; pS = 0.0; first = 1;
forprime(p = 2, 10^7,
  S += 1.0/p;
  if(r % p != 0,
    hp = kronecker(p, r) * exp(2*Pi*I*lift(Mod(p,r)^(-1))/r);
    M1 += (1 - real(hp))/p;
    hp = kronecker(p, r) * exp(2*Pi*I*2*lift(Mod(p,r)^(-1))/r);
    M2 += (1 - real(hp))/p
  ,
    M1 += 1.0/p; M2 += 1.0/p);
  if(p > X && k <= 7,
    printf("X=10^%d  M=%.6f  S=%.6f  deficit=%.6f", k, M1, S, cr*S - M1);
    if(first, first = 0, printf("  growth dM/dS=%.6f", (M1-pm)/(S-pS)));
    print("");
    pm = M1; pS = S; k += 1; X = 10^k));
printf("X=10^7  M=%.6f  S=%.6f  deficit=%.6f  growth dM/dS=%.6f\n",
       M1, S, cr*S - M1, (M1-pm)/(S-pS));
printf("chi(t)=-1 branch: M_2(10^7) = %.6f against leading term c_r S = %.6f\n", M2, cr*S);
printf("c_5 = %.6f   1 + sqrt(5)/4 = %.6f\n", cr, dr);
}
quit;
