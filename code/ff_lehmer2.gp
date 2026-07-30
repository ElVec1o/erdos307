/* Does the power-of-two pattern come from Chebyshev composition, and does it hold for the ACTUAL
 * shape q_n = (x_n^2 - D)/A rather than for x_n itself? x_n satisfies x_{n+1} = 2X x_n - x_{n-1}
 * with x_0 = 1, x_1 = X, so x_n = T_n(X), the Chebyshev polynomial. T_{ab} = T_a o T_b, and T_n is
 * divisible by T_1 = x for n odd, which is exactly why irreducibility wants n a power of 2.
 * Test both sequences over F_p[t] and, separately, the same statement over Z.
 */
print("=== over F_3[t]: x_n = T_n(X) versus q_n = x_n^2 - D ===");
{
my(p = 3, D = Mod(1,p)*(t^2+1), X = Mod(1,p)*(2*t^2+1));
my(a = Mod(1,p)*1, b = X, tw = 2*X);
print("   n   x_n irred?   q_n = x_n^2 - D : factor degrees");
for(n = 1, 16,
  my(xn = if(n==1, X, 0));
  if(n > 1, my(u = Mod(1,p)*1, v = X); for(k = 2, n, my(w = tw*v - u); u = v; v = w); xn = v);
  my(fx = factor(xn), xirr = (#fx~ == 1 && fx[1,2] == 1));
  my(qn = xn^2 - D, fq = factor(qn), qdeg = vector(#fq~, i, poldegree(fq[i,1])));
  my(qirr = (#fq~ == 1 && fq[1,2] == 1));
  printf("  %2d   %-10s   %-6s %s\n", n, if(xirr,"YES","no"), if(qirr,"IRR","   "), qdeg);
);
}
print("");
print("=== the same divisibility over Z: x_n = T_n(X) at an integer X ===");
{
my(X = 3);   /* T_n(3): a genuine integer exponential sequence, eps = 3 + sqrt(8) */
print("   n   x_n = T_n(3)                     prime?   omega   n a power of 2?");
my(u = 1, v = X);
for(n = 1, 14,
  my(xn = if(n==1, X, 0));
  if(n > 1, my(a = 1, b = X); for(k = 2, n, my(c = 2*X*b - a); a = b; b = c); xn = b);
  my(isp = isprime(xn), w = omega(xn), pow2 = (n == 2^valuation(n,2)));
  printf("  %2d   %-30s  %-7s %5d   %s\n", n, xn, if(isp,"PRIME","no"), w, if(pow2,"yes","NO"));
);
}
quit;
