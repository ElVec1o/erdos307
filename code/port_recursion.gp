{
my(B, c, D, dB, bad, tot, q, f, fixed);
print("PORT RECURSION. B squarefree, d = arithmetic derivative, Delta_c(B) = cB - d(B).");
print("Appending a prime q not dividing B:  Delta_c(qB) = q Delta_c(B) - B.");
print("");
print("CLAIM 1: gcd(Delta_c(B), B) = 1 for every squarefree B and every c.");
bad = 0; tot = 0;
for(t = 1, 4000,
  B = 1; f = List();
  forprime(p = 2, 200, if(random(100) < 12, B *= p; listput(f, p)));
  if(#f < 1, next);
  dB = sum(i = 1, #f, B/f[i]);
  for(c = 1, 6, D = c*B - dB; tot++; if(gcd(abs(D), B) != 1, bad++)));
print("  tested ", tot, " pairs (B,c): gcd failures ", bad);
print("");
print("CLAIM 2 (the recursion): Delta_c(qB) = q Delta_c(B) - B.");
bad = 0; tot = 0;
for(t = 1, 3000,
  B = 1; f = List();
  forprime(p = 2, 120, if(random(100) < 15, B *= p; listput(f, p)));
  if(#f < 1, next);
  dB = sum(i = 1, #f, B/f[i]);
  q = nextprime(200 + random(500)); if(B % q == 0, next);
  my(B2, d2); B2 = q*B; d2 = B + q*dB;
  for(c = 1, 5, tot++;
    if(c*B2 - d2 != q*(c*B - dB) - B, bad++)));
print("  tested ", tot, ": recursion failures ", bad);
print("");
print("CLAIM 3: the only SELF-SUSTAINING value is 1.");
print("  Delta(qB) = Delta(B)  <=>  Delta(B)(q-1) = B  =>  Delta(B) | B  =>  Delta(B) = 1 by claim 1.");
print("  So the only fixed point is Delta = 1, attained by q = B + 1.");
fixed = 0; bad = 0;
for(t = 1, 3000,
  B = 1; f = List();
  forprime(p = 2, 120, if(random(100) < 15, B *= p; listput(f, p)));
  if(#f < 1, next);
  dB = sum(i = 1, #f, B/f[i]);
  for(c = 1, 5, D = c*B - dB;
    if(D <= 0, next);
    \\ search a prime q with Delta(qB) = Delta(B)
    forprime(q = 2, 5000,
      if(B % q == 0, next);
      if(q*D - B == D, fixed++;
        if(D != 1, bad++; print("   SELF-SUSTAINING WITH D != 1: ", D))))));
print("  self-sustaining steps found: ", fixed, "   with Delta != 1: ", bad);
print("");
print("=== consequence: Sylvester maintains Delta=1, so #313 has a family; u>=2 has none ===");
B = 1; print("  Sylvester chain, c = 1:");
for(i = 1, 5,
  my(dd); dd = if(B == 1, 0, my(g); g = factor(B)[,1]~; sum(j=1,#g,B/g[j]));
  D = 1*B - dd;
  printf("    B = %-12s Delta = %d   next q = B/Delta + 1 = %d\n", B, D, B/D + 1);
  B = B * (B/D + 1));
}
quit;
