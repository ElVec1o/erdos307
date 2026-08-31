{
my(B, f, dB, D, q1, q2, found, tested, c, lim);
print("PERIOD-2 ORBITS of the port map.  Delta(qB) = q Delta - B, so appending q1 then q2:");
print("   Delta(q2 q1 B) = q1 q2 Delta - B(q1+q2).");
print("Returning to the same value requires   Delta (q1 q2 - 1) = B (q1 + q2),");
print("and since gcd(Delta,B) = 1 this forces  Delta | (q1 + q2).");
print("Solving:  q2 = (Delta + B q1) / (Delta q1 - B),  needing q1 > B/Delta.");
print("");
print("prop:portfixed rules out ONE-step self-sustaining values above 1. It says nothing");
print("about two-step orbits, which is where a family for u >= 2 could hide.");
print("");
found = 0; tested = 0;
forstep(Bt = 3, 200000, 2,
  if(!issquarefree(Bt), next);
  B = Bt;
  f = factor(B)[,1]~;
  dB = sum(i = 1, #f, B/f[i]);
  for(c = 1, 3,
    D = c*B - dB;
    if(D <= 1, next);            \\ we want Delta > 1
    tested++;
    \\ q1 ranges just above B/D; q2 shrinks toward B/D, so a short scan suffices
    lim = (B \ D) + 1;
    forprime(q1 = lim, lim + 4000,
      if(B % q1 == 0, next);
      my(num, den); den = D*q1 - B; if(den <= 0, next);
      num = D + B*q1;
      if(num % den != 0, next);
      q2 = num/den;
      if(q2 < 2 || !isprime(q2) || q2 == q1 || B % q2 == 0, next);
      found++;
      if(found <= 8,
        printf("  B=%-7d c=%d Delta=%-7d q1=%-9d q2=%-9d  (Delta | q1+q2 : %d)\n",
               B, c, D, q1, q2, (q1+q2) % D == 0)))));
print("");
print("states (B,c) with Delta > 1 tested: ", tested);
print("period-2 orbits found: ", found);
}
quit;
{
my(B, f, dB, D, q1, q2, found, tested, lim, oddfound);
print("TARGETED: c = 2 (our 1-free case), B odd squarefree, q1 and q2 both ODD primes.");
print("");
found = 0; oddfound = 0; tested = 0;
forstep(Bt = 3, 400000, 2,
  if(!issquarefree(Bt), next);
  B = Bt; f = factor(B)[,1]~;
  if(f[1] == 2, next);
  dB = sum(i = 1, #f, B/f[i]);
  D = 2*B - dB;
  if(D <= 1, next);
  tested++;
  lim = (B \ D) + 1;
  forprime(q1 = max(3, lim), lim + 3000,
    if(B % q1 == 0, next);
    my(num, den); den = D*q1 - B; if(den <= 0, next);
    num = D + B*q1;
    if(num % den != 0, next);
    q2 = num/den;
    if(q2 < 3 || !isprime(q2) || q2 == q1 || B % q2 == 0, next);
    found++;
    if(q1 % 2 == 1 && q2 % 2 == 1, oddfound++;
      if(oddfound <= 6, printf("  ODD ORBIT: B=%d Delta=%d q1=%d q2=%d\n", B, D, q1, q2)))));
print("odd squarefree B with c=2, Delta>1 tested: ", tested);
print("period-2 orbits found: ", found, "   with both q odd: ", oddfound);
print("");
print("=== the real obstruction: even the PPN chain dies on primality ===");
print("Sylvester keeps Delta = 1 forever, so the VALUE dynamics never obstructs;");
print("what obstructs is that the required element must be PRIME:");
my(Bc); Bc = 1;
for(i = 1, 6,
  my(dd, q); dd = if(Bc == 1, 0, my(g); g = factor(Bc)[,1]~; sum(j=1,#g,Bc/g[j]));
  q = Bc - dd + Bc;   \\ = B/Delta + 1 with Delta = B - dd
  q = Bc \ (Bc - dd) + 1;
  printf("  B = %-10s next element B/Delta + 1 = %-10s prime? %s\n",
         Bc, q, if(isprime(q), "yes", concat("NO  = ", Str(factor(q)[,1]~))));
  if(!isprime(q), break);
  Bc = Bc * q);
}
quit;
