{
my(found, u, v, c1, D);
\\ Validate the epsilon-dichotomy bounds on the c1=1 problem (1 + rsum A)(rsum B) = 1,
\\ whose solutions are known: Cambie's examples. Enumerate |A|=1, |B|<=4, elements >= 2.
print("solutions of (1 + 1/a)(1/b1+...+1/bk) = 1, a >= 2, 2 <= b1 < ... <= 200, k <= 4:");
found = 0;
for(b1 = 2, 200, for(b2 = b1+1, 200, my(s2); s2 = 1/b1 + 1/b2;
  if(s2 < 1 && denominator(1/(1-s2)) == 1 && 1/(1-s2) - 1 >= 2,
    \\ (1+1/a) s = 1 -> a = s/(1-s); require integer >= 2
    my(a); a = s2/(1-s2);
    if(denominator(a) == 1 && a >= 2, found++; print("  A={",a,"}  B={",b1,",",b2,"}")));
  for(b3 = b2+1, 200, my(s3); s3 = s2 + 1/b3;
    if(s3 >= 1, next);
    my(a); a = s3/(1-s3);
    if(denominator(a) == 1 && a >= 2, found++; print("  A={",a,"}  B={",b1,",",b2,",",b3,"}"));
    for(b4 = b3+1, 200, my(s4); s4 = s3 + 1/b4;
      if(s4 >= 1, next);
      my(a); a = s4/(1-s4);
      if(denominator(a) == 1 && a >= 2, found++;
        print("  A={",a,"}  B={",b1,",",b2,",",b3,",",b4,"}"))))));
print("total: ", found);
print("");
print("dichotomy check on each: epsilon = 1 - c1 c2 = 1; case A bound D_A = 2 c1 n / eps = 2n");
print("  every solution must have some b <= 2n  OR some a <= m(2 c2 + n) = n");
}
quit;
