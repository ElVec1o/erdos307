{
my(bad1, bad2, S, chi, l, a, b, c, d, n);
bad1 = 0; bad2 = 0; n = 0;
forprime(l = 3, 60,
  for(a = 1, l-1, for(b = 0, l-1,
    S = sum(q = 0, l-1, kronecker(a*q + b, l));
    if(S != 0, bad1++)));
  for(a = 1, l-1, for(c = 1, l-1, for(b = 0, l-1, for(d = 0, l-1,
    if((a*d - b*c) % l == 0, next);
    S = sum(q = 0, l-1, kronecker((a*q+b)*(c*q+d), l));
    n++;
    if(S != -kronecker(a*c, l), bad2++)))))
);
print("linear sum  sum_q chi(aq+b) = 0      : violations ", bad1);
print("quadratic sum = -chi(ac), ad != bc   : ", n, " cases, violations ", bad2);
}
quit;
