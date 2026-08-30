{
my(l, A, B, D, cnt, f, g, Sf, Sg, Sfg, T, bad, minslack, worst, tot);
print("checking the character-sum decomposition and the explicit bound");
print("");
bad = 0; tot = 0; minslack = 10^9;
forprime(l = 11, 200,
  for(t = 1, 10,
    D = 1 + random(l-1); B = 1 + random(l-1); A = (B + 4*D) % l;
    if(A % l == 0 || B % l == 0 || D % l == 0, next);
    Sf = 0; Sg = 0; Sfg = 0; cnt = 0;
    for(a = 1, l-1, for(b = 1, l-1,
      f = (A*a*b + D*(a+b)) % l; g = (B*a*b + D*(a+b)) % l;
      Sf += kronecker(f,l); Sg += kronecker(g,l); Sfg += kronecker(f*g,l);
      if(f != 0 && g != 0 && kronecker(f,l)==1 && kronecker(g,l)==1, cnt++)));
    T = (l-1)^2 + Sf + Sg + Sfg;
    tot++;
    \\ the claimed crude bounds
    if(abs(Sf) > 2*l || abs(Sg) > 2*l || abs(Sfg) > 3*l, bad++;
       if(bad < 4, print("  bound violated: l=",l," Sf=",Sf," Sg=",Sg," Sfg=",Sfg)));
    \\ and the resulting count bound
    my(lb); lb = ((l-1)^2 - 15*l)/4.0;
    if(l >= 19 && cnt < lb, print("  COUNT BOUND FAILS l=",l," cnt=",cnt," lb=",lb));
    if(l >= 19 && cnt - lb < minslack, minslack = cnt - lb; worst = [l,cnt,lb])
  ));
print("cases: ", tot, "   crude |S| bound violations: ", bad);
printf("tightest case (l>=19): l=%d count=%d lower bound=%.1f slack=%.1f\n",
       worst[1], worst[2], worst[3], minslack);
print("");
print("threshold where (l-1)^2 > 15 l : l >= ", ceil((17 + sqrt(17^2-4))/2));
}
quit;
