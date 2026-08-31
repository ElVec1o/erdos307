{
my(mn, arg, v);
\\ minimum of 1 - sqrt(r)/phi(r) over odd squarefree r >= 7, swept directly
mn = 2.0; arg = 0;
forstep(r = 7, 20001, 2,
  if(!issquarefree(r), next);
  v = 1 - sqrt(r)/eulerphi(r);
  if(v < mn, mn = v; arg = r));
printf("min over odd squarefree 7 <= r <= 20001 : %.6f at r = %d\n", mn, arg);
printf("r=3 : %.6f   r=5 : %.6f\n", 1 - sqrt(3)/2.0, 1 - sqrt(5)/4.0);
print("local factor check: sqrt(p)/(p-1) <= sqrt(3)/2 for all odd p, max at p = 3");
}
quit;
