{
my(N, r, s, worst, llN);
N = 10^7; llN = log(log(N));
print("3. worst real non-principal |sum_{p<=N} psi(p)/p| at small moduli, vs loglog N = ", llN);
foreach([15, 21, 33, 35, 77, 143], r,
  worst = 0.0;
  fordiv(r, d,
    if(d == 1, next);
    my(t); t = 0.0;
    forprime(p = 2, N, if(p % r != 0 && kronecker(d, p) != 0, t += kronecker(d, p)*1.0/p));
    if(abs(t) > worst, worst = abs(t)));
  printf("  r=%4d  worst = %.4f   ratio to loglog N = %.3f\n", r, worst, worst/llN));
print("");
print("4. the assembled distance bound: M/loglogN >= 1 - sqrt(r)/phi(r) - (nonprincipal)/loglogN");
foreach([15, 77, 143], r,
  printf("  r=%4d  1 - sqrt(r)/phi(r) = %.4f\n", r, 1 - sqrt(r)/eulerphi(r)));
}
quit;
