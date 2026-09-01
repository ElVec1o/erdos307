\\ |P u Q| >= 1 + K  where  PS[K] >= sigma(d) + 1/sigma(d).  Since s + 1/s >= 2 with equality only
\\ at s = 1, a sector is "cheap" precisely when sigma(d) is close to 1.  Invert: for the bound to be
\\ at most B we need s + 1/s <= PS[B-1], i.e. sigma(d) in an explicit window about 1.
{
my(PS, tot, p, np, M, lo, hi, B);
np = 0; tot = 0.0; PS = List();
forprime(p = 2, 10^6, tot += 1.0/p; listput(PS, tot); np += 1);
print("  bound B   PS[B-1]     admissible window for sigma(d)");
foreach([60, 61, 62, 64, 66, 69, 70, 80, 100, 200], B,
  M = PS[B-1];
  lo = (M - sqrt(M^2 - 4))/2; hi = (M + sqrt(M^2 - 4))/2;
  printf("  %5d     %.7f   [%.6f , %.6f]   width %.6f\n", B, M, lo, hi, hi-lo));
print("");
print("So: EVERY sector with sigma(d) outside [0.913, 1.095] already forces |P u Q| >= 70.");
print("The whole d > 2 problem lives in a narrow window of sigma(d) around 1.");
}
quit;
