{
my(S, D, N, sig, bad, tot, c1, c2, b);
print("DICHOTOMY (corrected): q = max U, S = U \\ {q}, D = prod S, N = D(S), sigma = N/D");
print("  case 1 (sigma < 2): mass forces  q <= D/(2D - N) = 1/(2 - sigma)");
print("  case 2 (sigma >= 2): prop:tailbound gives q <= (N + sqrt(N^2 - 4D^2 + 4D))/2");
print("");
bad = 0; tot = 0; c1 = 0; c2 = 0;
for(trial = 1, 400,
  S = List(); forprime(p = 2, 300, if(random(100) < 92, listput(S, p)));
  if(#S < 40, next);
  S = Vec(S);
  D = prod(i=1,#S,S[i]); N = sum(i=1,#S, D/S[i]); sig = 1.0*N/D;
  tot++;
  if(sig < 2, c1++; b = 1.0*D/(2*D - N); if(b <= 0, bad++),
              c2++; if(N^2 - 4*D^2 + 4*D < 0, bad++)));
print("bases tested: ", tot, "   case1: ", c1, "   case2: ", c2, "   failures: ", bad);
print("");
print("=== cross-check against Sixty.lean's independently proved bound ===");
S = List(); forprime(p = 2, 271, listput(S, p)); S = Vec(S);
D = prod(i=1,#S,S[i]); N = sum(i=1,#S, D/S[i]);
printf("58-prime base, sigma = %.6f < 2  ->  q <= D/(2D-N) = %.3f\n", 1.0*N/D, 1.0*D/(2*D-N));
print("Sixty.lean proves independently: every element of a 59-element support is <= 795.");
print("");
print("=== level 61: the two regimes, concretely ===");
S = List(); forprime(p = 2, 283, listput(S, p)); S = Vec(S);
D = prod(i=1,#S,S[i]); N = sum(i=1,#S, D/S[i]);
printf("S = first 61 primes: sigma = %.6f >= 2, so case 2\n", 1.0*N/D);
printf("  log10 D = %.2f   q <= %.4f * D  (log10 = %.2f)\n",
  log(D*1.0)/log(10), ((N + sqrt(N^2*1.0-4*D^2+4*D))/2.0)/(D*1.0),
  log(((N + sqrt(N^2*1.0-4*D^2+4*D))/2.0))/log(10));
S = List(); forprime(p = 2, 281, listput(S, p)); S = Vec(S);
D = prod(i=1,#S,S[i]); N = sum(i=1,#S, D/S[i]);
printf("S = first 60 primes: sigma = %.6f >= 2, so case 2\n", 1.0*N/D);
printf("  q <= %.4f * D  (log10 = %.2f)\n", ((N + sqrt(N^2*1.0-4*D^2+4*D))/2.0)/(D*1.0),
  log(((N + sqrt(N^2*1.0-4*D^2+4*D))/2.0))/log(10));
}
quit;
