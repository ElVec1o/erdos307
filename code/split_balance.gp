{
my(T, k, p, sS, t0, lo, hi, tot, out, S, m, s, tries);
print("SPLIT CONSTRAINT. thm:frame needs Delta = MN - M'N' > 0 for alpha = (MN'+N^2)/Delta > 0.");
print("But M'N' = MN sigma(P0) sigma(Q0), so Delta = D(1 - sigma(P0) sigma(Q0)):");
print("");
print("   Delta > 0  <=>  sigma(P0) sigma(Q0) < 1.");
print("");
print("With sigma(P0) + sigma(Q0) = sigma(S) FIXED, the product is a downward parabola, maximal at");
print("the midpoint. So the product is < 1 exactly OUTSIDE the roots of z^2 - sigma(S) z + 1 = 0,");
print("i.e. sigma(P0) must lie strictly OUTSIDE the mass window [1/t0, t0] of the base.");
print("");
sS = 0.0; k = 0;
forprime(p = 2, 277, k++; sS += 1.0/p);
t0 = (sS + sqrt(sS^2 - 4))/2;
printf("first 59 primes: sigma(S) = %.6f, window [1/t0, t0] = [%.6f, %.6f]\n", sS, 1/t0, t0);
printf("midpoint sigma(P0) = %.6f gives product %.6f > 1  -- FORBIDDEN\n", sS/2, (sS/2)^2);
print("");
print("So the balanced splits, which is where one would look first, are exactly the excluded ones.");
print("");
print("=== how many splits survive? (sampling, 2^59 is not enumerable) ===");
tot = 0; out = 0;
S = vector(59); k = 0; forprime(p = 2, 277, k++; S[k] = 1.0/p);
for(trial = 1, 2000000,
  s = 0.0;
  for(i = 1, 59, if(random(2) == 1, s += S[i]));
  tot++;
  if(s * (sS - s) < 1, out++));
printf("sampled %d splits: %d have sigma(P0)sigma(Q0) < 1  (%.3f%%)\n", tot, out, 100.0*out/tot);
printf("so of 2^59 = %.2e splits, about %.2e survive the sign condition\n", 2.0^59, 2.0^59*out/tot);
printf("times 49,961 supports: about %.2e candidate splits at level 61\n", 49961*2.0^59*out/tot);
}
quit;
