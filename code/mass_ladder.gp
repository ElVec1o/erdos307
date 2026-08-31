{
my(Tv, T, k, j, bad, tot, S, r, base, extra, pool, cand, mass, tries);
Tv = vector(70); T = 0.0; k = 0;
forprime(p = 2, 400, k++; T += 1.0/p; if(k <= 70, Tv[k] = T));
Tv = concat([0.0], Tv);
print("FALSIFICATION of the ladder  u_j <= (k-j+1)/(2 - sum_{i<j} 1/u_i)  for j <= 59.");
print("Generator: start from the first 59..66 primes (mass > 2), then swap a random subset");
print("of members for larger primes, keeping mass >= 2. This produces genuine supports.");
print("");
pool = List(); forprime(p = 2, 20000, listput(pool, p)); pool = Vec(pool);
bad = 0; tot = 0;
for(trial = 1, 20000,
  base = 59 + random(8);
  S = vector(base, i, pool[i]);
  \\ swap a few for larger primes
  for(swaps = 1, 1 + random(4),
    my(idx, newp); idx = 1 + random(base);
    newp = pool[base + 1 + random(300)];
    if(!vecsearch(vecsort(S), newp), S[idx] = newp));
  S = vecsort(S);
  mass = sum(i = 1, #S, 1.0/S[i]);
  if(mass < 2, next);
  tot++;
  k = #S;
  for(j = 1, min(59, k),
    r = 2 - sum(i = 1, j-1, 1.0/S[i]);
    if(r > 0 && S[j] > (k-j+1)/r + 1e-9,
      bad++;
      if(bad < 4, print("  VIOLATION k=", k, " j=", j, " u_j=", S[j], " bound=", (k-j+1)/r));
      break)));
print("genuine supports with mass >= 2 tested: ", tot);
print("ladder violations: ", bad);
print("");
print("=== also check the universal claim: u_59 <= (k-58)/(2-T_58) on the same sample ===");
bad = 0; tot = 0;
for(trial = 1, 20000,
  base = 59 + random(8);
  S = vector(base, i, pool[i]);
  for(swaps = 1, 1 + random(4),
    my(idx, newp); idx = 1 + random(base); newp = pool[base + 1 + random(300)];
    if(!vecsearch(vecsort(S), newp), S[idx] = newp));
  S = vecsort(S);
  if(sum(i=1,#S,1.0/S[i]) < 2, next);
  tot++; k = #S;
  if(k >= 59 && S[59] > (k-58)/(2 - Tv[59]) + 1e-9, bad++));
print("supports tested: ", tot, "   violations of u_59 <= (k-58)/(2-T_58): ", bad);
}
quit;
