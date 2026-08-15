\\ tailsearch_plan.gp -- size the finite tail search of prop:tailbound, and emit its configs.
\\
\\ prop:tailbound: a Pythagorean tail prime satisfies q = 2(N +- k)/m^2 with k^2 = AB + D m^2 and
\\ m | 4D. So the tail set of a base is a FINITE search over the divisors of 4D. This script decides
\\ whether that search is runnable and, if so, writes what the searcher needs.
\\
\\ The full space is ~3*2^58 ~ 8.6e17 divisors per family, which is not enumerable. But the hit
\\ probability for a given m is ~ (AB + D m^2)^{-1/2} ~ 1/(m sqrt D) once D m^2 dominates, so the
\\ EXPECTED COUNT is dominated by small m and is proportional to sum_m 1/m restricted to the slice
\\ searched. Restricting to omega(m) <= K therefore costs almost nothing in expectation while
\\ collapsing the space. This script measures exactly that trade: for each K it reports the number
\\ of candidates and the fraction of sum_{m | 4D} 1/m covered.
\\
\\ Run:  gp -q -f tailsearch_plan.gp

default(parisize, 4000000000);

P    = primes([2,800]);
T58  = sum(i = 1, 58, 1/P[i]);
forc = select(x -> x <= 167, P);
pool = select(x -> x > 167 && T58 + 1/x > 2, P);
np   = #pool;
kk   = 59 - #forc;
thr  = 2 - sum(i = 1, #forc, 1/forc[i]);
pf   = vector(np, i, 1/pool[i]);
cum  = vector(np+1); cum[1] = 0;
for(i = 1, np, cum[i+1] = cum[i] + pf[i]);
bases = List();
dfs(i, need, cur, ch) =
{
  if(need == 0, if(cur > thr, listput(bases, ch)); return());
  if(i + need > np + 1, return());
  if(cur + (cum[min(i+need, np+1)] - cum[i]) <= thr, return());
  dfs(i+1, need-1, cur + pf[i], concat(ch, [i]));
  dfs(i+1, need, cur, ch);
}
dfs(1, kk, 0, []);

imm = List();
{
my(S, D, N, A, B);
for(j = 1, #bases,
  S = concat(forc, vector(#bases[j], t, pool[bases[j][t]]));
  D = prod(t = 1, #S, S[t]);
  N = sum(t = 1, #S, D \ S[t]);
  A = N + 2*D; B = N - 2*D;
  if(ispseudoprime(A) && ispseudoprime(B) && kronecker(D, A) == 1, listput(imm, [D, A, B, S])));
}
printf("immune families: %d\n\n", #imm);

\\ ---- elementary symmetric sums of {1/p : p in S}, to split sum 1/m by omega(m) ----
\\ e[j+1] = sum over subsets T of S with |T| = j of prod_{p in T} 1/p
esym(S) =
{
  my(n = #S, e = vector(n+1));
  e[1] = 1.0;
  for(i = 1, n,
    forstep(j = i, 1, -1, e[j+1] = e[j+1] + e[j] / S[i]));
  e;
}

print("slice sizing on the first immune base (all 34 have the same shape):");
print("      K    candidates m     fraction of sum_{m|4D} 1/m covered");
{
my(S = imm[1][4], e, tot, run, cand, nb);
e = esym(S);
tot = sum(j = 1, #S + 1, e[j]) * (1 + 1/2. + 1/4.);
run = 0.0; cand = 0; nb = #S;
for(K = 0, 12,
  run += e[K+1];
  cand += binomial(nb, K);
  printf("    %3d  %14.0f     %.9f\n", K, 3.0*cand, run * 1.75 / tot));
printf("\n    full space: 3 * 2^%d = %.4e\n", nb, 3.0 * 2^nb);
}

\\ ---- emit configs for the Rust searcher ----
\\ One line per family:  D  N  A  B  p1 p2 ... p59
{
my(f = "tailsearch_cfg.txt", S, D, N, A, B, s);
write(f, "# D N A B p1..p59   -- prop:tailbound tail search, one immune family per line");
for(j = 1, #imm,
  D = imm[j][1]; A = imm[j][2]; B = imm[j][3]; S = imm[j][4]; N = A - 2*D;
  s = Str(D, " ", N, " ", A, " ", B);
  for(t = 1, #S, s = Str(s, " ", S[t]));
  write(f, s));
printf("wrote %s: %d families\n", f, #imm);
}

print("");
print("done.");
