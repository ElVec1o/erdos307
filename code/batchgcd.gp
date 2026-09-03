\\ batchgcd.gp -- is the level-60 residual splittable by shared structure?  All 49,961 bases share the
\\ 39 forced primes below 167, so two A_S might share a prime factor and split each other for free.
\\ This builds the residual (Jacobi certificate, then trial division to 1e6 -- deliberately weaker than
\\ the campaign of rem:campaign, so the result is a SUPERSET of the 3,478 and the count below is an
\\ upper bound), then runs a Bernstein batch GCD over the hard cofactors of A_S: one product tree, one
\\ remainder tree, every pair tested at once.  Answer: 2 of 6,972, both seven-digit.  Runtime ~7 min.
default(parisize, 8000000000);
P    = primes([2,800]);
forc = select(x -> x <= 167, P);
pool = select(x -> x > 167 && sum(i=1,58,1/P[i]) + 1/x > 2, P);
np = #pool; kk = 59 - #forc;
thr = 2 - sum(i=1, #forc, 1/forc[i]);
pf = vector(np, i, 1/pool[i]);
cum = vector(np+1); for(i=1, np, cum[i+1] = cum[i] + pf[i]);
bases = List();
dfs(i, need, cur, chosen) = {
  if(need == 0, if(cur > thr, listput(bases, chosen)); return());
  if(i + need > np + 1, return());
  if(cur + (cum[min(i+need, np+1)] - cum[i]) <= thr, return());
  dfs(i+1, need-1, cur + pf[i], concat(chosen, [i]));
  dfs(i+1, need,   cur,          chosen);
};
dfs(1, kk, 0, []);

\\ trial-division certificate
killed(W, D) = { my(fa = factor(W, 1000000), r);
  for(r = 1, #fa~, if(fa[r,1] <= 1000000 && kronecker(D, fa[r,1]) == -1, return(1)));
  0; }

RES = List(); t0 = getabstime();
{
for(j=1, #bases,
  S = concat(forc, vector(#bases[j], t, pool[bases[j][t]]));
  D = prod(t=1, #S, S[t]);
  N = sum(t=1, #S, D \ S[t]);
  A = N + 2*D; B = N - 2*D;
  if(kronecker(D, A) == -1, next);
  if(killed(A, D) || killed(B, D), next);
  listput(RES, [D, A, B]));
}
printf("true residual families: %d   (paper: 3478)   (%.0fs)\n", #RES, (getabstime()-t0)/1000.);

\\ hard cofactors of A_S over the residual, batch GCD against one another
V = List(); idx = List();
{ for(j=1, #RES, my(fa = factor(RES[j][2], 1000000), c = 1);
    for(r = 1, #fa~, if(fa[r,1] > 1000000, c *= fa[r,1]^fa[r,2]));
    if(c > 1 && !ispseudoprime(c), listput(V, c); listput(idx, j))); }
V = Vec(V); idx = Vec(idx); n = #V;
printf("hard composite A-cofactors in the residual: %d\n", n);
lev = List(); cur = V;
{ while(#cur > 1, listput(lev, cur);
    cur = vector((#cur + 1) \ 2, i, if(2*i <= #cur, cur[2*i-1] * cur[2*i], cur[2*i-1]))); }
R = [cur[1]];
{ forstep(d = #lev, 1, -1, my(below = lev[d], nx = vector(#below));
    for(i = 1, #below, nx[i] = R[(i+1)\2] % (below[i]^2)); R = nx); }
hits = List();
{ for(i = 1, n, my(g = gcd(R[i] \ V[i], V[i]));
    if(g > 1 && g < V[i], listput(hits, [idx[i], g]))); }
printf("residual families whose A_S splits by batch GCD: %d\n", #hits);
{ for(h = 1, #hits, printf("  family %d: %d-digit factor\n", hits[h][1], #Str(hits[h][2]))); }
if(#hits == 0, print("\nNEGATIVE: no two of the 3,478 residual A_S share a factor. Batch GCD buys nothing at the wall;\nthe residual really is a set of pairwise-coprime balanced semiprimes needing GNFS apiece."));
quit;
