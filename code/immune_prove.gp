\\ immune_prove.gp -- rigorous primality PROOFS for the level-60 immune families.
\\
\\ rem:campaign records 34 families in which A_S = N_S + 2 D_S and B_S = N_S - 2 D_S are both
\\ Baillie-PSW probable primes. BPSW is rigorous only in its COMPOSITE verdicts, so the immunity
\\ was labelled [C]. code/immune_certify.py showed the elementary route cannot close the gap:
\\ 0 of 34 reach the Brillhart-Lehmer-Selfridge threshold log F / log n > 1/3 after trial division
\\ to 1e6 and bounded Pollard rho. APR-CL does close it, and PARI's isprime() is a proof, not a
\\ probable-prime test (ispseudoprime() is the BPSW one).
\\
\\ Run:  gp -q -f immune_prove.gp
default(parisize, 800000000);
P    = primes([2,800]);
T58  = sum(i=1, 58, 1/P[i]);
forc = select(x -> x <= 167, P);
pool = select(x -> x > 167 && T58 + 1/x > 2, P);
np   = #pool;
kk   = 59 - #forc;
thr  = 2 - sum(i=1, #forc, 1/forc[i]);
pf   = vector(np, i, 1/pool[i]);
cum  = vector(np+1); cum[1] = 0;
for(i=1, np, cum[i+1] = cum[i] + pf[i]);
printf("forced %d, pool %d, choose %d, threshold %s\n", #forc, np, kk, thr);

bases = List();
dfs(i, need, cur, chosen) = {
  if(need == 0, if(cur > thr, listput(bases, chosen)); return());
  if(i + need > np + 1, return());
  if(cur + (cum[min(i+need, np+1)] - cum[i]) <= thr, return());
  dfs(i+1, need-1, cur + pf[i], concat(chosen, [i]));
  dfs(i+1, need,   cur,          chosen);
};
dfs(1, kk, 0, []);
printf("admissible bases: %d   (expected 49961)\n", #bases);

\\ find the immune ones: A_S and B_S both BPSW probable primes
\\ NOTE: gp needs braces around any multi-line statement in a script file.
imm = List(); jkill = 0;
{
for(j=1, #bases,
  S = concat(forc, vector(#bases[j], t, pool[bases[j][t]]));
  D = prod(t=1, #S, S[t]);
  N = sum(t=1, #S, D \ S[t]);
  A = N + 2*D; B = N - 2*D;
  if(ispseudoprime(A) && ispseudoprime(B), listput(imm, [S, A, B, kronecker(D, A), kronecker(D, B)]));
  if(kronecker(D, A) == -1, jkill++);
);
}
printf("Jacobi certificate (D_S|A_S) = -1 kills: %d   (paper: 31219)\n", jkill);
printf("both A_S and B_S BPSW-prime: %d\n", #imm);
nimm = 0; for(j=1, #imm, if(imm[j][4] == 1, nimm++));
printf("of those, IMMUNE ((D_S|A_S) = +1): %d   (paper: 34)\n\n", nimm);

\\ upgrade [C] -> [P] with APR-CL proofs

ok = 0; okimm = 0;
{
for(j=1, #imm,
  A = imm[j][2]; B = imm[j][3];
  t0 = getabstime();
  pa = isprime(A); pb = isprime(B);
  t1 = getabstime();
  if(pa && pb, ok++; if(imm[j][4] == 1, okimm++));
);
}
printf("APR-CL PROVEN prime pairs: %d of %d\n", ok, #imm);
printf("APR-CL PROVEN among the IMMUNE ones: %d of %d\n", okimm, nimm);
{ if(okimm == nimm && nimm > 0,
  printf("\n=> all %d immune families upgrade [C] -> [P]. Their immunity is UNCONDITIONAL.\n", nimm)); }
quit;
