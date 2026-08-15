\\ The ideal-theoretic #307: do disjoint finite sets P, Q of PRIME IDEALS exist with
\\ (sum_{pi in P} 1/N(pi)) * (sum_{rho in Q} 1/N(rho)) = 1 ?
\\ Over Q this is #307 and needs >= 59 primes. Over O_K several ideals SHARE a norm.
{
K = bnfinit(polcompositum(x^2-17, x^2-33)[1]);
dec = idealprimedec(K, 2);
printf("K = Q(sqrt17, sqrt33), degree %d\n", poldegree(K.pol));
printf("primes above 2: %d, norms %s\n", #dec, vector(#dec, j, idealnorm(K, dec[j])));
\\ are they pairwise distinct as ideals?
distinct = 1;
for(i = 1, #dec, for(j = i+1, #dec,
  if(idealnorm(K, idealadd(K, dec[i], dec[j])) == 1, , distinct = 0)));
printf("pairwise coprime (hence distinct): %d\n", distinct);
print();
print("Take P = {pi_1, pi_2}, Q = {pi_3, pi_4}, all of norm 2, all distinct:");
sP = 1/2 + 1/2; sQ = 1/2 + 1/2;
printf("  sigma(P) = %s,  sigma(Q) = %s,  product = %s\n", sP, sQ, sP*sQ);
printf("  |P u Q| = 4     <-- against >= 59 over Q\n");
print();
print("Does the DERIVATIVE transfer?  a = pi_1 pi_2, a' = a/pi_1 + a/pi_2 = pi_2 + pi_1 as ideals:");
s = idealadd(K, dec[1], dec[2]);
printf("  pi_1 + pi_2 = ideal of norm %d  (1 = the unit ideal, so the derivative collapses)\n", idealnorm(K, s));
}
quit
