\\ nearmiss_above_verify.gp -- independent exact re-check of the r > 1 witness (Rule 7).
\\
\\ Recomputes a and a' from the prime list alone, peels a' by trial division, confirms the cofactor
\\ is prime so that sigma(a') is EXACT rather than a lower bound, and compares r to 1 as exact
\\ rationals. No floating point enters any verdict; the one float is the printed |r-1|.
\\
\\ Deliberately avoids issquarefree() and factor() on the 118-digit values: a is squarefree by
\\ construction as a product of distinct primes, and a' needs only the peel plus a primality test on
\\ the cofactor. Calling factor() here does not terminate in reasonable time.
\\
\\ Usage: gp -q -f nearmiss_above_verify.gp
S = [7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,269,271,277,281,283,293,3301];
a  = prod(i=1,#S,S[i]);
ap = sum(i=1,#S, a/S[i]);
printf(" 1. entries prime and pairwise distinct : %d\n", #select(p->isprime(p),S)==#S && #Set(S)==#S);
printf(" 2. omega(a) = %d, a squarefree by construction\n", #S);
printf(" 3. a has %d digits; barrier needs >113 : %d\n", #digits(a), a > 877*10^110);
printf(" 4. a' = sum_p a/p matches the report   : %d\n", ap == 6046191046582015972998150740881239532301559880841543034317540567902031001933144639269971470174283520525305173872825070);
s = 0; rem = ap; sq = 1; np = 0;
forprime(p = 2, 200000, if(rem % p == 0, s += 1/p; np++; rem /= p; if(rem % p == 0, sq = 0; while(rem % p == 0, rem /= p))));
printf(" 5. a' peeled: %d small primes, squarefree there : %d\n", np, sq);
printf(" 6. cofactor %d digits, prime           : %d\n", #digits(rem), ispseudoprime(rem));
printf(" 7. cofactor matches the report         : %d\n", rem == 201539701552733865766605024696041317743385329361384767810584685596734366731104821308999049005809450684176839129094169);
sa = sum(i=1,#S,1/S[i]); sap = s + 1/rem; r = sa*sap;
printf(" 8. sigma(a)  = %s\n", sa);
printf(" 9. sigma(a') = %s\n", sap);
printf("10. r > 1, exact rational comparison    : %d\n", r > 1);
printf("11. r matches the reported exact value  : %d\n", r == 11176620300777727797432479008188337835500796440434575674647809040248238584372539285472219175635228928818393583187691/11165295962967513126751529802191216196327096909060466744953062847367144605415212361489449896410124443995416465805383);
printf("12. |r-1| = %.6e   (prev best: 7.922e-3 below, 3.944e-2 above)\n", abs(r-1)*1.0);
printf("13. gcd(a,a') = 1  (rigidity)           : %d\n", gcd(a,ap)==1);
app = ap*sap;
printf("14. a'' integral, a''/a == r exactly    : %d\n", denominator(app)==1 && app == r*a);
printf("15. a'' > a  (dynamically, r>1)         : %d\n", app > a);
printf("16. a'' has %d digits\n", #digits(app));
quit;
