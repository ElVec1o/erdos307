\\ nearmiss_below_verify.gp -- independent exact re-check of the from-below witness (Rule 7).
\\
\\ Recomputes a and a' from the prime list alone, peels a', requires its small primes to be exactly
\\ {2,3,5} and its cofactor prime so sigma(a') is exact, and compares r to 1 as exact rationals.
\\
\\ Also checks the three identities that make this stratum the M = 30 case of prop:oneprime:
\\ a' = 30P, a'' = 31P + 30, and r = a''/a; and the side condition sigma(a) < 30/31 that every
\\ solution of that stratum must satisfy, since sigma(a) = 30P/(31P+30) = 30/31 - 900/(31a).
\\
\\ No floating point enters any verdict. issquarefree and factor are avoided on the 121-digit values:
\\ a is squarefree by construction, a' needs only the peel plus one primality test.
\\
\\ Usage: gp -q -f nearmiss_below_verify.gp

S = [7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,431,68111,2792213];
{
my(a, ap, s, rem, small, P, sa, sap, r, app, T);
T = 30/31;
a  = prod(i=1,#S,S[i]);
ap = sum(i=1,#S, a/S[i]);
printf(" 1. entries prime and pairwise distinct : %d\n", #select(p->isprime(p),S)==#S && #Set(S)==#S);
printf(" 2. omega(a) = %d, squarefree by construction\n", #S);
printf(" 3. a has %d digits; barrier needs >113 : %d\n", #digits(a), a > 877*10^110);
printf(" 4. a' matches the reported value       : %d\n", ap == 837288885659892797916647449012132923898804294528776421078427486752518267800789540655989042643179360174669202127328403141870);
s = 0; rem = ap; small = List();
forprime(p = 2, 50000, if(rem % p == 0, listput(small,p); s += 1/p; rem /= p; if(rem % p == 0, error("a' not squarefree"))));
P = rem;
printf(" 5. small primes of a' are exactly {2,3,5} : %d\n", Vec(small)==[2,3,5]);
printf(" 6. cofactor P has %d digits and is prime  : %d\n", #digits(P), ispseudoprime(P));
printf(" 7. P matches the reported value        : %d\n", P == 27909629521996426597221581633737764129960143150959214035947582891750608926692984688532968088105978672488973404244280104729);
printf(" 8. a' = 30*P exactly                   : %d\n", ap == 30*P);
sa = sum(i=1,#S,1/S[i]); sap = s + 1/P; r = sa*sap; app = ap*sap;
printf(" 9. a'' = 31*P + 30 exactly             : %d\n", app == 31*P + 30);
printf("10. r = a''/a exactly                   : %d\n", r == app/a);
printf("11. sigma(a) < 30/31  (solution side)   : %d\n", sa < T);
printf("12. |r-1| = (31/30)|sigma(a)-30/31| ?   : %.12e vs %.12e\n", 1.0*abs(r-1), 1.0*(31/30)*(T-sa));
printf("13. |r - 1| = %.6e   (best from below before: 7.9220e-3)\n", 1.0*abs(r-1));
printf("14. gcd(a,a') = 1  (rigidity)           : %d\n", gcd(a,ap)==1);
printf("15. r < 1, so a'' < a                   : %d\n", r < 1 && app < a);
printf("16. r = 1 would need 30a - 31a' = 900; it is a %d-digit number\n", #digits(abs(30*a-31*ap)));
}
quit;
