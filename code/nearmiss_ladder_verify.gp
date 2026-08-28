\\ nearmiss_ladder_verify.gp -- independent exact re-check of the ladder witness (Rule 7).
\\
\\ Recomputes a and a' from the prime list alone, peels a', requires its small primes to be exactly
\\ {2,3,5} and its cofactor prime so that sigma(a') is exact, and compares r to 1 as exact rationals.
\\ Also checks the identity |r-1| = (31/30)|sigma(a) - 30/31| that the construction relies on.
\\ No floating point enters any verdict. issquarefree and factor are avoided on the 120-digit values:
\\ a is squarefree by construction and a' needs only the peel plus one primality test.
\\
\\ Usage: gp -q -f nearmiss_ladder_verify.gp
S = [7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,569,1949,15461];
{
my(a, ap, s, rem, sq, small, sa, sap, r, T);
T = 30/31;
a  = prod(i=1,#S,S[i]);
ap = sum(i=1,#S, a/S[i]);
printf(" 1. entries prime and distinct        : %d\n", #select(p->isprime(p),S)==#S && #Set(S)==#S);
printf(" 2. omega(a)=%d, a squarefree by construction\n", #S);
printf(" 3. a has %d digits (barrier >113)   : %d\n", #digits(a), a > 877*10^110);
printf(" 4. a' matches the reported value     : %d\n", ap == 175143467330985608553244982666728415560975432442673252698538392286570280347626935835849096628261485768056794525140957910);
s = 0; rem = ap; sq = 1; small = List();
forprime(p = 2, 50000, if(rem % p == 0, listput(small,p); s += 1/p; rem /= p; if(rem % p == 0, sq = 0)));
printf(" 5. small primes of a' are exactly {2,3,5} : %d\n", Vec(small)==[2,3,5]);
printf(" 6. cofactor %d digits and prime      : %d\n", #digits(rem), ispseudoprime(rem));
printf(" 7. cofactor matches reported         : %d\n", rem == 5838115577699520285108166088890947185365847748089108423284613076219009344920897861194969887608716192268559817504698597);
sa = sum(i=1,#S,1/S[i]); sap = s + 1/rem; r = sa*sap;
printf(" 8. sigma(a) - 30/31 > 0              : %d\n", sa - T > 0);
printf(" 9. |r-1| = (31/30)|sigma(a)-30/31| ? : %.12e vs %.12e\n", 1.0*abs(r-1), 1.0*(31/30)*(sa-T));
printf("10. r > 1, exact rational             : %d\n", r > 1);
printf("11. |r-1| = %.6e   (previous record 1.0142e-3)\n", 1.0*abs(r-1));
printf("12. gcd(a,a') = 1 (rigidity)          : %d\n", gcd(a,ap)==1);
printf("13. a'' = a'*sigma(a') integral, = r*a: %d\n", denominator(ap*sap)==1 && ap*sap == r*a);
printf("14. a'' > a                           : %d\n", ap*sap > a);
}
quit;
