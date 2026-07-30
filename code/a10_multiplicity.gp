\\ a10_multiplicity.gp -- can the 49,961 recurrences be played against each other?
\\
\\ The hope: a lower bound for "some term of SOME sequence is prime" is formally weaker than for
\\ any single sequence, so a large family might be reachable where one sequence is not. This
\\ measures whether the family is large enough for any sieve lower bound to apply.
\\
\\ Every known lower-bound method (Chen-type, Selberg, Harman) needs the candidate set to have
\\ counting function at least X^theta for some FIXED theta > 0. The union of the family's terms
\\ below X has counting function (#bases) * log X / log(eps), because each sequence grows
\\ exponentially and so contributes only O(log X) terms.
default(realprecision, 40);
nb   = 49961;                \\ admissible bases at level 60 (prop:close59, reproduced)
X    = 10^500;               \\ scale of the objects: q_n has ~500+ digits on an immune base
lX   = log(X*1.0);
eps  = log(10^224*1.0);      \\ fundamental unit, 224 digits (rem:lehmer)
terms_per_seq = lX/eps;
union = nb * terms_per_seq;
printf("family size (level 60)           : %d = 10^%.1f\n", nb, log(nb*1.0)/log(10));
printf("terms per sequence below X=10^500: %.1f\n", terms_per_seq);
printf("UNION of all terms below X       : %.1f  (i.e. 10^%.2f)\n", union, log(union)/log(10));
printf("density exponent log(union)/log X: %.4f\n", log(union)/lX);
printf("\nfor a sieve lower bound you need the union to be X^theta with theta FIXED > 0.\n");
printf("union = C * log X, so log(union)/log X = log(C log X)/log X -> 0 as X grows.\n");
printf("the CONSTANT C is irrelevant: it is inside a logarithm.\n");
printf("\nhow big would the family have to be, for theta = 1/2 at X = 10^500?\n");
need = sqrt(X*1.0)/terms_per_seq;
printf("  needed bases : 10^%.1f\n", log(need)/log(10));
printf("  we have      : 10^%.1f\n", log(nb*1.0)/log(10));
printf("  shortfall    : 10^%.1f\n", log(need/nb)/log(10));
printf("\nceiling on the family at ANY level, with support primes <= 800:\n");
npr = #primes([2,800]);
printf("  primes <= 800 : %d, so at most 2^%d = 10^%.1f subsets in total\n", npr, npr, npr*log(2.0)/log(10));
printf("  still short of the requirement by 10^%.1f\n", log(need)/log(10) - npr*log(2.0)/log(10));
quit;
