\\ a10_fieldbarrier.gp -- BLOCK 2 attack: is the barrier an artefact of Q?
\\
\\ thm:ffnocycle killed the algebraic route by showing the analogue is FALSE over K[t], the
\\ mechanism being ultrametricity: |sigma(f)| = max |1/pi| < 1 always. Over a number ring O_K the
\\ absolute value IS archimedean, so that obstruction vanishes and #307's analogue is open there
\\ rather than false. The natural hope: a field with many small-norm primes reaches mass 2 more
\\ cheaply, collapsing the 1e112.9 barrier and putting solutions in SEARCH range.
\\
\\ This measures it. The barrier is min prod N(pi) over prime ideals with sum 1/N(pi) >= 2. In a
\\ degree-d field a rational prime splitting completely gives d primes each of NORM p, so mass d/p
\\ at log-cost d log p -- the same mass-per-log-norm as Q. Inert primes are strictly worse: norm
\\ p^d for mass 1/p^d. So no field can beat Q, and some are much worse.
default(realprecision, 40);
l10 = log(10.0);
\\ Q: greedy over rational primes
{
mass = 0.0; lg = 0.0; k = 0; p = 2;
while(mass < 2, mass += 1.0/p; lg += log(p*1.0); k++; p = nextprime(p+1));
printf("Q            : %2d primes, log10(prod N) = %.1f\n", k, lg/l10);
}
\\ imaginary quadratic Q(i): p = 1 mod 4 splits into TWO primes of norm p; p = 3 mod 4 is inert, norm p^2
{
mass = 0.0; lg = 0.0; k = 0; p = 2;
while(mass < 2,
  if(p == 2, mass += 1.0/2; lg += log(2.0); k++,
    if(p % 4 == 1, mass += 2.0/p; lg += 2*log(p*1.0); k += 2,
                   mass += 1.0/(p*p*1.0); lg += 2*log(p*1.0); k++));
  p = nextprime(p+1));
printf("Q(i)         : %2d primes, log10(prod N) = %.1f\n", k, lg/l10);
}
\\ a degree-d field in which EVERY rational prime splits completely (the most favourable case
\\ possible; it does not exist for d > 1 but bounds what any field could achieve)
{
for(d = 2, 4,
  mass = 0.0; lg = 0.0; k = 0; p = 2;
  while(mass < 2, mass += d*1.0/p; lg += d*log(p*1.0); k += d; p = nextprime(p+1));
  printf("split-all d=%d: %2d primes, log10(prod N) = %.1f   <-- unattainable ideal case\n", d, k, lg/l10);
);
}
printf("\n  CORRECTION to the naive argument. Mass per log-norm IS 1/(p log p) in every case, but\n");
printf("  that is not what the barrier measures: doubling the mass per rational prime lets you STOP\n");
printf("  at a far smaller prime, and since sum 1/p diverges only like loglog, halving the required\n");
printf("  sum from 2 to 1 cuts the primorial from e^p_59 to e^p_3. The split-all rows show the gain\n");
printf("  would be enormous IF attainable.\n");
printf("  It is not. By Chebotarev, primes split completely with density only 1/d in a degree-d\n");
printf("  Galois field, so the split primes carry mass d * (1/d) loglog Y = loglog Y, the SAME as Q,\n");
printf("  while each costs d log p instead of log p. Inert primes contribute 1/p^d, i.e. nothing.\n");
printf("  Hence every number field is WORSE than Q, and Q is optimal: measured, Q(i) needs 226\n");
printf("  primes and 10^735.1 against Q's 59 and 10^112.9.\n");
quit;
