\\ nearmiss_below.gp -- the same ladder aimed at the side where solutions can actually live.
\\
\\
\\ WHY THE SIDE MATTERS. This near-miss family always produces a' = 2*3*5*P with P prime, which is
\\ exactly the M = 30 stratum of prop:oneprime: with M = 30, M' = 31, the equation MN - M'N' = M^2
\\ reads 30N - 31N' = 900, and N = M + M'p = 30 + 31P, N' = 30P. So a solution of #307 inside this
\\ family is precisely a = 31P + 30 with a' = 30P, whence
\\
\\      sigma(a) = 30P/(31P + 30) < 30/31   STRICTLY, and sigma(a) = 30/31 - 900/(31a).
\\
\\ Every solution of this stratum therefore sits BELOW 30/31. Records approaching 30/31 from above,
\\ including the 6.2787e-9 of v1.6.1 and the 3.7617e-9 of the wider sweep, lie on a side of the
\\ target that this stratum cannot populate. They remain valid as spectrum records for r and are
\\ reported as such, but they cannot converge on a solution.
\\
\\ This script aims below instead: every rung undershoots, including the last, so sigma(a) stays
\\ under 30/31 and the residual deficit is what |r-1| measures, at 31/30 times it.
\\
\\ In every EXACT witness this construction produces, a' = 2*3*5*P with P a large prime, so
\\ sigma(a') = 31/30 + 1/P with 1/P around 1e-117, and therefore
\\
\\      |r(a) - 1| = (31/30) * |sigma(a) - 30/31|.
\\
\\ Checked against the v1.6.0 witness: sigma(a) - 30/31 = 9.815267e-4, times 31/30 is 1.014244e-3,
\\ which is |r-1| to every printed digit. So the near-miss problem is not about a' at all. It is the
\\ Diophantine question of how closely a sum of distinct prime reciprocals approaches 30/31 from
\\ above, and |r-1| is 31/30 times that error.
\\
\\ Three designs, two of which fail; the failures are recorded because each is instructive.
\\
\\   (a) nearmiss_above.gp adjusts with a single prime drawn from [X+1, 4000]. Granularity 2.5e-4,
\\       floor near 1e-3.
\\
\\   (b) Close a coarse deficit d with one prime near 1/d. Fails: 1/d lands INSIDE the pool, where
\\       every prime is already used. Forcing the closing prime above X then narrows the admissible
\\       removal mass so much that only removals of size 1 and 2 fit, and the candidate supply
\\       collapses. Measured: 15 CRT-admissible candidates, 0 exact, with a smallest available
\\       overshoot of 1.186e-10 that nothing could reach.
\\
\\   (c) A ladder. Intermediate stages must UNDERSHOOT and only the last may overshoot. Using
\\       precprime at every stage, as (b) did, drives d1 negative immediately and generates nothing.
\\       With nextprime for the intermediate stages and precprime for the last:
\\
\\           d  = 30/31 - sigma(pool),   p1 = nextprime(1/d),   d1 = d - 1/p1,
\\           p2 = nextprime(1/d1),       d2 = d1 - 1/p2,        p3 = precprime(1/d2),
\\           overshoot = 1/p3 - d2  ~  gap(p3)/p3^2.
\\
\\       Each stage roughly squares the precision. For pool = primes in [7,271] this reaches
\\       5.2e-18, some 14 orders below the previous record.
\\
\\ Only pool = [7,271] is usable: for smaller X the first rung 1/d falls below X and the prime is
\\ already in the pool, and for larger X the deficit is negative. The candidate supply needed by the
\\ CRT filter (1 in 30) and the exactness filter (a' = 2*3*5*P, roughly 1 in log a') therefore comes
\\ from sweeping several choices at rungs 1 and 2 rather than from several pools.
\\
\\ Usage: gp -q -f nearmiss_below.gp

default(parisize, 6000000000);
TARGET  = 30/31;
TRIAL   = 50000;
MAXPEEL = 40000;
XBASE   = 271;
W1 = 420;
W2 = 420;

mass(v) = sum(i = 1, #v, 1/v[i]);
dsum(v) = my(N = prod(i = 1, #v, v[i])); sum(i = 1, #v, N / v[i]);
crtsum(v) =
{
  my(s2 = sum(i=1,#v,Mod(v[i],2)^(-1)), s3 = sum(i=1,#v,Mod(v[i],3)^(-1)),
     s5 = sum(i=1,#v,Mod(v[i],5)^(-1)));
  lift(chinese(chinese(s2, s3), s5));
}
peel235(m) =
{
  my(rem = m, small = List());
  forprime(p = 2, TRIAL,
    if(rem % p == 0,
      listput(small, p); rem /= p;
      if(rem % p == 0, return([0, 0]))));
  if(Vec(small) != [2, 3, 5], return([0, 0]));
  if(!ispseudoprime(rem), return([0, 0]));
  [1, rem];
}

POOL  = primes([7, XBASE]);
SFULL = mass(POOL);
CANDS = List();

{
my(d, p1, d1, p2, d2, p3, err, keep, gen, cv, best, bestrec, peels, exact);
d = TARGET - SFULL;
printf("pool = primes in [7,%d], %d primes; deficit d = %.6e\n", XBASE, #POOL, 1.0*d);
printf("aiming from BELOW 30/31, the side prop:oneprime allows at M = 30\n\n");
gen = 0;
p1 = nextprime(ceil(1/d));
for(a1 = 1, W1,
  d1 = d - 1/p1;
  if(d1 > 0 && p1 > XBASE,
    p2 = nextprime(ceil(1/d1));
    for(a2 = 1, W2,
      d2 = d1 - 1/p2;
      if(d2 > 0 && p2 > XBASE && p2 != p1,
        p3 = nextprime(ceil(1/d2));
        if(p3 > XBASE && p3 != p1 && p3 != p2,
          err = d2 - 1/p3;
          if(err > 0,
            gen++;
            keep = concat(POOL, [p1, p2, p3]);
            if(crtsum(keep) == 0, listput(CANDS, [err, keep])))));
      p2 = nextprime(p2 + 1)));
  p1 = nextprime(p1 + 1));
printf("ladders generated: %d ; CRT-admissible: %d\n", gen, #CANDS);
if(#CANDS == 0, print("none"); quit);
cv = vecsort(Vec(CANDS), 1);
printf("smallest residual deficit available: %.6e\n\n", 1.0*cv[1][1]);
best = 2; bestrec = 0; peels = 0; exact = 0;
for(ci = 1, #cv,
  if(peels >= MAXPEEL, break);
  my(kp, ap, pl, sa, r);
  kp = cv[ci][2];
  ap = dsum(kp);
  peels++;
  pl = peel235(ap);
  if(pl[1] == 0, next);
  exact++;
  sa = mass(kp);
  r = sa * (31/30 + 1/pl[2]);
  if(abs(r - 1) < best,
    best = abs(r - 1); bestrec = [kp, ap, pl[2], sa, r];
    printf("  new best after %d peels: dig(a)=%d  |r-1| = %.6e\n",
           peels, #digits(prod(t=1,#kp,kp[t])), 1.0*best)));
printf("\npeels attempted: %d ; exact (a' = 2*3*5*P): %d\n", peels, exact);
if(bestrec == 0, print("no exact witness found"),
  my(kp, ap, P, sa, r);
  kp = bestrec[1]; ap = bestrec[2]; P = bestrec[3]; sa = bestrec[4]; r = bestrec[5];
  print("\n=== best ===");
  print("primes of a: ", kp);
  print("a  = ", prod(t=1,#kp,kp[t]));
  print("a' = ", ap);
  print("P (prime cofactor of a') = ", P);
  printf("sigma(a) - 30/31 = %s\n", sa - TARGET);
  printf("|r - 1|          = %.6e   (best from below before this: 7.9220e-3)\n", 1.0*abs(r-1));
  printf("sigma(a) < 30/31 : %d   (required by prop:oneprime at M=30)\n", sa < TARGET));
}
quit;
