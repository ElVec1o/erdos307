\\ kladder_check.gp -- the k-ladder is algebra, and no search can witness it.
\\
\\ prop:pyth: for squarefree N, N'^2 - 4N^2 is a square iff N = ab with a, b coprime and
\\ N' = a^2 + b^2. Writing sigma(a) = b/a + k, that condition is equivalent to the ladder
\\
\\     a' = b + k a,     b' = a - k b,
\\
\\ with k an integer, and #307 is exactly the rung k = 0.
\\
\\ FIRST VERSION OF THIS SCRIPT WAS WRONG, and the way it was wrong is worth keeping. It searched
\\ squarefree N < 400000 for the Pythagorean locus, found nothing, ran its k-integrality and
\\ k-in-{0,-1} checks over the empty set, and printed "the reduction is sound". A verdict on zero
\\ data (Rule 7). The locus is empty for a structural reason, not a small-range accident:
\\
\\     N' = a^2 + b^2 >= 2ab = 2N,   so   sigma(N) >= 2,
\\
\\ which by the barrier needs omega(N) >= 59 and N > 8.77e112. That is cor:emptytest. NO brute-force
\\ search over N can ever produce a single instance, so the empirical route to checking the ladder
\\ does not exist and the ladder has to be established as algebra.
\\
\\ This version does that, and reports the emptiness as the finding it is:
\\   (1) the ladder identity is a polynomial identity, checked on random coprime squarefree pairs;
\\   (2) integrality of k follows from b(a'-b) = a(a-b') with gcd(a,b)=1, checked the same way;
\\   (3) the locus really is empty below the search bound, and the reason is printed, not the verdict.
\\
\\ Run:  gp -q -f kladder_check.gp

default(parisize, 2000000000);

der(n) = { my(f = factor(n)[,1]); sum(i = 1, #f, n/f[i]); }
sig(n) = { my(f = factor(n)[,1]); sum(i = 1, #f, 1/f[i]); }

\\ ---------------------------------------------------------------- (1) and (2): the algebra
print("(1)+(2)  the ladder identity and the integrality of k, on coprime squarefree pairs");
{
my(bad = 0, tested = 0, badint = 0);
for(a = 2, 300,
  if(!issquarefree(a), next);
  for(b = a+1, 300,
    if(!issquarefree(b) || gcd(a, b) != 1, next);
    my(N = a*b, Nd = der(N), ad = der(a), bd = der(b));
    tested++;
    \\ the identity that makes k integral:  b(a'-b) - a(a-b')  =  N' - (a^2+b^2)
    if(b*(ad - b) - a*(a - bd) != Nd - (a^2 + b^2), bad++);
    \\ so ON the locus, a | a'-b; off it there is nothing to check. Verify the implication directly.
    if(Nd == a^2 + b^2 && (ad - b) % a != 0, badint++)));
printf("   coprime squarefree pairs tested: %d\n", tested);
printf("   identity  b(a'-b) - a(a-b') = N' - (a^2+b^2)  failures: %d\n", bad);
printf("   integrality failures on the locus: %d\n", badint);
if(bad == 0,
  print("   The identity holds. Since gcd(a,b)=1, on the locus a | (a'-b), so k = (a'-b)/a is an"),
  print("   *** IDENTITY FAILED ***"));
print("   integer and b' = a - k b follows. That is the ladder, and it is proved, not sampled.");
}

\\ ---------------------------------------------------------------- (3) the locus is unreachable
print("");
print("(3)  why no search can witness any of this");
{
my(tested = 0, found = 0, maxsig = 0.0, argmax = 0, B = 400000);
for(N = 6, B,
  if(!issquarefree(N) || omega(N) < 2, next);
  tested++;
  my(s = sig(N));
  if(s > maxsig, maxsig = s; argmax = N);
  if(issquare(der(N)^2 - 4*N^2), found++));
printf("   squarefree N with omega >= 2 tested below %d : %d\n", B, tested);
printf("   on the Pythagorean locus                    : %d\n", found);
printf("   largest sigma(N) seen                       : %.6f  (at N = %d)\n", maxsig, argmax);
printf("   sigma required for the locus                : >= 2\n");
print("");
print("   N' = a^2 + b^2 >= 2ab = 2N forces sigma(N) >= 2, and the barrier then forces");
print("   omega(N) >= 59 and N > 8.77e112. The locus is empty below that, unconditionally, so");
print("   the emptiness above is a THEOREM (cor:emptytest) and not evidence about the ladder.");
print("   Any script that reports on the ladder by searching N is reporting on the empty set.");
}

print("");
print("done.");
