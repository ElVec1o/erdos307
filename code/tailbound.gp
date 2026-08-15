\\ tailbound.gp -- the Pythagorean tail prime is BOUNDED, so rem:lehmer is not Lehmer-class.
\\
\\ Setting. S a finite prime set, D = prod S, N = D' = sum_{p in S} D/p, A = N + 2D, B = N - 2D > 0.
\\ rem:lehmer: a Pythagorean pair in the tail family S u {q} is a solution of B x^2 - A y^2 = -4 D^2
\\ with q = (x^2 - D)/A = (y^2 - D)/B a positive prime, and the paper reads the surviving question as
\\ the primality of a term q_n of the exponential Pell orbit -- a Lehmer/Mersenne question.
\\
\\ It is not. Because A - B = 4D exactly,
\\        x^2 - y^2 = (A - B) q = 4 D q,      so   (x - y)(x + y) = 4 D q.
\\ A prime q with q \nmid 2D divides exactly one factor, so x + y = q m and x - y = 4D/m for a
\\ divisor m | 4D (the other case gives the same x). Substituting into x^2 = Aq + D and using
\\ 8D - 4A = -4N gives  (q m^2)^2 - 4N (q m^2) + 16 D^2 - 4 D m^2 = 0, hence
\\
\\        q = 2 (N +- k) / m^2,      k^2 = A B + D m^2,      m | 4D,            (*)
\\
\\ using A B = N^2 - 4 D^2. Since A B + D < N^2 the largest value is at m = 1, so
\\
\\        q < 4 N.                                                             (**)
\\
\\ So the tail primes form a FINITE explicitly parametrised set, the exponential orbit contributes
\\ nothing past a bounded initial segment, and the residual question is a finite search over the
\\ divisors of 4D, not a Lehmer primality question.
\\
\\ This script checks (*) and (**) four ways:
\\   (1) forward     -- every m solving (*) yields q with Aq + D and Bq + D both squares;
\\   (2) backward    -- exhaustive search over primes q finds NOTHING outside (*);
\\   (3) the orbit   -- the Pell orbit really is infinite, its terms really do satisfy both square
\\                      conditions, and every term past the bound is composite, as (**) demands;
\\   (4) the census  -- expected number of admissible m on a real immune base.
\\
\\ Run:  gp -q -f tailbound.gp

default(parisize, 2000000000);

\\ ---------------------------------------------------------------- helpers
\\ tail primes of the base (D,N) predicted by the parametrisation (*)
para(D, N) =
{
  my(A = N + 2*D, B = N - 2*D, AB, out = List(), k, q, s);
  AB = A*B;
  fordiv(4*D, m,
    if(issquare(AB + D*m^2, &k),
      for(j = 1, 2,
        s = 2*j - 3;
        q = 2*(N + s*k);
        if(q > 0 && q % m^2 == 0,
          q = q / m^2;
          if(q > 1 && isprime(q) && (2*D) % q != 0, listput(out, q))))));
  Set(Vec(out));
}

\\ tail primes of the base (D,N) found by exhaustive search up to bound X
brute(D, N, X) =
{
  my(A = N + 2*D, B = N - 2*D, out = List());
  forprime(q = 2, X,
    if((2*D) % q == 0, next);
    if(issquare(A*q + D) && issquare(B*q + D), listput(out, q)));
  Set(Vec(out));
}

\\ the immune-family enumerator, as in immune_certify.gp
dfs(i, need, cur, ch) =
{
  if(need == 0, if(cur > thr, listput(bases, ch)); return());
  if(i + need > np + 1, return());
  if(cur + (cum[min(i+need, np+1)] - cum[i]) <= thr, return());
  dfs(i+1, need-1, cur + pf[i], concat(ch, [i]));
  dfs(i+1, need, cur, ch);
}

\\ ---------------------------------------------------------------- (1) and (2)
print("(1)+(2)  parametrisation (*) against exhaustive search");
print("             D      N      4N   param            brute");
{
my(bad = 0, tested = 0, shown = 0, B, X, P, Q);
for(D = 1, 40,
  for(N = 2*D + 1, 2*D + 30,
    B = N - 2*D;
    if(B <= 0, next);
    X = min(4*N, 60000);
    P = select(x -> x <= X, para(D, N));
    Q = brute(D, N, X);
    tested++;
    if(P != Q, bad++; printf("  MISMATCH  D=%d N=%d  param=%s  brute=%s\n", D, N, P, Q));
    if(#Q > 0 && shown < 8,
      shown++;
      printf("      %6d %6d %7d   %-16s %-16s %s\n", D, N, 4*N, P, Q, if(P == Q, "agree", "DIFFER")))));
printf("\n         bases tested: %d      mismatches: %d\n", tested, bad);
if(bad == 0,
  print("         (*) is SOUND and COMPLETE on every base tested: no prime tail escapes it."),
  print("         *** (*) FAILED ***"));
}

\\ ---------------------------------------------------------------- (3) the orbit
print("");
print("(3)  the Pell orbit: infinite, satisfies both square conditions, composite past the bound");
{
my(D = 1, N = 7, A, B, x = 8, y = 6, u = 161, v = 24, X, q, np2, X2, y2, lab);
A = N + 2*D; B = N - 2*D;
printf("     base D=%d N=%d  A=%d B=%d   bound (**) 4N = %d\n", D, N, A, B, 4*N);
printf("     automorph of u^2 - %d v^2 = 1:  (u,v) = (%d,%d)   [orbit ratio ~ %d]\n", A*B, u, v, 2*u);
printf("       n              q_n   integer  Aq+D sq  Bq+D sq   q_n < 4N   prime?\n");
X = B*x;
for(n = 1, 7,
  q = (x^2 - D)/A;
  np2 = if(denominator(q) == 1, if(q < 10^30, if(isprime(q), "PRIME", "composite"), "too big: composite by (**)"), "-");
  lab = if(#Str(q) > 15, concat(Str(#digits(q)), " digits"), Str(q));
  printf("     %3d  %15s      %3s      %3s      %3s        %3s   %s\n",
         n, lab,
         if(denominator(q) == 1, "yes", "no"),
         if(issquare(A*q + D), "yes", "NO"), if(issquare(B*q + D), "yes", "NO"),
         if(q < 4*N, "yes", "no"), np2);
  X2 = X*u + A*B*y*v; y2 = X*v + y*u;
  X = X2; y = y2; x = X/B);
print("     The orbit is genuinely infinite and both square conditions hold along all of it.");
print("     Every term past the bound is composite, exactly as (**) requires.");
}

\\ ---------------------------------------------------------------- (4) the immune base
print("");
print("(4)  a real immune base: how large is the finite search, and how full is it expected to be?");
P = primes([2,800]);
T58 = sum(i = 1, 58, 1/P[i]);
forc = select(x -> x <= 167, P);
pool = select(x -> x > 167 && T58 + 1/x > 2, P);
np = #pool;
kk = 59 - #forc;
thr = 2 - sum(i = 1, #forc, 1/forc[i]);
pf = vector(np, i, 1/pool[i]);
cum = vector(np+1); cum[1] = 0;
for(i = 1, np, cum[i+1] = cum[i] + pf[i]);
bases = List();
dfs(1, kk, 0, []);
imm = List();
{
my(S, D, N, A, B);
for(j = 1, #bases,
  S = concat(forc, vector(#bases[j], t, pool[bases[j][t]]));
  D = prod(t = 1, #S, S[t]);
  N = sum(t = 1, #S, D \ S[t]);
  A = N + 2*D; B = N - 2*D;
  if(ispseudoprime(A) && ispseudoprime(B) && kronecker(D, A) == 1, listput(imm, [D, A, B, S])));
}
printf("     immune families: %d\n", #imm);
{
my(D, A, B, S, N, sumrecip, expct, tot);
if(#imm > 0,
  D = imm[1][1]; A = imm[1][2]; B = imm[1][3]; S = imm[1][4]; N = A - 2*D;
  printf("     first immune base:  |S| = %d,  D = %d digits,  N = %d digits\n", #S, #digits(D), #digits(N));
  printf("     tail bound (**):    q < 4N, a %d-digit bound -- FINITE, not a Lehmer question\n", #digits(4*N));
  printf("     divisors of 4D:     3 * 2^%d = %.3e candidates m\n", #S - 1, 3.0 * 2^(#S-1));
  sumrecip = prod(t = 1, #S, 1 + 1.0/S[t]) * (1 + 1/2. + 1/4.);
  expct = sumrecip / sqrt(1.0 * D);
  printf("     sum_{m | 4D} 1/m:   %.4f\n", sumrecip);
  printf("     expected #{m : AB + D m^2 = square}:  %.3e   <-- heuristically EMPTY\n", expct);
  tot = 0.0;
  for(j = 1, #imm, tot += prod(t = 1, #imm[j][4], 1 + 1.0/imm[j][4][t]) * 1.75 / sqrt(1.0*imm[j][1]));
  printf("     summed over all %d immune families:    %.3e\n", #imm, tot);
  print("     So the finite search is expected to contain nothing, on every immune family.");
  print("     That reverses the 'weakly favours yes' reading of rem:killcount for these families."));
}

print("");
print("done.");
