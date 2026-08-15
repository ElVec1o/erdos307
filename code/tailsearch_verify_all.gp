\\ tailsearch_verify_all.gp -- exact verification of tailsearch survivors, driven by the config file.
\\
\\ The earlier verifier rebuilt the 34 immune families in order to interpret survivor indices, which
\\ only works for the immune run. This one reads D, N, A, B and the prime list straight out of the
\\ config that the searcher itself consumed, so it verifies ANY run, including the 49,961-base one,
\\ and it cannot disagree with the searcher about which family an index refers to.
\\
\\ A modular filter can only ever produce FALSE POSITIVES: a true square is a quadratic residue
\\ modulo everything. So the searcher's survivor list is a superset of the true hits, and testing
\\ every survivor with exact bignum issquare settles the run.
\\
\\ Set CFG and SURV below, then:  gp -q -f tailsearch_verify_all.gp

default(parisize, 8000000000);
CFG  = "tailsearch_cfg_all.txt";
SURV = "tailsearch_survivors_all.txt";

{
my(cl, sl, fam, nf, hits, checked, bad, f1, D1, N1, A1, B1);

cl = iferr(readstr(CFG), E, 0);
if(type(cl) != "t_VEC", printf("cannot read %s\n", CFG); quit);
sl = iferr(readstr(SURV), E, 0);
if(type(sl) != "t_VEC", printf("cannot read %s\n", SURV); quit);

\\ parse config: one family per line, D N A B p1..p59
fam = List();
for(i = 1, #cl,
  my(L = cl[i], tk);
  if(#L == 0 || Vec(L)[1] == "#", next);
  tk = select(s -> #s > 0, strsplit(L, " "));
  listput(fam, vector(#tk, t, eval(tk[t]))));
nf = #fam;
printf("config %s: %d families\n", CFG, nf);

\\ spot-check the algebra on the first family, so a malformed config cannot pass silently
f1 = fam[1]; D1 = f1[1]; N1 = f1[2]; A1 = f1[3]; B1 = f1[4];
printf("  family 1: A = N+2D %d, B = N-2D %d, AB = N^2-4D^2 %d, D<N %d, D squarefree %d\n",
       A1 == N1 + 2*D1, B1 == N1 - 2*D1, A1*B1 == N1^2 - 4*D1^2, D1 < N1, issquarefree(D1));

hits = 0; checked = 0; bad = 0;
for(i = 1, #sl,
  my(L = sl[i], tk, w, f, D, N, A, B, odd, m, k);
  if(#L == 0 || Vec(L)[1] == "#", next);
  tk = select(s -> #s > 0, strsplit(L, " "));
  w  = vector(#tk, t, eval(tk[t]));
  \\ w = [family_index, b, count, idx...]  with indices into the ODD primes of S
  f = fam[w[1] + 1];
  D = f[1]; N = f[2]; A = f[3]; B = f[4];
  odd = select(x -> x != 2, vector(#f - 4, t, f[4 + t]));
  m = 2^w[2];
  for(t = 1, w[3], m *= odd[w[3 + t] + 1]);
  if((4*D) % m != 0, bad++);          \\ m must divide 4D, or the searcher walked the wrong set
  checked++;
  if(issquare(A*B + D*m^2, &k),
    hits++;
    printf("  *** SQUARE: family %d (line %d), m = %d\n", w[1], i, m);
    for(s = 1, 2,
      my(sg = 2*s - 3, qq = 2*(N + sg*k));
      if(qq > 0 && qq % m^2 == 0,
        qq = qq / m^2;
        printf("      q = %d\n      prime? %d   q | 2D? %d   q <= 4N? %d\n",
               qq, isprime(qq), (2*D) % qq == 0, qq <= 4*N)))));

printf("\nchecked %d survivors\n", checked);
printf("m | 4D violations: %d   (must be 0)\n", bad);
printf("actual squares:    %d\n", hits);
if(hits == 0 && bad == 0,
  print("\nVERIFIED EMPTY on the searched slice."),
  print("\n*** see above ***"));
}
