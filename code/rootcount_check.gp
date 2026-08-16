\\ rootcount_check.gp -- falsification pass for A6's last lemma, before formalising it.
\\
\\ prop:plusthin needs |R_u| <= tau(u), where R_u = {s mod u : 2s^2 + 1 = 0 mod u}. The route being
\\ formalised is NOT the usual CRT induction. Fix one root t_0 of t^2 = c (with t = 2s, c = -2); then
\\
\\     t |-> d = gcd(u, t - t_0)
\\
\\ maps R_u into the divisors of u, and is injective. Injectivity is elementary: with e = gcd(u, t+t_0)
\\ one has gcd(d,e) = 1 and de = u, so if two roots share the same d they also share e, whence d and e
\\ both divide their difference, and de = u does too.
\\
\\ Three things are checked here before any Lean is written, since a formalisation of a false lemma is
\\ wasted work:
\\   (1) |R_u| <= tau(u) for every odd u in range, and how tight it is;
\\   (2) the injection really is injective, checked directly rather than inferred;
\\   (3) the coprimality gcd(d,e) = 1 and the identity de = u, which the injectivity proof rests on.
\\
\\ Run:  gp -q -f rootcount_check.gp

default(parisize, 1000000000);

\\ roots of 2s^2 + 1 = 0 mod u
roots(u) = { my(r = List()); for(s = 0, u-1, if((2*s^2 + 1) % u == 0, listput(r, s))); Vec(r); }

print("(1) |R_u| <= tau(u) over odd u, with the extremal cases shown");
{
my(bad = 0, tested = 0, worst = 0, argworst = 0, nonempty = 0);
forstep(u = 1, 20000, 2,
  my(R = roots(u), t = numdiv(u));
  tested++;
  if(#R > 0, nonempty++);
  if(#R > t, bad++; printf("  VIOLATION u=%d: |R|=%d > tau=%d\n", u, #R, t));
  if(#R > 0 && #R > worst, worst = #R; argworst = u));
printf("   odd u tested: %d   with a root: %d   violations: %d\n", tested, nonempty, bad);
printf("   largest |R_u| seen: %d at u = %d (tau = %d, 2^omega = %d)\n",
       worst, argworst, numdiv(argworst), 2^omega(argworst));
if(bad == 0, print("   |R_u| <= tau(u) holds throughout the range."));
}

print("");
print("(2)+(3) the injection t -> gcd(u, t - t_0), and the facts its proof uses");
{
my(badinj = 0, badcop = 0, badprod = 0, checked = 0, u, R, t0, seen, d, e);
forstep(u = 3, 20000, 2,
  R = roots(u);
  if(#R == 0, next);
  t0 = R[1];
  seen = List();
  for(i = 1, #R,
    my(t = R[i]);
    d = gcd(u, t - t0);
    e = gcd(u, t + t0);
    checked++;
    \\ (3) the two facts the injectivity argument rests on
    if(gcd(d, e) != 1, badcop++);
    if(d * e != u, badprod++);
    \\ (2) injectivity: no two distinct roots share a d
    if(setsearch(Set(Vec(seen)), d), badinj++);
    listput(seen, d)));
printf("   (t, u) pairs checked: %d\n", checked);
printf("   gcd(d, e) != 1        : %d   (must be 0)\n", badcop);
printf("   d * e != u            : %d   (must be 0)\n", badprod);
printf("   injectivity failures  : %d   (must be 0)\n", badinj);
if(badcop == 0 && badprod == 0 && badinj == 0,
  print("   The injection and both supporting facts hold throughout. Safe to formalise."),
  print("   *** a check FAILED: do NOT formalise as stated ***"));
}

print("");
print("done.");
