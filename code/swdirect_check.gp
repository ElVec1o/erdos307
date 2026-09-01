\\ The error bound of lem:swdirect,
\\   B(logN) = (1 + logN) * logN^A * logN^{eps/2} * exp(-c * logN^{eps/2}),
\\ at A = 1, eps = 0.2, c = 1/2.  It tends to 0, but only far beyond anything computable.  This
\\ script computes the two figures the paper quotes: where B PEAKS, and where it first falls below 1.
\\ An earlier version sampled seven decades and quoted a turnover it never located.
{
my(A, eps, c, e, lg, b, best, bestat, firstbelow);
A = 1.0; eps = 0.2; c = 0.5;
best = 0; bestat = 0; firstbelow = 0;
forstep(e = 5.0, 30.0, 0.0005,
  lg = 10.0^e;
  b = (1+lg)*lg^A*lg^(eps/2)*exp(-c*lg^(eps/2));
  if(b > best, best = b; bestat = e);
  if(firstbelow == 0 && e > bestat && b < 1.0, firstbelow = e));
printf("peak            : log N = 10^%.4f   value %.4e\n", bestat, best);
printf("first below 1   : log N = 10^%.4f\n", firstbelow);
print("");
print("sampled decades, for orientation:");
foreach([8, 12, 16, 20, 24, 30], e,
  lg = 10.0^e;
  printf("  log N = 10^%-2d   B = %.4e\n", e, (1+lg)*lg^A*lg^(eps/2)*exp(-c*lg^(eps/2))));
}
quit;
