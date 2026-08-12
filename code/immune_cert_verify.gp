\\ immune_cert_verify.gp -- third-party verification of certs/immune_ecpp.txt.
\\
\\ WHY THIS EXISTS. certs/immune_ecpp.txt is a human-readable primecertexport dump: a prose header,
\\ then per family a header line, the prime, and its Atkin-Morain certificate. PARI's
\\ read()/primecertisvalid() CANNOT consume that layout: read() parses the prose header as a
\\ polynomial and errors. The instruction printed in that file's header and in README.md,
\\ "Verify with PARI: primecertisvalid(cert)", was therefore broken as committed. This script is the
\\ working replacement: it extracts every prime the dump asserts and re-proves each one
\\ independently with ECPP, isprime(n,2), which returns a proof rather than a probable-prime verdict
\\ and is the same method (Atkin-Morain) the stored certificates use.
\\
\\ Rule 8 pre-flight. 68 subjects of 109 to 114 digits. Measured cost with ECPP: about 0.02 s each,
\\ so the whole run is under a second and needs no checkpointing. Do NOT use isprime(n,1) (APRCL)
\\ here: it is wildly variable on these inputs, measured from 12 s to over 9 minutes per subject.
\\ Peak memory is one gp process under 0.5 GB.
\\
\\ Usage:  gp -q -f code/immune_cert_verify.gp
default(parisize, 512000000);
{
  lines = readstr("certs/immune_ecpp.txt");
  n = 0; ok = 0; bad = 0; t0 = getwalltime();
  for(i = 1, #lines, L = lines[i];
    if(#L >= 50 && Vec(L)[1] >= "0" && Vec(L)[1] <= "9",
      p = eval(L); n++;
      if(isprime(p, 2), ok++, bad++; printf("  FAIL: subject %d, %d digits\n", n, #L))));
  printf("subjects asserted by the dump : %d   (34 families x {A_S, B_S})\n", n);
  printf("re-proved prime by ECPP       : %d\n", ok);
  printf("failed                        : %d\n", bad);
  printf("elapsed                       : %.2f s\n", (getwalltime()-t0)/1000.0);
  printf("VERDICT: %s\n",
    if(bad == 0 && n == 68 && ok == n, "all 68 certificate subjects are prime", "MISMATCH"));
}
quit
