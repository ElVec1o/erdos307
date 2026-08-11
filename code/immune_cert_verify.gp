\\ immune_cert_verify.gp -- third-party verification of certs/immune_ecpp.txt.
\\
\\ That file is a HUMAN-READABLE primecertexport dump: prose header, then, per family, a header line
\\ and the prime followed by its Atkin-Morain certificate. PARI's read()/primecertisvalid() cannot
\\ consume it, so the instruction printed in earlier versions of the file and of README.md was wrong.
\\ This script gives a working verification path instead: it extracts every prime asserted by the
\\ dump and re-proves primality independently with APRCL (isprime(p,1)), which returns a proof, not a
\\ probable-prime verdict. Agreement on all 68 is the check.
\\
\\ Usage:  gp -q -f code/immune_cert_verify.gp
{
  f = "certs/immune_ecpp.txt";
  lines = readstr(f);
  ok = 0; bad = 0; n = 0;
  for(i = 1, #lines,
    L = lines[i];
    \\ a bare big decimal line is an asserted prime
    if(#L >= 50 && Vec(L)[1] >= "0" && Vec(L)[1] <= "9",
      p = eval(L); n++;
      if(isprime(p, 1), ok++, bad++; printf("  FAIL at line %d: %d digits\n", i, #L));
    );
  );
  printf("primes asserted by the dump : %d\n", n);
  printf("re-proved prime by APRCL    : %d\n", ok);
  printf("failed                      : %d\n", bad);
  printf("VERDICT: %s\n", if(bad == 0 && n > 0, "all certificates' subjects are prime", "MISMATCH"));
}
quit
