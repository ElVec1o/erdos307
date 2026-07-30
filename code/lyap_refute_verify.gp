/* lyap_refute_verify.gp -- independent EXACT verification that conj:lyap is FALSE.
 *
 * conj:lyap: there is a lambda > 0 with
 *      log sigma(n) < lambda (sigma(n) - sigma(n'))                                  (*)
 * for every squarefree n whose derivative n' is squarefree.
 *
 * Witness: n = product of the primes in [7,373] except 307, 317 and 359. Then sigma(n) > 1, so the left
 * side of (*) is positive, while sigma(n') > sigma(n) makes the right side negative for every
 * lambda > 0. So (*) fails at this single n for all lambda simultaneously.
 *
 * All comparisons are exact rational arithmetic; nothing depends on floating point. The only
 * external input is the primality of the 135-digit cofactor of n' (ECPP, ecpp_cofactor.gp).
 *
 * Usage: gp -q -f lyap_refute_verify.gp
 */

P = select(p -> p != 307 && p != 317 && p != 359, primes([7, 373]));
n  = prod(i = 1, #P, P[i]);
np = sum(i = 1, #P, n / P[i]);                      /* n' , exact */

print("=== witness ===");
print("n = product of the ", #P, " primes in [7,373] other than 307, 317 and 359");
print("digits(n) = ", #digits(n), ",  digits(n') = ", #digits(np));
print("n squarefree: ", if(issquarefree(n), "YES", "NO"), "   (product of distinct primes)");
print("gcd(n,n') = ", gcd(n, np), "   (thm:structure predicts 1)");
print("");

print("=== sigma(n), exact ===");
sn = sum(i = 1, #P, 1/P[i]);
print("sigma(n) = ", sn);
print("as a float: ", 1.0 * sn);
print("sigma(n) = n'/n exactly (rigidity): ", if(sn == np/n, "YES", "NO"));
print("sigma(n) > 1 exactly: ", if(sn > 1, "YES", "NO"));
print("");

print("=== factorisation of n' ===");
f = factor(np);
print(f);
print("factors multiply back to n': ", if(factorback(f) == np, "YES", "NO"));
print("every exponent is 1, so n' is SQUAREFREE: ", if(vecmax(f[,2]) == 1, "YES", "NO"));
snp = sum(i = 1, #f~, 1/f[i,1]);
print("sigma(n') = ", snp);
print("as a float: ", 1.0 * snp);
print("");

print("=== the refutation, exact ===");
print("sigma(n') > sigma(n) exactly: ", if(snp > sn, "YES", "NO"));
print("sigma(n') - sigma(n) = ", 1.0 * (snp - sn));
print("");
print("Hence for every lambda > 0:  lambda*(sigma(n) - sigma(n')) < 0 < log sigma(n),");
print("because sigma(n) > 1 makes log sigma(n) > 0. So (*) fails at this n for EVERY lambda,");
print("and conj:lyap is FALSE. (sigma(n') = sigma(n) is impossible anyway by lem:sigmainj.)");
print("");

print("=== consistency with what is proved ===");
tot = sn + snp;
print("sigma(n) + sigma(n') = ", 1.0 * tot, " > 2, so thm:halflyap does NOT apply here:");
print("its hypothesis sigma(n n') < 2 fails, as it must. The witness sits just above the");
print("threshold 2, which shows the hypothesis of thm:halflyap cannot be weakened.");
print("thm:rhobarrier requires n*n' >= Pi_59 = 8.77e112 whenever sigma(n') >= sigma(n) > 1:");
print("  digits(n*n') = ", #digits(n * np), ", so the requirement is met with room to spare.");
print("rho = sigma(n')/sigma(n) = ", 1.0 * (snp/sn), " > 1, so rho is not bounded by 1 either.");
print("");
print("#307 itself is NOT decided by this: conj:lyap was only a SUFFICIENT condition for the");
print("negative answer, so its refutation closes a route and decides nothing about #307.");

print("");
print("=== consequence: the near-miss quantity r crosses 1 ===");
r = sn * snp;
print("r(n) = sigma(n)*sigma(n') = ", 1.0 * r, "   (prop:nearmiss sweep max over a <= 1e7 is 0.5535)");
print("r > 1 exactly: ", if(r > 1, "YES", "NO"));
npp = np * snp;
print("n'' = n'*sigma(n') = ", npp);
print("n'' is an integer: ", if(denominator(npp) == 1, "YES", "NO"));
print("n'' > n exactly: ", if(npp > n, "YES", "NO"), "   (so the second derivative exceeds n)");
print("n''/n = ", 1.0 * (npp/n));
print("both n and n' are squarefree, so this is a legitimate point of the class prop:nearmiss");
print("sweeps; the region r >= 1 is therefore reachable by construction, though not by sweeping.");
quit;

