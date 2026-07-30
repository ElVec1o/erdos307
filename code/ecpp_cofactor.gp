/* ECPP certificate for the 141-digit cofactor C of n_0', the conj:lyap counterexample.
 * C is DERIVED from the witness, not transcribed, so no copying error is possible. */
default(parisize, 400000000);
P  = select(p -> p != 307 && p != 317 && p != 359, primes([7, 373]));
n  = prod(i = 1, #P, P[i]);
np = sum(i = 1, #P, n / P[i]);
C  = np / 30;
print("n' / 30 is an integer: ", denominator(np/30) == 1);
print("C digits: ", #digits(C));
print("C = ", C);
print("BPSW: ", ispseudoprime(C));
gettime();
cert = primecert(C);
print("primecert time: ", gettime(), " ms");
print("primecertisvalid: ", primecertisvalid(cert));
print("certificate is for N = C: ", cert[1][1] == C);
write("lyap_refute_cofactor_ecpp.txt", cert);
quit;
