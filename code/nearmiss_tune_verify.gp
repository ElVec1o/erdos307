/* Independent exact verification of the best constructed near-miss. */
P = concat(select(p -> p != 229 && p != 271, primes([7,269])), [3359]);
a = prod(i=1,#P,P[i]);
ap = sum(i=1,#P, a/P[i]);
print("w(a) = ", #P, ", digits(a) = ", #digits(a), ", digits(a') = ", #digits(ap));
print("a squarefree: ", issquarefree(a), "   gcd(a,a') = ", gcd(a,ap));
sa = sum(i=1,#P,1/P[i]);
print("sigma(a) = a'/a exactly: ", sa == ap/a);
f = factor(ap);
print("factorisation of a':"); print(f);
print("factors multiply back: ", factorback(f) == ap);
print("all exponents 1, a' SQUAREFREE: ", vecmax(f[,2]) == 1);
print("issquarefree(a') agrees: ", issquarefree(ap));
sap = sum(i=1,#f~,1/f[i,1]);
r = sa*sap;
print("sigma(a)  = ", 1.0*sa);
print("sigma(a') = ", 1.0*sap);
print("r = ", r);
print("r as float = ", 1.0*r);
print("|r-1| = ", 1.0*abs(r-1), "   (exact: ", abs(r-1), ")");
print("r < 1 exactly: ", r < 1);
print("a'' = ", ap*sap, "  integer: ", denominator(ap*sap)==1);
print("defect |a''-a| = ", abs(ap*sap - a));
print("largest prime factor of a' has ", #digits(f[#f~,1]), " digits, prime: ", isprime(f[#f~,1]));
quit
