\\ charcancel_check.gp -- the numeric witness for rem:charcancelerratum.
\\ The step "|tau| >= 1/log N  =>  |sum_{p<=N} p^{-1-i tau}| << loglog(3+|tau|)" is false near the
\\ threshold: the true size there is ~ log(1/|tau|) ~ loglog N, while loglog(3+|tau|) is O(1).
{
N = 20000000; L = log(N);
for(k = 1, 2,
  tau = k/L;
  s = 0.0; forprime(p = 2, N, s += p^(-1-I*tau));
  printf("tau = %d/log N = %.5f   |sum| = %.4f   claimed bound loglog(3+|tau|) = %.5f   ratio = %.1f\n",
         k, tau, abs(s), log(log(3+abs(tau))), abs(s)/log(log(3+abs(tau))));
);
}


\\ ---------------------------------------------------------------------------
\\ Added after adversarial review: lem:charcancel cites this file for two further
\\ facts that it did not previously compute. Both are now here.
\\
\\ (1) |tau(chi)| = sqrt(r) for the Jacobi symbol at the moduli the paper names.
\\ (2) sqrt(r)/phi(r) <= sqrt(3)/2, with the maximum at r = 3, over odd squarefree r.
\\     (A one-line proof also exists: each local factor sqrt(p)/(p-1) < 1 for odd p,
\\     so the supremum is the single factor at r = 3. The sweep is corroboration.)
{
print("");
print("(1) Gauss sums |tau(chi)| vs sqrt(r):");
foreach([3, 15, 21, 33, 35, 105, 1155], r,
  g = sum(t = 0, r-1, kronecker(t, r) * exp(2*Pi*I*t/r));
  printf("    r = %4d   |tau| = %.9f   sqrt(r) = %.9f   agree: %s\n",
         r, abs(g), sqrt(r), if(abs(abs(g)-sqrt(r)) < 1e-9, "yes", "NO")));
print("");
print("(2) sup of sqrt(r)/phi(r) over odd squarefree r > 1:");
worst = 0.0; wr = 0;
forstep(r = 3, 200000, 2, if(issquarefree(r), v = sqrt(r)/eulerphi(r); if(v > worst, worst = v; wr = r)));
printf("    max = %.6f at r = %d   (sqrt(3)/2 = %.6f)   surviving fraction >= %.6f\n",
       worst, wr, sqrt(3)/2, 1 - worst);
}
quit
