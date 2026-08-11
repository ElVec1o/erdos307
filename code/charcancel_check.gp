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
quit
