\\ selftest for bestfirst.gp's core machinery: reproduce the known PPN chain and the two-prime completion
\\ test on real data, before any search runs (Rule 25).
{
my(pfx = [2,3,11,17,101,157,1979,10093,16879], A2 = 1, a2 = 1, i, p, na);
for(i = 1, #pfx,
  p = pfx[i]; na = a2*p - A2;
  print("prefix step p=", p, " -> A=", A2*p, " a=", na);
  A2 = A2*p; a2 = na);
print("N_9 = ", A2, " (expect 5998279018951962402), defect a = ", a2, " (expect 1)");
if(A2 != 5998279018951962402 || a2 != 1, print("SELFTEST FAILED: N_9 prefix mismatch"); quit);
my(q = A2 + 1);
print("N_9+1 = ", q, " prime? ", isprime(q), " (expect 1)");
if(!isprime(q), print("SELFTEST FAILED: N_9+1 not prime"); quit);
my(N10 = A2 * q);
print("N_10 = ", N10, " (expect 35979351189199316534587473905773572006)");
if(N10 != 35979351189199316534587473905773572006, print("SELFTEST FAILED: N_10 mismatch"); quit);
}
{
my(A0 = 6, a0 = 1, N0, divs, i, d, ee, q1, q2, hit);
N0 = A0^2 + a0; divs = divisors(N0); hit = 0;
for(i = 1, #divs,
  d = divs[i]; ee = N0/d;
  if((d + A0) % a0 == 0 && (ee + A0) % a0 == 0,
    q1 = (d + A0)/a0; q2 = (ee + A0)/a0;
    if(q1 != q2 && isprime(q1) && isprime(q2),
      print("completion candidate q1=", q1, " q2=", q2);
      if(A0*q1*q2 == 1806, hit = 1))));
if(!hit, print("SELFTEST FAILED: did not recover 1806 = 2*3*7*43 via two-prime completion"); quit);
print("SELFTEST PASSED: N_9/N_10 prefix chain and the 1806 two-prime completion both reproduce exactly.");
}
quit;
