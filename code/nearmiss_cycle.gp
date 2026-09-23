\\ Step 2: why near-miss sets (sigma(P) = 1 - k/a, a = prod P) fail to be one half of a two-cycle.
\\ A two-cycle needs b = a' = a - k squarefree, coprime to a, with b' = a. For every node of the
\\ defect tree with k <= KMAX and a < 10^40 we record k, squarefreeness of b, and the miss e = b' - a.
KMAX = 200; AMAX = 10^40;
d(n) = my(f = factor(n)[,1]); sum(i = 1, #f, n / f[i]);
out = "runs/step2/nearmiss.txt";
visit(A, a) = {
  my(b = A - a, f, sf, e);
  if(b < 2, return);
  f = factor(b); sf = (vecmax(f[,2]) == 1);
  e = if(sf, d(b) - A, "nsf");
  write(out, [omega(A), a, sf, e, A]);
}
dfs(A, a, pmax) = {
  visit(A, a);
  if(A > AMAX, return);
  forprime(p = max(pmax + 1, A \ a + 1), (A + KMAX) \ a, dfs(A * p, a * p - A, p));
}
dfs(2, 1, 2);
print("done");
quit;
