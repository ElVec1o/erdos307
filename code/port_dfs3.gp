\\ Primitive port fillings for Erdos #313 (primary pseudoperfect numbers).
\\ v3: per-node width cap W primes; closure only when defect a <= AMAX (dfs2 stalled: tree grows x20/level).
\\ Node = squarefree A with defect a = A - A' > 0 (sigma(A) < 1). Appending a prime p > A/a
\\ gives defect a*p - A. Defect 1 <=> PPN. DFS keeps defects <= B; at every node with
\\ A < 10^LIM the two-prime closure (a q1 - A)(a q2 - A) = A^2 + a is solved by factoring.
\\ Output: one line per PPN found, appended to runs/port_dfs3/hits.txt (resumable by rerun).
C = 20; LIM = 40; DEPTH = 11; W = 20; AMAX = 10^6;
seen = Map();
rec(n) = if(!mapisdefined(seen,n), mapput(seen,n,1); write("runs/port_dfs3/hits.txt", [omega(n), n]); print("PPN ", omega(n), " ", n));
closure(A,a,pmax) = {
  my(N = A^2 + a, D);
  if(A > 10^LIM, return);
  D = divisors(N);
  for(i=1, #D, my(d=D[i], e=N/d, q1, q2);
    if(d >= e, break);
    if((d + A) % a || (e + A) % a, next);
    q1 = (d + A)/a; q2 = (e + A)/a;
    if(q1 > pmax && isprime(q1) && isprime(q2), rec(A*q1*q2)));
}
dfs(A, a, pmax, k) = {
  if(a == 1, rec(A));
  if(k >= DEPTH, return);
  if(a <= AMAX, closure(A, a, pmax));
  my(lo = max(pmax+1, A\a + 1), hi = (A + C*sqrtint(A) + 1)\a);
  my(j = 0); forprime(p = lo, hi, j++; if(j > W, break); dfs(A*p, a*p - A, p, k+1));
}
dfs(2, 1, 2, 1);
print("DONE nodes-limited run C=",C," LIM=",LIM);
