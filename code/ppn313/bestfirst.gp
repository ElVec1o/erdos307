default(parisizemax, 4*10^9);
\\ bestfirst.gp -- best-first, checkpointed search for an 11-factor primary pseudoperfect number (Erdos #313).
\\
\\ A PPN prefix is (A, a): A squarefree, a = A - A' > 0. Appending a prime p > A/a gives new defect a*p - A.
\\ A two-prime completion of prefix (A,a) exists iff a divisor d of N = A^2 + a has d == -A (mod a), giving
\\ q1=(d+A)/a, q2=(N/d+A)/a, both prime, both > max prefix prime. Core machinery re-derived and checked
\\ against the known chain (N_9, N_10) and the 1806 = 2*3*7*43 completion in selftest.gp before this ran.
\\
\\ Priority: expand the node whose N=A^2+a looks smoothest (trial division to 1e5) combined with 1/log(a),
\\ since a smooth N has more candidate divisor pairs. Full factorization is attempted only for the node
\\ actually popped; on failure within budget the node is written to unresolved.txt and dropped from further
\\ automatic expansion (never silently discarded -- it is on disk, re-checkable by hand).
\\
\\ Literature: infinitude of PPNs is open (erdosproblems.com); no PPN beyond N_10 (10 factors) is known
\\ published anywhere (checked 2026-09-27: Wang's paper, OEIS A054377, erdosproblems.com forum); Alekseyev
\\ confirmed no other PPN below 10^24 (OEIS, Aug 2026), which N_10 already exceeds by 13 orders of magnitude,
\\ so this search targets extensions of large prefixes, not a small-number sweep.
\\
\\ Checkpoint: frontier.gp (GP vector literal, one row per open node [A,a,pmax,depth]), atomic (tmp+rename),
\\ every ROUND pops and at exit. Resume: rerun in the same directory, it reloads frontier.gp if present.
\\ Run:   gp -q bestfirst.gp <BUDGET_SECONDS> <MAXDIG> (via a wrapper that sets these -- see run.sh)

BUDGET = getenv("PPN_BUDGET"); if(BUDGET == "" || BUDGET == 0, BUDGET = 3600, BUDGET = eval(BUDGET));
MAXDIG = getenv("PPN_MAXDIG"); if(MAXDIG == "" || MAXDIG == 0, MAXDIG = 45, MAXDIG = eval(MAXDIG));
ROUND = 100; TRIALBOUND = 100000;

score(A, a) = {
  my(C = A^2 + a, e = 0, p);
  forprime(p = 2, TRIALBOUND, while(C % p == 0, C \= p; e++));
  my(sm = e * 1.0 + if(C == 1, 0, if(ispseudoprime(C), 1, 2)));
  sm - log(a + 1) / log(2);
}

MAXKIDS = 25;
expand(A, a, pmax) = {
  my(lo = max(pmax + 1, A\a + 1), width = max(500, a \ 20 + 100), hi = lo + width, out = List(), p);
  forprime(p = lo, hi, my(na = a*p - A, nA = A*p);
    if(na > 0 && #Str(nA) <= MAXDIG, listput(out, [nA, na, p, score(nA, na)])));
  \\ cap branching: keep only the MAXKIDS best-scoring children, so the frontier does not blow up
  if(#out > MAXKIDS,
    my(v = Vec(out)); v = vecsort(v, (x,y) -> -sign(x[4] - y[4]));
    out = List(vector(MAXKIDS, i, v[i])));
  out;
}

tryComplete(A, a, pmax, depth) = {
  if(a <= 0, write("unresolved.txt", [A, a, "non-positive defect, skipped"]); return);
  if(a == 1,
    write("hits.txt", [depth, A, "single-prefix"]);
    print("PPN FOUND (prefix itself): A=", A, " depth=", depth));
  if(#Str(A) > MAXDIG, return);
  my(N = A^2 + a, f = factor(N, 10^7), C = 1, i, ps = List(), es = List());
  for(i = 1, matsize(f)[1],
    if(f[i,1] > 10^7, C *= f[i,1]^f[i,2], listput(ps, f[i,1]); listput(es, f[i,2])));
  if(C > 1 && !ispseudoprime(C) && #Str(C) > 40,
    write("unresolved.txt", [A, a, "cofactor digits", #Str(C)]);
    return);
  \\ N is now known fully: the trial-divided small factors (ps,es, each prime <= 1e7), plus the leftover
  \\ cofactor C (1, a probable prime, or itself refactored below 40 digits) -- disjoint from ps/es, no
  \\ double-counting.
  my(psv = Vec(ps), esv = Vec(es));
  if(C > 1,
    if(ispseudoprime(C), psv = concat(psv, [C]); esv = concat(esv, [1]),
      my(cf = factor(C)); psv = concat(psv, cf[,1]~); esv = concat(esv, cf[,2]~)));
  my(full = matrix(#psv, 2, i, j, if(j == 1, psv[i], esv[i])));
  \\ integrity check: the reconstructed factorization must multiply back to N exactly (Rule 25)
  if(factorback(full) != N, write("unresolved.txt", [A, a, "factorback mismatch, bug"]); return);
  my(divs = divisors(full));
  my(i2, d, ee, q1, q2);
  for(i2 = 1, #divs,
    d = divs[i2]; ee = N/d;
    if((d + A) % a == 0 && (ee + A) % a == 0,
      q1 = (d + A)/a; q2 = (ee + A)/a;
      if(q1 != q2 && q1 > pmax && q2 > pmax && isprime(q1) && isprime(q2),
        write("hits.txt", [depth+2, A*q1*q2, q1, q2, "two-prime completion"]);
        print("TWO-PRIME COMPLETION FOUND: A=", A, " q1=", q1, " q2=", q2))));
}

{
my(t0 = getabstime(), frontier = List(), rounds = 0, p, bi, bs, node, A, a, pmax, depth, kids, k, tmp);
if(system("test -f frontier.gp") == 0,
  frontier = List(eval(read("frontier.gp"))),
  forprime(p = 2, 200, listput(frontier, [p, p - 1, p, 1, score(p, p - 1)])));
print("PPN313 best-first search: frontier=", #frontier, " budget=", BUDGET, "s maxdig=", MAXDIG);
while(getabstime() - t0 < BUDGET * 1000 && #frontier > 0,
  bi = 1; bs = frontier[1][5];
  for(k = 2, #frontier, if(frontier[k][5] > bs, bs = frontier[k][5]; bi = k));
  node = frontier[bi]; listpop(frontier, bi);
  A = node[1]; a = node[2]; pmax = node[3]; depth = node[4];
  tryComplete(A, a, pmax, depth);
  if(depth < 15,
    kids = expand(A, a, pmax);
    for(k = 1, #kids, listput(frontier, [kids[k][1], kids[k][2], kids[k][3], depth + 1, kids[k][4]])));
  rounds++;
  if(rounds % ROUND == 0,
    tmp = "frontier.gp.tmp"; write(tmp, Vec(frontier)); system("mv frontier.gp.tmp frontier.gp");
    print("round ", rounds, " frontier=", #frontier, " elapsed=", (getabstime()-t0)\1000, "s")));
tmp = "frontier.gp.tmp"; write(tmp, Vec(frontier)); system("mv frontier.gp.tmp frontier.gp");
print("STOPPED (UNRESOLVED beyond this point): rounds=", rounds, " frontier=", #frontier,
  " elapsed=", (getabstime()-t0)\1000, "s");
}
quit;
