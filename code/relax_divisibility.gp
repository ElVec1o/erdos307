{
my(P, Q, DP, DQ, pP, pQ, found, tot, pool, n, i, j, a, b);
print("RELAX AND MEASURE (Rule 2). A two-cycle needs prod(Q) = D(P) and prod(P) = D(Q) EXACTLY.");
print("Relaxation: require only  prod(Q) | D(P)  and  prod(P) | D(Q).");
print("Equivalently, by lem:symbolfact:  sum_{p in P} p^-1 = 0 (mod q) for all q in Q, and dually.");
print("If the relaxed system has solutions but the exact one does not, the obstruction is the");
print("EQUALITY (which forces mass >= 2), not the divisibility.");
print("");
pool = primes(60);
found = 0; tot = 0;
\\ |P| = |Q| = 2
for(i1 = 1, #pool, for(i2 = i1+1, #pool,
  P = [pool[i1], pool[i2]];
  pP = P[1]*P[2]; DP = P[1] + P[2];
  for(j1 = 1, #pool, for(j2 = j1+1, #pool,
    Q = [pool[j1], pool[j2]];
    if(Q[1] == P[1] || Q[1] == P[2] || Q[2] == P[1] || Q[2] == P[2], next);
    pQ = Q[1]*Q[2]; DQ = Q[1] + Q[2];
    tot++;
    if(DP % pQ == 0 && DQ % pP == 0,
      found++;
      if(found <= 10, print("  RELAXED SOLUTION  P=", P, " Q=", Q,
        "   D(P)=", DP, " = ", DP/pQ, "*prod(Q);  D(Q)=", DQ, " = ", DQ/pP, "*prod(P)")))))));
print("");
print("|P|=|Q|=2 pairs tested: ", tot, "   relaxed solutions: ", found);
print("");
print("=== and the EXACT system at |P|=|Q|=2?  prod(Q) = D(P), prod(P) = D(Q) ===");
found = 0;
for(i1 = 1, #pool, for(i2 = i1+1, #pool,
  P = [pool[i1], pool[i2]]; pP = P[1]*P[2]; DP = P[1]+P[2];
  for(j1 = 1, #pool, for(j2 = j1+1, #pool,
    Q = [pool[j1], pool[j2]];
    if(Q[1]==P[1]||Q[1]==P[2]||Q[2]==P[1]||Q[2]==P[2], next);
    pQ = Q[1]*Q[2]; DQ = Q[1]+Q[2];
    if(DP == pQ && DQ == pP, found++; print("  EXACT: P=",P," Q=",Q))))));
print("exact solutions at size 2: ", found, "  (mass of any such pair is far below 2)");
}
quit;
{
my(P, Q, DP, DQ, pP, pQ, bad, tot, pool, k, sP, sQ);
print("FALSIFY the claim: does prod(Q) | D(P) and prod(P) | D(Q) really force sigma(P)sigma(Q) >= 1?");
print("Random disjoint prime sets, keep those satisfying BOTH divisibilities, check the mass.");
print("");
pool = primes(200);
bad = 0; tot = 0;
for(t = 1, 400000,
  my(S, idx); S = List();
  k = 2 + random(4);
  for(i = 1, 2*k, listput(S, pool[1 + random(#pool)]));
  S = Set(S); if(#S < 2*k, next);
  S = Vec(S);
  P = vector(k, i, S[i]); Q = vector(k, i, S[k+i]);
  pP = prod(i=1,k,P[i]); pQ = prod(i=1,k,Q[i]);
  DP = sum(i=1,k,pP/P[i]); DQ = sum(i=1,k,pQ/Q[i]);
  if(DP % pQ != 0 || DQ % pP != 0, next);
  tot++;
  sP = 1.0*DP/pP; sQ = 1.0*DQ/pQ;
  if(sP*sQ < 1 - 1e-12, bad++; print("  VIOLATION P=",P," Q=",Q," product=",sP*sQ)));
print("random sets satisfying BOTH divisibilities: ", tot);
print("violations of sigma(P)sigma(Q) >= 1: ", bad);
print("");
print("=== direct check of the algebra on arbitrary positive data ===");
bad = 0;
for(t = 1, 200000,
  my(a, b, x, y); a = 1 + random(10^6); b = 1 + random(10^6);
  x = random(300)/100.0 + 0.01; y = random(300)/100.0 + 0.01;
  if(b <= x*a && a <= y*b && x*y < 1 - 1e-9, bad++));
print("counterexamples to (b <= xa and a <= yb) => xy >= 1 : ", bad);
}
quit;
