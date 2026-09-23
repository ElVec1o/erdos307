\\ q_exact.gp -- exact decision of q-sieve survivors (code/qsieve/q_sieve.rs).
\\ A two-cycle on the family S u {q} with a = q*alpha, b = beta, alpha*beta = D forces
\\   A q + D = (q alpha + beta)^2,  B q + D = (q alpha - beta)^2,  A, B = D' +- 2D.
\\ So x = sqrt(Aq+D), y = sqrt(Bq+D) give {q alpha, beta} = {(x+y)/2, (x-y)/2}; the survivor is a cycle iff for one
\\ of the two assignments alpha is an integer divisor of D, beta = D/alpha, and beta' = q alpha, beta - alpha = q alpha'.
\\ Usage: gp -q q_exact.gp < /dev/null  with BASES and RESULTS set below (or via the default paths).
dd(n) = my(f = factor(n)[,1]); sum(i = 1, #f, n / f[i]);
decide(S, q) = {
  my(D = prod(i = 1, #S, S[i]), N = dd(D), A = N + 2*D, B = N - 2*D, u = A*q + D, v = B*q + D, x, y, out = []);
  if(v < 0 || !issquare(u, &x) || !issquare(v, &y), return([0, []]));
  foreach([[(x+y)/2, (x-y)/2], [(x-y)/2, (x+y)/2]], c,
    my(qa = c[1], be = c[2]);
    if(denominator(qa) == 1 && denominator(be) == 1 && be > 0 && qa > 0 && qa % q == 0,
      my(al = qa / q);
      if(al > 0 && D % al == 0 && D / al == be && dd(be) == q*al && be - al == q*dd(al),
        out = concat(out, [[al, be]]))));
  [1, out];
}
\\ controls
{my(r = decide([2,3,5], 1)); print("positive control {2,3,5}, q=1: squares=", r[1], " splits=", r[2]);
 if(r[1] != 1 || #r[2] < 1, error("positive control failed"));
 my(r2 = decide([2,3,7,41], 1)); print("positive control {2,3,7,41}, q=1: squares=", r2[1], " splits=", r2[2]);
 if(r2[1] != 1 || #r2[2] < 1, error("positive control failed"));
 my(neg = 0); for(q = 2, 2000, if(decide([2,3,5], q)[1], neg++)); print("negative scan {2,3,5}, q in [2,2000]: square hits=", neg);}
BASES = "bases.txt"; RESULTS = "results.txt";
{my(B = Map(), f, s, nb = 0, nq = 0, nsq = 0, ncyc = 0);
 f = fileopen(BASES); while(s = filereadstr(f), my(v = eval(concat(["[", strjoin(strsplit(s, " "), ","), "]"]))); mapput(B, v[1], v[5..#v])); fileclose(f);
 f = fileopen(RESULTS);
 while(s = filereadstr(f),
   my(t = strsplit(s, " list=")); if(#t < 2, next);
   my(idx = eval(strsplit(strsplit(s, "base=")[2], " ")[1]), L = eval(strsplit(t[2], " secs")[1]), S = mapget(B, idx));
   nb++;
   for(i = 1, #L, nq++; my(r = decide(S, L[i])); if(r[1], nsq++; print("SQUARES base=", idx, " q=", L[i], " splits=", r[2])); if(#r[2], ncyc++; print("CYCLE CANDIDATE base=", idx, " q=", L[i], " isprime(q)=", isprime(L[i])))));
 fileclose(f);
 print("bases read=", nb, "  survivors tested=", nq, "  both squares=", nsq, "  exact splits=", ncyc);}
quit;
