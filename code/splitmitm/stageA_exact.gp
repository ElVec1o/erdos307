\\ stageA_exact.gp -- exact audit of split_mitm.rs output (results.txt in the run directory).
\\ (1) Every reported split T is re-decided by the single equation: a two-cycle on S u {q} with a = q*alpha exists iff
\\     alpha^2 + alpha'*beta' = D (alpha = prod T, beta = D/alpha) and q = beta'/alpha is a prime > max S.
\\ (2) Coverage: every base of bases.txt has exactly one DONE line; totals of candidates and (*)-hits are summed.
\\ Controls: {2,3,5}/T={5} satisfies the equation with q = 1 (not a prime tail); random splits of the first base fail it.
dd(n) = if(n == 1, 0, my(f = factor(n)[,1]); sum(i = 1, #f, n / f[i]));
decideT(S, T) = { my(D = prod(i=1,#S,S[i]), al = prod(i=1,#T,T[i]), be = D/al, eq, q);
  if(denominator(be) != 1, return("T not in S"));
  eq = (al^2 + dd(al)*dd(be) == D); if(!eq, return("fails equation"));
  if(dd(be) % al, return("equation holds, beta'/alpha not integral"));
  q = dd(be)/al; if(q < 3 || !isprime(q) || q <= vecmax(S), return(Str("equation holds, q=", q, " is not a prime tail")));
  Str("TWO-CYCLE q=", q); }
print("control {2,3,5}, T={5}: ", decideT([2,3,5], [5]));
BASES = "bases.txt"; RESULTS = "results.txt";
{my(B = Map(), f, s, S1 = 0, nb = 0, seen = Map(), ndone = 0, dup = 0, cand = 0, eqs = 0, hits = 0, bad = 0);
 f = fileopen(BASES); while(s = filereadstr(f), my(v = eval(concat(["[", strjoin(strsplit(s, " "), ","), "]"])));
   nb++; mapput(B, v[1], v[5..#v]); if(S1 == 0, S1 = v[5..#v])); fileclose(f);
 setrand(307); my(neg = 0); for(k = 1, 200, my(T = select(x -> random(2), S1)); if(#T > 0 && #T < #S1 && decideT(S1, T) != "fails equation", neg++));
 print("negative control: random splits of the first base passing the equation: ", neg, " of 200");
 f = fileopen(RESULTS);
 while(s = filereadstr(f),
   if(#strsplit(s, "DONE base=") > 1,
     my(idx = eval(strsplit(strsplit(s, "DONE base=")[2], " ")[1]));
     if(mapisdefined(seen, idx), dup++, mapput(seen, idx, 1)); ndone++;
     my(c = strsplit(s, "cand="), e = strsplit(s, " eq="));
     if(#c > 1, cand += eval(strsplit(c[2], " ")[1])); if(#e > 1, eqs += eval(strsplit(e[2], " ")[1]));
     next);
   my(t = strsplit(s, " T="));
   if(#t > 1,
     my(idx = eval(strsplit(strsplit(s, "base=")[2], " ")[1]), T = eval(concat(["[", strsplit(t[2], " ")[1], "]"])), r);
     r = decideT(mapget(B, idx), T); print("reported base=", idx, " T=", T, " -> ", r);
     if(#strsplit(r, "TWO-CYCLE") > 1, hits++); if(r == "fails equation", bad++)));
 fileclose(f);
 print("bases in list: ", nb, "  DONE lines: ", ndone, "  duplicates: ", dup, "  missing: ", nb - #seen);
 print("candidates: ", cand, "  (*)-hits reported: ", eqs, "  exact two-cycles: ", hits, "  reported but failing equation: ", bad);}
quit;
