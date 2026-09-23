\\ Auxiliary-modulus test on the Z[sqrt2] twisted two-cycles (code/hunt/real_hits.txt).
\\ Unit-invariant data per cycle: A = |N(prod a-classes)|, B = |N(b)|. Statistics compared against a
\\ control of random coprime squarefree pairs (A0, B0) with the same sizes (Rule 25).
\\  s1: share of odd primes q | B with (A|q) = +1       (control: 1/2)
\\  s2: share of pairs with ell | A - B, for ell = 3,5,7   (control: 1/ell)
\\  s3: share of pairs with ell | A + B, for ell = 3,5,7
nrm(v) = abs(v[1]^2 - 2*v[2]^2);
parsepairs(s) = my(v = [], t = strsplit(s, "("), i); for(i = 2, #t, my(u = strsplit(strsplit(t[i], ")")[1], ",")); v = concat(v, [[eval(u[1]), eval(u[2])]])); v;
L = [];
{my(f = fileopen("code/hunt/real_hits.txt"), s);
 while(s = filereadstr(f),
   if(#strsplit(s, "TWISTED 2-CYCLE") < 2, next);
   my(pa = strsplit(strsplit(s, "a-classes ")[2], " code")[1], pb = strsplit(strsplit(s, "b=a'=")[2], " b-classes")[1]);
   my(ac = parsepairs(pa), bv = parsepairs(pb)[1], A = prod(i = 1, #ac, nrm(ac[i])), B = nrm(bv));
   if(A > 1 && B > 1, L = concat(L, [[A, B]])));
 fileclose(f);}
stats(P) = {
  my(qr = 0, qt = 0, dm = vector(3), dp = vector(3), ls = [3,5,7]);
  for(i = 1, #P, my(A = P[i][1], B = P[i][2], f = factor(B)[,1]);
    for(j = 1, #f, my(q = f[j]); if(q > 2 && A % q, qt++; if(kronecker(A, q) == 1, qr++)));
    for(k = 1, 3, if((A - B) % ls[k] == 0, dm[k]++); if((A + B) % ls[k] == 0, dp[k]++)));
  [#P, qr * 1. / qt, dm * 1. / #P, dp * 1. / #P];
}
print("cycles (raw hits): ", #L, "  with gcd(A,B) > 1 (conjugate primes shared): ", sum(i=1,#L,gcd(L[i][1],L[i][2])>1));
L = vecsort(select(v -> gcd(v[1], v[2]) == 1, L), , 8);
print("distinct coprime norm pairs: ", #L);
print("cycles  [n, s1, s2(3,5,7), s3(3,5,7)]: ", stats(L));
setrand(307);
\\ control: norms of random elements x + y sqrt2 of the same size, coprime pair (norms carry the same
\\ splitting bias as the cycles: inert primes 3, 5 appear only squared).
rnd(N) = {my(x, y, v); until(v > 1, y = random(sqrtint(N) + 2); x = sqrtint(2*y^2 + N) + random(3) - 1; v = abs(x^2 - 2*y^2)); v};
{C = vector(#L, i, my(A, B); until(gcd(A, B) == 1, A = rnd(L[i][1]); B = rnd(L[i][2])); [A, B]);}
print("control [n, s1, s2(3,5,7), s3(3,5,7)]: ", stats(C));
cond(P, l) = my(S = select(v -> (v[1]*v[2]) % l, P)); [l, #S, sum(i=1,#S,(S[i][1]-S[i][2])%l==0)*1./max(#S,1), sum(i=1,#S,(S[i][1]+S[i][2])%l==0)*1./max(#S,1)];
print("conditional on l not dividing AB: [l, n, P(l | A-B), P(l | A+B)]");
{foreach([3,5,7,17,23,31], l, print("  cycles  ", cond(L, l), "   control ", cond(C, l)));}
quit;
