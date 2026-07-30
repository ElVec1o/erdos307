\\ a10_pell_feasibility.gp -- can the 34 immune families actually be TESTED?
\\
\\ rem:lehmer: a Pythagorean pair in the tail family S u {q} is exactly a solution of
\\     B_S x^2 - A_S y^2 = -4 D_S^2,   q = (x^2 - D_S)/A_S = (y^2 - D_S)/B_S  a positive prime.
\\ The 34 immune families are the only ones the congruence campaign cannot kill, so each is a live
\\ candidate and "just check them" is the obvious attack. This script measures whether that attack
\\ is available at all. Two routes, both quantified:
\\   (1) solve the Pell system -- needs the fundamental unit / class group of the real quadratic
\\       order of discriminant 4 A_S B_S;
\\   (2) parametrise by x = x0 + t A_S (legitimate: A_S is prime and (D_S|A_S) = +1, so sqrt(D_S)
\\       exists mod A_S) and search t, checking whether B_S q(t) + D_S is a square.
default(parisize, 1000000000);
P = primes([2,800]); T58 = sum(i=1,58,1/P[i]);
forc = select(x -> x <= 167, P);
pool = select(x -> x > 167 && T58 + 1/x > 2, P);
np = #pool; kk = 59 - #forc; thr = 2 - sum(i=1,#forc,1/forc[i]);
pf = vector(np, i, 1/pool[i]); cum = vector(np+1); cum[1]=0;
for(i=1,np, cum[i+1]=cum[i]+pf[i]);
bases = List();
dfs(i, need, cur, ch) = {
  if(need == 0, if(cur > thr, listput(bases, ch)); return());
  if(i + need > np+1, return());
  if(cur + (cum[min(i+need,np+1)] - cum[i]) <= thr, return());
  dfs(i+1, need-1, cur+pf[i], concat(ch,[i])); dfs(i+1, need, cur, ch);
};
dfs(1, kk, 0, []);
imm = List();
{
for(j=1, #bases,
  S = concat(forc, vector(#bases[j], t, pool[bases[j][t]]));
  D = prod(t=1,#S,S[t]); N = sum(t=1,#S, D \ S[t]);
  A = N + 2*D; B = N - 2*D;
  if(ispseudoprime(A) && ispseudoprime(B) && kronecker(D,A)==1, listput(imm,[D,A,B]));
);
}
printf("immune families: %d\n\n", #imm);
D = imm[1][1]; A = imm[1][2]; B = imm[1][3];
disc = 4*A*B;
{ printf("first immune base:  D_S %d digits,  A_S %d digits,  B_S %d digits\n", #digits(D), #digits(A), #digits(B)); }
{ printf("Pell discriminant 4 A_S B_S : %d digits,  nonsquare: %d\n", #digits(disc), !issquare(disc)); }

\\ (1) cost of the class-group / fundamental-unit route: L_Delta(1/2) = exp(sqrt(ln D * lnln D))
ld = log(disc*1.0); lld = log(ld);
{ printf("\n(1) fundamental-unit / class-group route: L(1/2) = exp(sqrt(ln(disc) * lnln(disc))) = 10^%.1f operations\n", sqrt(ld*lld)/log(10)); }

\\ (2) parametrised search: q(t) = ((x0 + t A)^2 - D)/A, need B q(t) + D to be a SQUARE
x0 = lift(sqrt(Mod(D, A)));
{ printf("\n(2) parametrised search legitimate: x0^2 = D mod A_S ? %d   (A_S prime, (D_S|A_S)=+1)\n", Mod(x0,A)^2 == Mod(D,A)); }
{
for(t = 0, 3,
  q = ((x0 + t*A)^2 - D)/A;
  v = B*q + D;
  printf("    t=%d : q has %d digits,  B q + D has %d digits,  square? %d\n",
         t, #digits(q), #digits(v), issquare(v));
);
}
v = B*(((x0 + 1*A)^2 - D)/A) + D;
printf("    heuristic P(square) per trial ~ 1/sqrt(B q + D) = 10^-%d\n", (#digits(v))\2);
printf("\n  => neither route is available.\n");
quit;
