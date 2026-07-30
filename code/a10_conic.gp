\\ a10_conic.gp -- attack prop:untestable via Hasse-Minkowski instead of the class group.
\\
\\ prop:untestable said solving B x^2 - A y^2 = -4 D^2 needs the fundamental unit of the order of
\\ discriminant 4AB (225 digits), costing L(1/2) ~ 1e24.7. But homogenised,
\\     B x^2 - A y^2 + 4 D^2 z^2 = 0
\\ is a TERNARY QUADRATIC FORM, i.e. a conic, and conics satisfy Hasse-Minkowski: a rational point
\\ exists iff one exists everywhere locally, which prop:tier60 already gives (kappa_S > 0). Simon's
\\ algorithm (PARI qfsolve) finds such a point in time polynomial in the input GIVEN the
\\ factorisation of the coefficients -- and we have it: A_S and B_S are prime and D_S is a known
\\ product of 59 primes. No class group is required.
default(parisize, 2000000000);
P = primes([2,800]); T58 = sum(i=1,58,1/P[i]);
forc = select(x -> x <= 167, P);
pool = select(x -> x > 167 && T58 + 1/x > 2, P);
np = #pool; kk = 59 - #forc; thr = 2 - sum(i=1,#forc,1/forc[i]);
pf = vector(np,i,1/pool[i]); cum = vector(np+1); cum[1]=0;
for(i=1,np, cum[i+1]=cum[i]+pf[i]);
bases = List();
dfs(i,need,cur,ch) = {
  if(need==0, if(cur>thr, listput(bases,ch)); return());
  if(i+need>np+1, return());
  if(cur + (cum[min(i+need,np+1)]-cum[i]) <= thr, return());
  dfs(i+1,need-1,cur+pf[i],concat(ch,[i])); dfs(i+1,need,cur,ch);
};
dfs(1,kk,0,[]);
imm = List();
{
for(j=1,#bases,
  S = concat(forc, vector(#bases[j],t,pool[bases[j][t]]));
  D = prod(t=1,#S,S[t]); N = sum(t=1,#S, D \ S[t]);
  A = N+2*D; B = N-2*D;
  if(ispseudoprime(A) && ispseudoprime(B) && kronecker(D,A)==1, listput(imm,[S,D,A,B]));
);
}
printf("immune families: %d\n", #imm);
S = imm[1][1]; D = imm[1][2]; A = imm[1][3]; B = imm[1][4];

\\ the conic  B x^2 - A y^2 + 4 D^2 z^2 = 0
G = matdiagonal([B, -A, 4*D^2]);
printf("conic diag(B, -A, 4 D^2), entries of %d / %d / %d digits\n", #digits(B), #digits(A), #digits(4*D^2));
t0 = getabstime();
sol = qfsolve(G);
t1 = getabstime();
printf("qfsolve returned in %.2fs\n", (t1-t0)/1000.0);
{ if(type(sol) == "t_INT",
    printf("NO rational point: local obstruction at %s\n", sol)
  ,
    printf("RATIONAL POINT FOUND\n");
    x = sol[1]; y = sol[2]; z = sol[3];
    printf("  x has %d digits, y has %d digits, z has %d digits\n", #digits(x), #digits(y), #digits(z));
    printf("  residual B x^2 - A y^2 + 4 D^2 z^2 = %d  (must be 0)\n", B*x^2 - A*y^2 + 4*D^2*z^2);
    printf("  z = 0 ?  %d   (z != 0 is what gives an affine solution)\n", z == 0);
    if(z != 0,
      q = (x^2/z^2 - D)/A;
      printf("  q = (x/z)^2 - D)/A  is an integer? %d\n", denominator(q) == 1);
      printf("  q > 0 ? %d\n", q > 0);
    );
  );
}
quit;
