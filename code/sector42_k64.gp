\\ sector42_k64.gp -- exact rational facts behind sector42_k64.rs: the case split (at most two primes > 1229 in a
\\ 64-set), the phase windows, and the terminal formula l = (41R+1764)/(42R-41R') as a rational identity.

{ my(A = [], p = 5, T = 42/41, S61, S62, S63, N = 197);
  while(#A < 400, if(isprime(p) && p != 7 && p != 41, A = concat(A, p)); p++);
  S61 = sum(j=1,61, 1/A[j]); S62 = sum(j=1,62, 1/A[j]); S63 = sum(j=1,63, 1/A[j]);
  print("A_61..A_64 = ", [A[61],A[62],A[63],A[64]], "   A_N=", A[N], "  A_(N+1)=", A[N+1]);
  print("S61 < 42/41 : ", S61 < T, "    S62 >= 42/41 : ", S62 >= T, "   (2 large primes never excluded by mass)");
  print("m=3 excluded: S61 + 3/A_(N+1) < 42/41 : ", S61 + 3/A[N+1] < T, "   margin = ", 1.0*(T - S61 - 3/A[N+1]));
  print("phase-1 window lo = 42/41 - 1/A_64 = ", 1.0*(T - 1/A[64]), "   phase-2 lo = 42/41 - 2/A_(N+1) = ", 1.0*(T - 2/A[N+1]));
  my(S = vecextract(A, Set(vector(63, i, random(150)+1))), R = vecprod(S), Rp = R * sum(i=1,#S, 1/S[i]), D = 42*R - 41*Rp, l, e, ep);
  l = (41*R + 1764) / D; e = R*l; ep = Rp*l + R;
  print("terminal formula (rational, random 63-set): 42e - 41e' - 1764 = ", 42*e - 41*ep - 1764);
}
quit;
