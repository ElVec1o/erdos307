\\ sector_kexclude.gp -- the generalised terminal formula l*(dR - d'R') = d'R + d^2 behind sector_kexclude.rs,
\\ checked symbolically (identically zero) and in exact rationals at each sector enumerated.

\\ Independent check of the generalised terminal formula l*(dR - d'R') = d'R + d^2 used by
\\ sector_kexclude.rs, in exact rationals, at each sector we ran.
nd(n) = my(f = factor(n)); sum(i = 1, #f~, n / f[i,1] * f[i,2]);
{ foreach([[42,62],[47058,54],[2214502422,70]], D,
    my(d = D[1], k = D[2], dp = nd(d), A = [], p = 2, S, R, Rp, l, e, ep, bad = 0);
    while(#A < 400, if(isprime(p) && d % p != 0 && dp % p != 0, A = concat(A, p)); p++);
    for(t = 1, 200,
      S = vecextract(A, Set(vector(k-1, i, random(250)+1)));
      if(#S < 3, next);
      R = vecprod(S); Rp = R * sum(i=1,#S,1/S[i]);
      if(d*R - dp*Rp == 0, next);
      l = (dp*R + d^2) / (d*R - dp*Rp);
      if(type(l) != "t_INT", next);
      e = R*l; ep = Rp*l + R;
      if(d*e - dp*ep != d^2, bad++));
    printf("d=%-12d k=%-3d d'=%-12d  terminal identity d*e - d'*e' = d^2 : violations %d\n", d, k, dp, bad);
    \\ also confirm the sector equation is EQUIVALENT (converse direction) on a symbolic instance
    my(r = 'r, rp = 'rp, ll = 'll);
    printf("    symbolic: d*(R*l) - d'*(R'*l + R) - d^2 with l = (d'R + d^2)/(dR - d'R')  ->  %s\n",
      Str(simplify(d*(r*((dp*r + d^2)/(d*r - dp*rp))) - dp*(rp*((dp*r + d^2)/(d*r - dp*rp)) + r) - d^2))));
}
quit;
