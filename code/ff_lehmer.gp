/* ff_lehmer.gp -- the function-field analogue of the Lehmer question (I9 toy universe).
 *
 * Over Z the residue of #307 is: does a determined term q_n of a Pell orbit ever come out PRIME?
 * That is open for every exponential sequence. Change the point of view: ask the same question in
 * F_p[t], where the project already works (thm:ff) and where counting is governed by Weil rather
 * than by conjecture.
 *
 * Faithful analogue: take D non-square in F_p[t] of even degree with square leading coefficient, a
 * solution X^2 - D Y^2 = 1, and the orbit (X + Y sqrt(D))^n, whose x-coordinates satisfy
 *      x_{n+1} = (2X) x_n - x_{n-1},     x_0 = 1, x_1 = X.
 * Then ask whether x_n is IRREDUCIBLE for some n. Both answers are informative: abundance says the
 * obstruction over Z is analytic rather than structural, absence would say we have missed a
 * structural obstruction that would apply over Z too.
 */
{
for(pi = 1, 3,
  my(p = [3,5,7][pi]);
  my(D = Mod(1,p)*(t^2+1), X, Y, found = 0);
  /* find a small solution X^2 - D Y^2 = 1 by search over low-degree Y */
  for(dy = 1, 3,
    if(found, break);
    forvec(v = vector(dy+1, i, [0, p-1]),
      my(Yc = Mod(1,p)*sum(i=1, dy+1, v[i]*t^(i-1)));
      if(Yc == 0, next);
      my(R = 1 + D*Yc^2);
      if(issquare(R, &X), Y = Yc; found = 1; break);
    );
  );
  if(!found, print("p = ", p, ": no small Pell solution found"); next);
  printf("\np = %d,  D = t^2+1,  X = %s,  Y = %s   (X^2 - D Y^2 = %s)\n",
         p, lift(X), lift(Y), lift(X^2 - D*Y^2));
  my(x0 = Mod(1,p)*1, x1 = X, tw = 2*X, irr = 0, tested = 0);
  print("   n   deg(x_n)   irreducible?   factor degrees");
  for(n = 1, 24,
    my(xn = if(n == 1, x1, 0));
    if(n > 1,
      my(a = x0, b = x1);
      for(k = 2, n, my(c = tw*b - a); a = b; b = c);
      xn = b;
    );
    tested++;
    my(f = factor(xn), degs = vector(#f~, i, poldegree(f[i,1])), isirr = (#f~ == 1 && f[1,2] == 1));
    if(isirr, irr++);
    if(n <= 12 || isirr,
      printf("  %2d   %6d   %-12s  %s\n", n, poldegree(xn), if(isirr,"YES","no"), degs);
    );
  );
  printf("  --> %d of %d terms irreducible over F_%d\n", irr, tested, p);
);
}
quit;
