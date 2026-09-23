\\ Weighted derivative D_w(n) = sum_{p|n} w_p n/p, w_p in {-2,-1,1,2}, on squarefree n.
\\ Collect two-cycles D_w(a) = b, D_w(b) = a (a, b coprime squarefree, a <= AMAX) as data for
\\ testing candidate divisibility relations between a and b. Output data/twisted/weighted_cycles_signed.txt.
AMAX = 100000; out = "data/twisted/weighted_cycles_signed.txt";
hit(b, a) = {  \\ is there a weighting v_q in {-2,-1,1,2} of primes(b) with sum v_q b/q = a ?
  my(f = factor(b)[,1], k = #f);
  forvec(e = vector(k, i, [1,4]), if(sum(i=1,k,[-2,-1,1,2][e[i]]*b/f[i]) == a, return(1)));
  0;
}
{for(a = 2, AMAX, if(!issquarefree(a), next);
  my(f = factor(a)[,1], k = #f);
  forvec(w = vector(k, i, [1,4]),
    my(ww = apply(x -> [-2,-1,1,2][x], w), b = sum(i=1,k,ww[i]*a/f[i]));
    if(b > 1 && b != a && issquarefree(b) && gcd(a,b) == 1 && hit(b, a),
      write(out, [a, b, ww~]))));}
quit;
