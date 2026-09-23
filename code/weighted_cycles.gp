\\ Weighted derivative D_w(n) = sum_{p|n} w_p n/p, w_p in {1,2}, on squarefree n.
\\ Collect two-cycles D_w(a) = b, D_w(b) = a (a, b coprime squarefree, a <= AMAX) as data for
\\ testing candidate divisibility relations between a and b. Output data/twisted/weighted_cycles.txt.
AMAX = 200000; out = "data/twisted/weighted_cycles.txt";
hit(b, a) = {  \\ is there S subset of primes(b) with sum_{q in S} b/q = a - b' ?
  my(f = factor(b)[,1], t = a - sum(i=1,#f,b/f[i]), k = #f);
  if(t < 0, return(0));
  forvec(e = vector(k, i, [0,1]), if(sum(i=1,k,e[i]*b/f[i]) == t, return(1)));
  0;
}
{for(a = 2, AMAX, if(!issquarefree(a), next);
  my(f = factor(a)[,1], k = #f);
  forvec(w = vector(k, i, [1,2]),
    my(b = sum(i=1,k,w[i]*a/f[i]));
    if(b > 1 && b != a && issquarefree(b) && gcd(a,b) == 1 && hit(b, a),
      write(out, [a, b, w~]))));}
quit;
