\\ Bado: a = q d, b = e, with e = d + q d' and e' = q d.  The paper (prop:tailbound): D = prod S = d e,
\\ N = D' = d' e + d e', and the tail prime is a root of alpha^2 q^2 - N q + (beta^2 - D) = 0 with
\\ alpha beta = D.  Claim: alpha = d, beta = e.  Treat d, d' (=dd), q as free symbols and check that
\\ Bado's relations force the paper's quadratic at alpha = d, and its discriminant square.
{
my(d, dd, q, e, N, D, quad, disc, k);
d = 'd; dd = 'dd; q = 'q;
e = d + q*dd;                        \\ Bado, Cor 3.2
N = dd*e + d*(q*d);                  \\ Leibniz, using e' = q d
D = d*e;
quad = d^2*q^2 - N*q + (e^2 - D);    \\ paper's quadratic at alpha = d, beta = e
disc = N^2 - 4*D^2 + 4*d^2*D;        \\ paper's discriminant at alpha = d
k    = 2*q*d^2 - N;                  \\ paper's k
print("paper's quadratic at alpha=d, given Bado's relations:  ", simplify(quad));
print("k^2 - disc                                        :  ", simplify(k^2 - disc));
print("(both must be identically 0)");
}
quit;
