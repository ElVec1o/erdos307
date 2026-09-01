\\ Bado's primary-pseudoperfect apparatus, generalised: everywhere he writes d-1, the correct
\\ general object is d'.  For primary pseudoperfect d these agree (d' = d-1), which is why the
\\ specialisation looked special.  Checks, with d, dd = d', q, R, RR = R', r free symbols:
\\   (i)   the fundamental sector identity   d e - d' e' = d^2      [his (4) with d-1 -> d']
\\   (ii)  the defect recurrence             D(Rr) = r D(R) - d' R  [his (10)]
\\   (iii) the terminal value                D(e) = d^2             [his Prop 4.1]
\\ where e = d + q d', e' = q d, D(R) = d R - d' R', and (Rr)' = r R' + R for r not dividing R.
{
my(d, dd, q, R, RR, r, e, ee, DR, DRr);
d = 'd; dd = 'dd; q = 'q; R = 'R; RR = 'RR; r = 'r;
e  = d + q*dd;
ee = q*d;
print("(i)   d e - d' e' - d^2            = ", simplify(d*e - dd*ee - d^2));
DR  = d*R - dd*RR;
DRr = d*(R*r) - dd*(r*RR + R);
print("(ii)  D(Rr) - ( r D(R) - d' R )    = ", simplify(DRr - (r*DR - dd*R)));
print("(iii) D(e) - d^2  [R=e, R'=e']     = ", simplify((d*e - dd*ee) - d^2));
print("(all three must be identically 0)");
print("");
print("and the mass identity  sum_{r|e} 1/r = d/d' - d^2/(d' e):");
print("      e'/e - ( d/dd - d^2/(dd*e) )  = ", simplify(ee/e - (d/dd - d^2/(dd*e))));
}
quit;
