{
my(dA, dB, t, la, lU_A, lU_B);
dA = 113.397;   \\ max log10 prod over the 49,961 admissible 59-supports (mass >= 2)
dB = 113.526;   \\ max log10 prod under the ladder with mass < 2
t  = 1.102008;  \\ mass-window root at T_61
print("LEVEL 61 HEIGHT.");
print("");
print("Delta = MN - M'N' = D(1 - sigma(P0)sigma(Q0)) > 0 since sigma(P0)sigma(Q0) < sigma(P)sigma(Q) = 1,");
print("and Delta is an integer, so Delta >= 1.");
print("MN = D exactly (P0, Q0 complementary), so MN' = D sigma(Q0) <= ", t, " D.");
print("Hence alpha = (MN' + N^2)/Delta <= D^2 + 1.11 D, and likewise beta.");
print("");
la = 2*dA + log(1 + 1.11/10^dA)/log(10);
printf("case A (bottom 59 of mass >= 2): log10 D <= %.3f\n", dA);
printf("  log10 alpha, beta <= %.2f\n", la);
lU_A = dA + 2*la;
printf("  log10 prod U      <= %.2f\n", lU_A);
print("");
lU_B = dB + (dB + log(2.0)/log(10)) + (2*dB + log(2.22)/log(10));
printf("case B (bottom 59 of mass < 2): log10 D <= %.3f\n", dB);
printf("  u_60 <= 2D, u_61 <= 1.11 D u_60  ->  log10 prod U <= %.2f\n", lU_B);
print("");
printf("LEVEL 61: prod U < 10^%d in both cases\n", ceil(max(lU_A, lU_B)));
print("");
print("consistency with the barrier: prod U = prod P * prod Q >= (2.09e56)^2 = 10^112.6");
printf("so the level-61 window is 10^112.6 <= prod U < 10^%d\n", ceil(max(lU_A,lU_B)));
}
quit;
