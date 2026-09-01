{
my(L, r, ratio);
print("the true wall: sqrt(r) log L / L at r ~ (log N)^{1/2} = e^{L/2}, needs -> 0:");
foreach([5.0, 14.0, 28.0, 69.0], L,
  r = exp(L/2);
  ratio = sqrt(r)*log(L)/L;
  printf("  L=%5.1f (N ~ 10^%.0f)   sqrt(r) log L / L = %12.2f\n", L, exp(L)/log(10), ratio));
print("");
print("even with an O(1) per-character bound the requirement is sqrt(r) = o(L), so P = o(L):");
foreach([5.0, 14.0, 28.0], L,
  printf("  L=%5.1f   needed P ~ (log N)^{1/4} = %10.2f   available P = o(L) = %6.1f\n",
         L, exp(L/4), L));
}
quit;
