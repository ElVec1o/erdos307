\\ For each prime r | e:  e/r = e' = q d = -d^2/d'  (mod r)   [Bado I, Prop 3.5].
\\ So  prod_{s | e, s != r} s  =  -d^2/d'  (mod r),  one condition per prime of e.
\\ At d = 42: -1764/41 mod r.  Test his 62-element maximiser T at its three smallest primes.
{
my(T, c, r, P, i, ok);
T = [5, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
     97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
     179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
     269, 271, 277, 281, 283, 293, 307, 313, 373, 379];
print("Znam target c_r = -1764/41 mod r, and prod of the OTHER primes of T mod r:");
foreach([5, 11, 13, 17, 19, 23], r,
  c = lift(Mod(-1764, r) / Mod(41, r));
  P = 1; for(i = 1, #T, if(T[i] != r, P = P * T[i] % r));
  ok = if(setsearch(Set(T), r), if(P == c, "SATISFIED", "VIOLATED"), "r not in T");
  printf("  r=%2d   target %2d   prod_others %2d   %s\n", r, c, P, ok));
}
quit;
