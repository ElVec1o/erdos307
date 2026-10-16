import Erdos307.Certificate

/-!
# A Jacobi-symbol algorithm with a soundness theorem, and the divisor kill

`jacF` computes `J(a | n)` for odd `n` by the binary algorithm (strip factors of `2`, then quadratic
reciprocity), with a fuel counter and `Option` result: `jacF f a n = some r → J(a | n) = r`. Fuel
exhaustion returns `none`, so no sufficiency proof is needed; the evaluation decides.

`kill_of_divisor`: if `d ∣ A` and `J(D | d) = -1`, then `x² = A q + D` has no solution for any `q`.
No factorisation or primality is needed: a Jacobi symbol `-1` hides a prime divisor with Legendre
symbol `-1` (`jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one`).

Paper: Proposition `prop:tailkill`.
-/

open scoped NumberTheorySymbols

namespace Erdos307

def sign2 (n : ℕ) : ℤ := if n % 8 = 3 ∨ n % 8 = 5 then -1 else 1

def qsign (a n : ℕ) : ℤ := if a % 4 = 3 ∧ n % 4 = 3 then -1 else 1

def jacF : ℕ → ℕ → ℕ → Option ℤ
  | 0, _, _ => none
  | f + 1, a, n =>
    if a = 0 then some (if n = 1 then 1 else 0)
    else if a % 2 = 0 then (jacF f (a / 2) n).map (· * sign2 n)
    else (jacF f (n % a) a).map (· * qsign a n)

theorem jacF_sound : ∀ (f a n : ℕ) (r : ℤ), n % 2 = 1 → jacF f a n = some r → J(a | n) = r := by
  intro f
  induction f with
  | zero => intro a n r _ h; simp [jacF] at h
  | succ f ih =>
    intro a n r hn h
    have hnodd : Odd n := Nat.odd_iff.2 hn
    unfold jacF at h
    by_cases ha0 : a = 0
    · subst ha0
      simp only [if_true, Option.some.injEq] at h
      subst h
      by_cases hn1 : n = 1
      · subst hn1; simp [jacobiSym.one_right]
      · have : 1 < n := by
          rcases Nat.lt_or_ge 1 n with h1 | h1
          · exact h1
          · exfalso; interval_cases n <;> simp_all
        simp [hn1, jacobiSym.zero_left this]
    · by_cases ha2 : a % 2 = 0
      · simp only [if_neg ha0, if_pos ha2] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
        have := ih (a / 2) n r' hn hr'
        have hmul : ((a : ℕ) : ℤ) = 2 * ((a / 2 : ℕ) : ℤ) := by omega
        rw [hmul, jacobiSym.mul_left, jacobiSym.at_two hnodd, this, ZMod.χ₈_nat_eq_if_mod_eight]
        simp only [sign2]
        have hn2 : n % 2 ≠ 0 := by omega
        simp only [if_neg hn2]
        by_cases h8 : n % 8 = 3 ∨ n % 8 = 5
        · have : ¬ (n % 8 = 1 ∨ n % 8 = 7) := by omega
          simp [h8, this, mul_comm]
        · have : (n % 8 = 1 ∨ n % 8 = 7) := by omega
          simp [h8, this, mul_comm]
      · simp only [if_neg ha0, if_neg ha2] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
        have hao : a % 2 = 1 := by omega
        have := ih (n % a) a r' hao hr'
        have hmod : J(n | a) = r' := by
          rw [jacobiSym.mod_left]; push_cast [Int.natCast_mod] at this ⊢; exact this
        have haodd : Odd a := Nat.odd_iff.2 hao
        simp only [qsign]
        by_cases h33 : a % 4 = 3 ∧ n % 4 = 3
        · rw [if_pos h33, jacobiSym.quadratic_reciprocity_three_mod_four h33.1 h33.2, hmod]; ring
        · rw [if_neg h33]
          by_cases h1 : a % 4 = 1
          · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hnodd, hmod]; ring
          · have h1' : n % 4 = 1 := by omega
            rw [jacobiSym.quadratic_reciprocity_one_mod_four' haodd h1', hmod]; ring

/-- **The divisor kill.** `d ∣ A` and `J(D | d) = -1` make `x² = A q + D` unsolvable. -/
theorem kill_of_divisor {A D : ℤ} {d : ℕ} (hd : (d : ℤ) ∣ A) (hJ : J(D | d) = -1) (x q : ℤ) :
    x ^ 2 ≠ A * q + D := by
  obtain ⟨l, hl, hld, hJl⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hJ
  haveI : Fact l.Prime := ⟨hl⟩
  have hL : legendreSym l D = -1 := (jacobiSym.legendreSym.to_jacobiSym l D).trans hJl
  exact certificate_sound l D A hL ((Int.natCast_dvd_natCast.2 hld).trans hd) x q

/-- The check used in the compiled kill: `d ∣ A` and the algorithm returns `-1` for `D mod d`. -/
def killCheck (A D d fuel : ℕ) : Bool :=
  d % 2 == 1 && A % d == 0 && jacF fuel (D % d) d == some (-1)

theorem killCheck_sound {A D d fuel : ℕ} (h : killCheck A D d fuel = true) (x q : ℤ) :
    x ^ 2 ≠ (A : ℤ) * q + D := by
  unfold killCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hd2, hdA⟩, hj⟩ := h
  have hJ : J((D : ℤ) | d) = -1 := by
    rw [jacobiSym.mod_left]
    have := jacF_sound fuel (D % d) d (-1) hd2 hj
    push_cast [Int.natCast_mod] at this ⊢; exact this
  exact kill_of_divisor (Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero hdA)) hJ x q

end Erdos307
