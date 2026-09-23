import Erdos307.PrattN10
import Erdos307.Frame

/-!
# `N_10` admits no one- or two-prime inheritance (Erdős #313)

`N_10 = N_9 (N_9 + 1)` is the ten-prime-factor primary pseudoperfect number of Wang
(arXiv:2605.21518). In the `Finset` model a primary pseudoperfect product is `csum S = dprod S - 1`.
Appending primes to its support never gives another one:

* one prime `p`: the equation forces `p = N_10 + 1`, which is divisible by `7`;
* two primes `p, q`: it forces `(p - N_10)(q - N_10) = N_10 ^ 2 + 1`, and
  `N_10 ^ 2 + 1 = 21807157 * 480382349 * P60` with all three prime, so the smaller factor is one of
  `1, 21807157, 480382349, 21807157 * 480382349`, and `N_10` plus each of these is divisible by
  `7, 7, 5, 2141` respectively.

The central idea is that inheritance is a *factorisation* problem, not a search: the two new primes
are pinned to a divisor pair of one fixed integer, so exhausting that integer's divisors decides the
question. Paper: `prop:ppninherit`. Data: `code/ppn_inherit.py`, `code/pratt_n10.gp`.
-/

namespace Erdos307

/-- The support of `N_10`. -/
def S10 : Finset ℕ := {2, 3, 11, 17, 101, 157, 1979, 10093, 16879, 5998279018951962403}

/-- `N_10`. -/
def K10 : ℕ := 35979351189199316534587473905773572006

theorem S10_prime : ∀ p ∈ S10, p.Prime := by
  intro p hp
  simp only [S10, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact prime_c10 | norm_num
theorem dprod_S10 : dprod S10 = K10 := by
  simp [dprod, S10, K10]
theorem csum_S10 : csum S10 = K10 - 1 := by
  rw [csum, dprod_S10]; simp [S10, K10]

/-- **No one-prime inheritance.** -/
theorem N10_no_one_prime (p : ℕ) (hp : p.Prime) (hpS : p ∉ S10) :
    csum (S10 ∪ {p}) ≠ dprod (S10 ∪ {p}) - 1 := by
  intro h
  rw [csum_insert_prime hpS hp.pos, dprod_insert_prime hpS, csum_S10, dprod_S10,
    Nat.mul_sub_one, Nat.mul_comm p K10] at h
  have hK : 1 ≤ K10 := by norm_num [K10]
  have hle : p ≤ K10 * p := Nat.le_mul_of_pos_left p (by norm_num [K10])
  generalize K10 * p = X at h hle
  have hpK : p = K10 + 1 := by omega
  have h7 : 7 ∣ p := by rw [hpK]; norm_num [K10]
  rcases hp.eq_one_or_self_of_dvd 7 h7 with h | h
  · norm_num at h
  · rw [hpK] at h; norm_num [K10] at h

/-- The two-prime equation is the factorisation `(p - K)(q - K) = K^2 + 1`. -/
theorem two_prime_factor (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpS : p ∉ S10)
    (hqS : q ∉ S10) (h : csum (S10 ∪ {p} ∪ {q}) = dprod (S10 ∪ {p} ∪ {q}) - 1) :
    ((p : ℤ) - K10) * ((q : ℤ) - K10) = (K10 : ℤ) ^ 2 + 1 := by
  have hqT : q ∉ S10 ∪ {p} := by simp [hqS, Ne.symm hpq]
  rw [csum_insert_prime hqT hq.pos, dprod_insert_prime hqT, csum_insert_prime hpS hp.pos,
    dprod_insert_prime hpS, csum_S10, dprod_S10] at h
  have hK : 1 ≤ K10 := by norm_num [K10]
  have hX : 1 ≤ K10 * p * q := Nat.mul_pos (Nat.mul_pos (by norm_num [K10]) hp.pos) hq.pos
  zify [hK, hX] at h
  linear_combination -h

/-- Every divisor pair of `K^2 + 1` has a composite side after adding `K`. -/
theorem divisor_side_composite (d : ℕ) (hd : d ∣ K10 ^ 2 + 1) :
    ¬ (K10 + d).Prime ∨ ¬ (K10 + (K10 ^ 2 + 1) / d).Prime := by
  have hM : K10 ^ 2 + 1 = 21807157 * (480382349 *
      123572138719194583969192220095883252267503088389616114960309) := by norm_num [K10]
  rw [hM] at hd ⊢
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨c, e, hc, he, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hb
  rw [Nat.dvd_prime (by norm_num)] at ha hc
  rw [Nat.dvd_prime prime_c9] at he
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> rcases he with rfl | rfl <;>
  first
  | (left; refine Nat.not_prime_of_dvd_of_lt (m := 7) ?_ (by norm_num) ?_ <;> (norm_num [K10]; done))
  | (left; refine Nat.not_prime_of_dvd_of_lt (m := 5) ?_ (by norm_num) ?_ <;> (norm_num [K10]; done))
  | (left; refine Nat.not_prime_of_dvd_of_lt (m := 2141) ?_ (by norm_num) ?_ <;> (norm_num [K10]; done))
  | (right; refine Nat.not_prime_of_dvd_of_lt (m := 7) ?_ (by norm_num) ?_ <;> (norm_num [K10]; done))
  | (right; refine Nat.not_prime_of_dvd_of_lt (m := 5) ?_ (by norm_num) ?_ <;> (norm_num [K10]; done))
  | (right; refine Nat.not_prime_of_dvd_of_lt (m := 2141) ?_ (by norm_num) ?_ <;> (norm_num [K10]; done))

/-- **No two-prime inheritance.** -/
theorem N10_no_two_prime (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpS : p ∉ S10)
    (hqS : q ∉ S10) : csum (S10 ∪ {p} ∪ {q}) ≠ dprod (S10 ∪ {p} ∪ {q}) - 1 := by
  intro h
  have hf := two_prime_factor p q hp hq hpq hpS hqS h
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  have hK2 : (2 : ℤ) ≤ K10 := by norm_num [K10]
  rcases le_or_gt p K10 with hpK | hpK <;> rcases le_or_gt q K10 with hqK | hqK
  · -- both new primes below `K`: the product is at most `(K - 2)^2 < K^2 + 1`
    have a : (p : ℤ) ≤ K10 := by exact_mod_cast hpK
    have b : (q : ℤ) ≤ K10 := by exact_mod_cast hqK
    nlinarith [mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 b),
      mul_nonneg (sub_nonneg.2 hq2) (sub_nonneg.2 hK2)]
  · -- opposite signs: the product is non-positive
    have a : (p : ℤ) ≤ K10 := by exact_mod_cast hpK
    have b : (K10 : ℤ) < q := by exact_mod_cast hqK
    nlinarith [mul_nonneg (sub_nonneg.2 a) (sub_nonneg.2 b.le)]
  · have a : (K10 : ℤ) < p := by exact_mod_cast hpK
    have b : (q : ℤ) ≤ K10 := by exact_mod_cast hqK
    nlinarith [mul_nonneg (sub_nonneg.2 a.le) (sub_nonneg.2 b)]
  · -- both above `K`: `p - K` and `q - K` are a divisor pair of `K^2 + 1`
    obtain ⟨d, rfl⟩ : ∃ d, p = K10 + d := ⟨p - K10, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, q = K10 + e := ⟨q - K10, by omega⟩
    have hde : d * e = K10 ^ 2 + 1 := by
      have : (d : ℤ) * e = (K10 : ℤ) ^ 2 + 1 := by push_cast at hf; linarith
      exact_mod_cast this
    have hd0 : 0 < d := by omega
    have he : (K10 ^ 2 + 1) / d = e := by rw [← hde, Nat.mul_div_cancel_left e hd0]
    rcases divisor_side_composite d ⟨e, hde.symm⟩ with h1 | h1
    · exact h1 hp
    · rw [he] at h1; exact h1 hq

end Erdos307
