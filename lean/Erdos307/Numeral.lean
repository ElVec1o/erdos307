import Erdos307.Barrier
import Erdos307.Extremal

/-!
# Erdős #307 — T4′ closure: numeral bridge (first 59 primes)

`Nat.count … = …` uses `native_decide`; these lemmas (only) carry `Lean.ofReduceBool`.
All *mathematical* theorems stay 3-axiom.
-/

namespace Erdos307
open Finset

lemma np0 : Nat.nth Nat.Prime 0 = 2 := by
  have h : Nat.count Nat.Prime 2 = 0 := by native_decide
  calc Nat.nth Nat.Prime 0 = Nat.nth Nat.Prime (Nat.count Nat.Prime 2) := by rw [h]
    _ = 2 := Nat.nth_count (by norm_num)

lemma np1 : Nat.nth Nat.Prime 1 = 3 := by
  have h : Nat.count Nat.Prime 3 = 1 := by native_decide
  calc Nat.nth Nat.Prime 1 = Nat.nth Nat.Prime (Nat.count Nat.Prime 3) := by rw [h]
    _ = 3 := Nat.nth_count (by norm_num)

lemma np2 : Nat.nth Nat.Prime 2 = 5 := by
  have h : Nat.count Nat.Prime 5 = 2 := by native_decide
  calc Nat.nth Nat.Prime 2 = Nat.nth Nat.Prime (Nat.count Nat.Prime 5) := by rw [h]
    _ = 5 := Nat.nth_count (by norm_num)

lemma np3 : Nat.nth Nat.Prime 3 = 7 := by
  have h : Nat.count Nat.Prime 7 = 3 := by native_decide
  calc Nat.nth Nat.Prime 3 = Nat.nth Nat.Prime (Nat.count Nat.Prime 7) := by rw [h]
    _ = 7 := Nat.nth_count (by norm_num)

lemma np4 : Nat.nth Nat.Prime 4 = 11 := by
  have h : Nat.count Nat.Prime 11 = 4 := by native_decide
  calc Nat.nth Nat.Prime 4 = Nat.nth Nat.Prime (Nat.count Nat.Prime 11) := by rw [h]
    _ = 11 := Nat.nth_count (by norm_num)

lemma np5 : Nat.nth Nat.Prime 5 = 13 := by
  have h : Nat.count Nat.Prime 13 = 5 := by native_decide
  calc Nat.nth Nat.Prime 5 = Nat.nth Nat.Prime (Nat.count Nat.Prime 13) := by rw [h]
    _ = 13 := Nat.nth_count (by norm_num)

lemma np6 : Nat.nth Nat.Prime 6 = 17 := by
  have h : Nat.count Nat.Prime 17 = 6 := by native_decide
  calc Nat.nth Nat.Prime 6 = Nat.nth Nat.Prime (Nat.count Nat.Prime 17) := by rw [h]
    _ = 17 := Nat.nth_count (by norm_num)

lemma np7 : Nat.nth Nat.Prime 7 = 19 := by
  have h : Nat.count Nat.Prime 19 = 7 := by native_decide
  calc Nat.nth Nat.Prime 7 = Nat.nth Nat.Prime (Nat.count Nat.Prime 19) := by rw [h]
    _ = 19 := Nat.nth_count (by norm_num)

lemma np8 : Nat.nth Nat.Prime 8 = 23 := by
  have h : Nat.count Nat.Prime 23 = 8 := by native_decide
  calc Nat.nth Nat.Prime 8 = Nat.nth Nat.Prime (Nat.count Nat.Prime 23) := by rw [h]
    _ = 23 := Nat.nth_count (by norm_num)

lemma np9 : Nat.nth Nat.Prime 9 = 29 := by
  have h : Nat.count Nat.Prime 29 = 9 := by native_decide
  calc Nat.nth Nat.Prime 9 = Nat.nth Nat.Prime (Nat.count Nat.Prime 29) := by rw [h]
    _ = 29 := Nat.nth_count (by norm_num)

lemma np10 : Nat.nth Nat.Prime 10 = 31 := by
  have h : Nat.count Nat.Prime 31 = 10 := by native_decide
  calc Nat.nth Nat.Prime 10 = Nat.nth Nat.Prime (Nat.count Nat.Prime 31) := by rw [h]
    _ = 31 := Nat.nth_count (by norm_num)

lemma np11 : Nat.nth Nat.Prime 11 = 37 := by
  have h : Nat.count Nat.Prime 37 = 11 := by native_decide
  calc Nat.nth Nat.Prime 11 = Nat.nth Nat.Prime (Nat.count Nat.Prime 37) := by rw [h]
    _ = 37 := Nat.nth_count (by norm_num)

lemma np12 : Nat.nth Nat.Prime 12 = 41 := by
  have h : Nat.count Nat.Prime 41 = 12 := by native_decide
  calc Nat.nth Nat.Prime 12 = Nat.nth Nat.Prime (Nat.count Nat.Prime 41) := by rw [h]
    _ = 41 := Nat.nth_count (by norm_num)

lemma np13 : Nat.nth Nat.Prime 13 = 43 := by
  have h : Nat.count Nat.Prime 43 = 13 := by native_decide
  calc Nat.nth Nat.Prime 13 = Nat.nth Nat.Prime (Nat.count Nat.Prime 43) := by rw [h]
    _ = 43 := Nat.nth_count (by norm_num)

lemma np14 : Nat.nth Nat.Prime 14 = 47 := by
  have h : Nat.count Nat.Prime 47 = 14 := by native_decide
  calc Nat.nth Nat.Prime 14 = Nat.nth Nat.Prime (Nat.count Nat.Prime 47) := by rw [h]
    _ = 47 := Nat.nth_count (by norm_num)

lemma np15 : Nat.nth Nat.Prime 15 = 53 := by
  have h : Nat.count Nat.Prime 53 = 15 := by native_decide
  calc Nat.nth Nat.Prime 15 = Nat.nth Nat.Prime (Nat.count Nat.Prime 53) := by rw [h]
    _ = 53 := Nat.nth_count (by norm_num)

lemma np16 : Nat.nth Nat.Prime 16 = 59 := by
  have h : Nat.count Nat.Prime 59 = 16 := by native_decide
  calc Nat.nth Nat.Prime 16 = Nat.nth Nat.Prime (Nat.count Nat.Prime 59) := by rw [h]
    _ = 59 := Nat.nth_count (by norm_num)

lemma np17 : Nat.nth Nat.Prime 17 = 61 := by
  have h : Nat.count Nat.Prime 61 = 17 := by native_decide
  calc Nat.nth Nat.Prime 17 = Nat.nth Nat.Prime (Nat.count Nat.Prime 61) := by rw [h]
    _ = 61 := Nat.nth_count (by norm_num)

lemma np18 : Nat.nth Nat.Prime 18 = 67 := by
  have h : Nat.count Nat.Prime 67 = 18 := by native_decide
  calc Nat.nth Nat.Prime 18 = Nat.nth Nat.Prime (Nat.count Nat.Prime 67) := by rw [h]
    _ = 67 := Nat.nth_count (by norm_num)

lemma np19 : Nat.nth Nat.Prime 19 = 71 := by
  have h : Nat.count Nat.Prime 71 = 19 := by native_decide
  calc Nat.nth Nat.Prime 19 = Nat.nth Nat.Prime (Nat.count Nat.Prime 71) := by rw [h]
    _ = 71 := Nat.nth_count (by norm_num)

lemma np20 : Nat.nth Nat.Prime 20 = 73 := by
  have h : Nat.count Nat.Prime 73 = 20 := by native_decide
  calc Nat.nth Nat.Prime 20 = Nat.nth Nat.Prime (Nat.count Nat.Prime 73) := by rw [h]
    _ = 73 := Nat.nth_count (by norm_num)

lemma np21 : Nat.nth Nat.Prime 21 = 79 := by
  have h : Nat.count Nat.Prime 79 = 21 := by native_decide
  calc Nat.nth Nat.Prime 21 = Nat.nth Nat.Prime (Nat.count Nat.Prime 79) := by rw [h]
    _ = 79 := Nat.nth_count (by norm_num)

lemma np22 : Nat.nth Nat.Prime 22 = 83 := by
  have h : Nat.count Nat.Prime 83 = 22 := by native_decide
  calc Nat.nth Nat.Prime 22 = Nat.nth Nat.Prime (Nat.count Nat.Prime 83) := by rw [h]
    _ = 83 := Nat.nth_count (by norm_num)

lemma np23 : Nat.nth Nat.Prime 23 = 89 := by
  have h : Nat.count Nat.Prime 89 = 23 := by native_decide
  calc Nat.nth Nat.Prime 23 = Nat.nth Nat.Prime (Nat.count Nat.Prime 89) := by rw [h]
    _ = 89 := Nat.nth_count (by norm_num)

lemma np24 : Nat.nth Nat.Prime 24 = 97 := by
  have h : Nat.count Nat.Prime 97 = 24 := by native_decide
  calc Nat.nth Nat.Prime 24 = Nat.nth Nat.Prime (Nat.count Nat.Prime 97) := by rw [h]
    _ = 97 := Nat.nth_count (by norm_num)

lemma np25 : Nat.nth Nat.Prime 25 = 101 := by
  have h : Nat.count Nat.Prime 101 = 25 := by native_decide
  calc Nat.nth Nat.Prime 25 = Nat.nth Nat.Prime (Nat.count Nat.Prime 101) := by rw [h]
    _ = 101 := Nat.nth_count (by norm_num)

lemma np26 : Nat.nth Nat.Prime 26 = 103 := by
  have h : Nat.count Nat.Prime 103 = 26 := by native_decide
  calc Nat.nth Nat.Prime 26 = Nat.nth Nat.Prime (Nat.count Nat.Prime 103) := by rw [h]
    _ = 103 := Nat.nth_count (by norm_num)

lemma np27 : Nat.nth Nat.Prime 27 = 107 := by
  have h : Nat.count Nat.Prime 107 = 27 := by native_decide
  calc Nat.nth Nat.Prime 27 = Nat.nth Nat.Prime (Nat.count Nat.Prime 107) := by rw [h]
    _ = 107 := Nat.nth_count (by norm_num)

lemma np28 : Nat.nth Nat.Prime 28 = 109 := by
  have h : Nat.count Nat.Prime 109 = 28 := by native_decide
  calc Nat.nth Nat.Prime 28 = Nat.nth Nat.Prime (Nat.count Nat.Prime 109) := by rw [h]
    _ = 109 := Nat.nth_count (by norm_num)

lemma np29 : Nat.nth Nat.Prime 29 = 113 := by
  have h : Nat.count Nat.Prime 113 = 29 := by native_decide
  calc Nat.nth Nat.Prime 29 = Nat.nth Nat.Prime (Nat.count Nat.Prime 113) := by rw [h]
    _ = 113 := Nat.nth_count (by norm_num)

lemma np30 : Nat.nth Nat.Prime 30 = 127 := by
  have h : Nat.count Nat.Prime 127 = 30 := by native_decide
  calc Nat.nth Nat.Prime 30 = Nat.nth Nat.Prime (Nat.count Nat.Prime 127) := by rw [h]
    _ = 127 := Nat.nth_count (by norm_num)

lemma np31 : Nat.nth Nat.Prime 31 = 131 := by
  have h : Nat.count Nat.Prime 131 = 31 := by native_decide
  calc Nat.nth Nat.Prime 31 = Nat.nth Nat.Prime (Nat.count Nat.Prime 131) := by rw [h]
    _ = 131 := Nat.nth_count (by norm_num)

lemma np32 : Nat.nth Nat.Prime 32 = 137 := by
  have h : Nat.count Nat.Prime 137 = 32 := by native_decide
  calc Nat.nth Nat.Prime 32 = Nat.nth Nat.Prime (Nat.count Nat.Prime 137) := by rw [h]
    _ = 137 := Nat.nth_count (by norm_num)

lemma np33 : Nat.nth Nat.Prime 33 = 139 := by
  have h : Nat.count Nat.Prime 139 = 33 := by native_decide
  calc Nat.nth Nat.Prime 33 = Nat.nth Nat.Prime (Nat.count Nat.Prime 139) := by rw [h]
    _ = 139 := Nat.nth_count (by norm_num)

lemma np34 : Nat.nth Nat.Prime 34 = 149 := by
  have h : Nat.count Nat.Prime 149 = 34 := by native_decide
  calc Nat.nth Nat.Prime 34 = Nat.nth Nat.Prime (Nat.count Nat.Prime 149) := by rw [h]
    _ = 149 := Nat.nth_count (by norm_num)

lemma np35 : Nat.nth Nat.Prime 35 = 151 := by
  have h : Nat.count Nat.Prime 151 = 35 := by native_decide
  calc Nat.nth Nat.Prime 35 = Nat.nth Nat.Prime (Nat.count Nat.Prime 151) := by rw [h]
    _ = 151 := Nat.nth_count (by norm_num)

lemma np36 : Nat.nth Nat.Prime 36 = 157 := by
  have h : Nat.count Nat.Prime 157 = 36 := by native_decide
  calc Nat.nth Nat.Prime 36 = Nat.nth Nat.Prime (Nat.count Nat.Prime 157) := by rw [h]
    _ = 157 := Nat.nth_count (by norm_num)

lemma np37 : Nat.nth Nat.Prime 37 = 163 := by
  have h : Nat.count Nat.Prime 163 = 37 := by native_decide
  calc Nat.nth Nat.Prime 37 = Nat.nth Nat.Prime (Nat.count Nat.Prime 163) := by rw [h]
    _ = 163 := Nat.nth_count (by norm_num)

lemma np38 : Nat.nth Nat.Prime 38 = 167 := by
  have h : Nat.count Nat.Prime 167 = 38 := by native_decide
  calc Nat.nth Nat.Prime 38 = Nat.nth Nat.Prime (Nat.count Nat.Prime 167) := by rw [h]
    _ = 167 := Nat.nth_count (by norm_num)

lemma np39 : Nat.nth Nat.Prime 39 = 173 := by
  have h : Nat.count Nat.Prime 173 = 39 := by native_decide
  calc Nat.nth Nat.Prime 39 = Nat.nth Nat.Prime (Nat.count Nat.Prime 173) := by rw [h]
    _ = 173 := Nat.nth_count (by norm_num)

lemma np40 : Nat.nth Nat.Prime 40 = 179 := by
  have h : Nat.count Nat.Prime 179 = 40 := by native_decide
  calc Nat.nth Nat.Prime 40 = Nat.nth Nat.Prime (Nat.count Nat.Prime 179) := by rw [h]
    _ = 179 := Nat.nth_count (by norm_num)

lemma np41 : Nat.nth Nat.Prime 41 = 181 := by
  have h : Nat.count Nat.Prime 181 = 41 := by native_decide
  calc Nat.nth Nat.Prime 41 = Nat.nth Nat.Prime (Nat.count Nat.Prime 181) := by rw [h]
    _ = 181 := Nat.nth_count (by norm_num)

lemma np42 : Nat.nth Nat.Prime 42 = 191 := by
  have h : Nat.count Nat.Prime 191 = 42 := by native_decide
  calc Nat.nth Nat.Prime 42 = Nat.nth Nat.Prime (Nat.count Nat.Prime 191) := by rw [h]
    _ = 191 := Nat.nth_count (by norm_num)

lemma np43 : Nat.nth Nat.Prime 43 = 193 := by
  have h : Nat.count Nat.Prime 193 = 43 := by native_decide
  calc Nat.nth Nat.Prime 43 = Nat.nth Nat.Prime (Nat.count Nat.Prime 193) := by rw [h]
    _ = 193 := Nat.nth_count (by norm_num)

lemma np44 : Nat.nth Nat.Prime 44 = 197 := by
  have h : Nat.count Nat.Prime 197 = 44 := by native_decide
  calc Nat.nth Nat.Prime 44 = Nat.nth Nat.Prime (Nat.count Nat.Prime 197) := by rw [h]
    _ = 197 := Nat.nth_count (by norm_num)

lemma np45 : Nat.nth Nat.Prime 45 = 199 := by
  have h : Nat.count Nat.Prime 199 = 45 := by native_decide
  calc Nat.nth Nat.Prime 45 = Nat.nth Nat.Prime (Nat.count Nat.Prime 199) := by rw [h]
    _ = 199 := Nat.nth_count (by norm_num)

lemma np46 : Nat.nth Nat.Prime 46 = 211 := by
  have h : Nat.count Nat.Prime 211 = 46 := by native_decide
  calc Nat.nth Nat.Prime 46 = Nat.nth Nat.Prime (Nat.count Nat.Prime 211) := by rw [h]
    _ = 211 := Nat.nth_count (by norm_num)

lemma np47 : Nat.nth Nat.Prime 47 = 223 := by
  have h : Nat.count Nat.Prime 223 = 47 := by native_decide
  calc Nat.nth Nat.Prime 47 = Nat.nth Nat.Prime (Nat.count Nat.Prime 223) := by rw [h]
    _ = 223 := Nat.nth_count (by norm_num)

lemma np48 : Nat.nth Nat.Prime 48 = 227 := by
  have h : Nat.count Nat.Prime 227 = 48 := by native_decide
  calc Nat.nth Nat.Prime 48 = Nat.nth Nat.Prime (Nat.count Nat.Prime 227) := by rw [h]
    _ = 227 := Nat.nth_count (by norm_num)

lemma np49 : Nat.nth Nat.Prime 49 = 229 := by
  have h : Nat.count Nat.Prime 229 = 49 := by native_decide
  calc Nat.nth Nat.Prime 49 = Nat.nth Nat.Prime (Nat.count Nat.Prime 229) := by rw [h]
    _ = 229 := Nat.nth_count (by norm_num)

lemma np50 : Nat.nth Nat.Prime 50 = 233 := by
  have h : Nat.count Nat.Prime 233 = 50 := by native_decide
  calc Nat.nth Nat.Prime 50 = Nat.nth Nat.Prime (Nat.count Nat.Prime 233) := by rw [h]
    _ = 233 := Nat.nth_count (by norm_num)

lemma np51 : Nat.nth Nat.Prime 51 = 239 := by
  have h : Nat.count Nat.Prime 239 = 51 := by native_decide
  calc Nat.nth Nat.Prime 51 = Nat.nth Nat.Prime (Nat.count Nat.Prime 239) := by rw [h]
    _ = 239 := Nat.nth_count (by norm_num)

lemma np52 : Nat.nth Nat.Prime 52 = 241 := by
  have h : Nat.count Nat.Prime 241 = 52 := by native_decide
  calc Nat.nth Nat.Prime 52 = Nat.nth Nat.Prime (Nat.count Nat.Prime 241) := by rw [h]
    _ = 241 := Nat.nth_count (by norm_num)

lemma np53 : Nat.nth Nat.Prime 53 = 251 := by
  have h : Nat.count Nat.Prime 251 = 53 := by native_decide
  calc Nat.nth Nat.Prime 53 = Nat.nth Nat.Prime (Nat.count Nat.Prime 251) := by rw [h]
    _ = 251 := Nat.nth_count (by norm_num)

lemma np54 : Nat.nth Nat.Prime 54 = 257 := by
  have h : Nat.count Nat.Prime 257 = 54 := by native_decide
  calc Nat.nth Nat.Prime 54 = Nat.nth Nat.Prime (Nat.count Nat.Prime 257) := by rw [h]
    _ = 257 := Nat.nth_count (by norm_num)

lemma np55 : Nat.nth Nat.Prime 55 = 263 := by
  have h : Nat.count Nat.Prime 263 = 55 := by native_decide
  calc Nat.nth Nat.Prime 55 = Nat.nth Nat.Prime (Nat.count Nat.Prime 263) := by rw [h]
    _ = 263 := Nat.nth_count (by norm_num)

lemma np56 : Nat.nth Nat.Prime 56 = 269 := by
  have h : Nat.count Nat.Prime 269 = 56 := by native_decide
  calc Nat.nth Nat.Prime 56 = Nat.nth Nat.Prime (Nat.count Nat.Prime 269) := by rw [h]
    _ = 269 := Nat.nth_count (by norm_num)

lemma np57 : Nat.nth Nat.Prime 57 = 271 := by
  have h : Nat.count Nat.Prime 271 = 57 := by native_decide
  calc Nat.nth Nat.Prime 57 = Nat.nth Nat.Prime (Nat.count Nat.Prime 271) := by rw [h]
    _ = 271 := Nat.nth_count (by norm_num)

lemma np58 : Nat.nth Nat.Prime 58 = 277 := by
  have h : Nat.count Nat.Prime 277 = 58 := by native_decide
  calc Nat.nth Nat.Prime 58 = Nat.nth Nat.Prime (Nat.count Nat.Prime 277) := by rw [h]
    _ = 277 := Nat.nth_count (by norm_num)

lemma np59 : Nat.nth Nat.Prime 59 = 281 := by
  have h : Nat.count Nat.Prime 281 = 59 := by native_decide
  calc Nat.nth Nat.Prime 59 = Nat.nth Nat.Prime (Nat.count Nat.Prime 281) := by rw [h]
    _ = 281 := Nat.nth_count (by norm_num)

lemma prod_first59_nat : ∏ i ∈ Finset.range 59, Nat.nth Nat.Prime i = P59 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39, np40, np41, np42, np43, np44, np45, np46, np47, np48, np49, np50, np51, np52, np53, np54, np55, np56, np57, np58]
  unfold P59
  norm_num

lemma prod_first59 : ∏ i ∈ Finset.range 59, (Nat.nth Nat.Prime i : ℚ) = (P59 : ℚ) := by
  calc ∏ i ∈ Finset.range 59, (Nat.nth Nat.Prime i : ℚ)
      = ((∏ i ∈ Finset.range 59, Nat.nth Nat.Prime i : ℕ) : ℚ) := by push_cast; ring
    _ = (P59 : ℚ) := by rw [prod_first59_nat]

lemma sum_first59 :
    ∑ i ∈ Finset.range 59, (Nat.nth Nat.Prime i : ℚ)⁻¹ = (N59 : ℚ) / (P59 : ℚ) := by
  unfold N59 P59
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39, np40, np41, np42, np43, np44, np45, np46, np47, np48, np49, np50, np51, np52, np53, np54, np55, np56, np57, np58]
  norm_num

lemma sum_first58 :
    ∑ i ∈ Finset.range 58, (Nat.nth Nat.Prime i : ℚ)⁻¹ = (N58 : ℚ) / (P58 : ℚ) := by
  unfold N58 P58
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, np0, np1, np2, np3, np4, np5, np6, np7, np8, np9, np10, np11, np12, np13, np14, np15, np16, np17, np18, np19, np20, np21, np22, np23, np24, np25, np26, np27, np28, np29, np30, np31, np32, np33, np34, np35, np36, np37, np38, np39, np40, np41, np42, np43, np44, np45, np46, np47, np48, np49, np50, np51, np52, np53, np54, np55, np56, np57]
  norm_num

lemma base_case :
    (4 * 10 ^ 112 : ℚ) * (∑ i ∈ Finset.range 59, (Nat.nth Nat.Prime i : ℚ)⁻¹)
      ≤ ∏ i ∈ Finset.range 59, (Nat.nth Nat.Prime i : ℚ) := by
  rw [sum_first59, prod_first59]
  have hP : (0 : ℚ) < (P59 : ℚ) := by unfold P59; norm_num
  rw [← mul_div_assoc, div_le_iff₀ hP]
  have hbn : (4 * 10 ^ 112 : ℚ) * (N59 : ℚ) ≤ (P59 : ℚ) ^ 2 := by exact_mod_cast barrier_numeric
  rw [pow_two] at hbn
  linarith [hbn]

end Erdos307