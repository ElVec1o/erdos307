import Erdos307.Computational.QSieveBase
import Erdos307.KillData

/-!
# The q-sieve over the survivor pools, in chunks

`chunkOK i` asks `sieveBase` to return `true` on the survivor pools `100 i … 100 i + 99`. Each chunk is a separate
module (`QSChunk/C00 … C36`) with one `native_decide`, so a long run can be stopped between chunks and resumed by
`lake build`; `sieve_all` assembles them.

Paper: Proposition `prop:level60closed` (the sieve for `ρ > 2^-40`).
-/

namespace Erdos307

def sieveOK (V : List ℕ) : Bool := sieveBase (forced39 ++ V)

def chunkOK (i : ℕ) : Bool := ((survivorPools.drop (i * 100)).take 100).all sieveOK

theorem all_chunks {α : Type} (f : α → Bool) (n : ℕ) :
    ∀ (K : ℕ) (L : List α), L.length ≤ K * n →
      (∀ i < K, ((L.drop (i * n)).take n).all f = true) → L.all f = true := by
  intro K
  induction K with
  | zero =>
    intro L hL _
    have : L = [] := List.length_eq_zero_iff.1 (by omega)
    subst this; rfl
  | succ K ih =>
    intro L hL h
    rw [← List.take_append_drop n L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), ?_⟩
    have hlen : (L.drop n).length ≤ K * n := by
      rw [List.length_drop]
      have e : (K + 1) * n = K * n + n := by ring
      omega
    refine ih (L.drop n) hlen ?_
    intro i hi
    have := h (i + 1) (by omega)
    rw [List.drop_drop]
    have e : n + i * n = (i + 1) * n := by ring
    rw [e]; exact this

theorem survivorPools_length : survivorPools.length = 3698 := by decide +kernel

theorem sieve_all (h : ∀ i < 37, chunkOK i = true) : ∀ V ∈ survivorPools, sieveOK V = true := by
  have := all_chunks sieveOK 100 37 survivorPools (by rw [survivorPools_length]; norm_num) h
  intro V hV
  exact List.all_eq_true.1 this V hV

end Erdos307
