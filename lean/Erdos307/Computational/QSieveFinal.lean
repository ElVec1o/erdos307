import Erdos307.Computational.PairNative
import Erdos307.Computational.KillNative
import Erdos307.Computational.QSChunk.C00
import Erdos307.Computational.QSChunk.C01
import Erdos307.Computational.QSChunk.C02
import Erdos307.Computational.QSChunk.C03
import Erdos307.Computational.QSChunk.C04
import Erdos307.Computational.QSChunk.C05
import Erdos307.Computational.QSChunk.C06
import Erdos307.Computational.QSChunk.C07
import Erdos307.Computational.QSChunk.C08
import Erdos307.Computational.QSChunk.C09
import Erdos307.Computational.QSChunk.C10
import Erdos307.Computational.QSChunk.C11
import Erdos307.Computational.QSChunk.C12
import Erdos307.Computational.QSChunk.C13
import Erdos307.Computational.QSChunk.C14
import Erdos307.Computational.QSChunk.C15
import Erdos307.Computational.QSChunk.C16
import Erdos307.Computational.QSChunk.C17
import Erdos307.Computational.QSChunk.C18
import Erdos307.Computational.QSChunk.C19
import Erdos307.Computational.QSChunk.C20
import Erdos307.Computational.QSChunk.C21
import Erdos307.Computational.QSChunk.C22
import Erdos307.Computational.QSChunk.C23
import Erdos307.Computational.QSChunk.C24
import Erdos307.Computational.QSChunk.C25
import Erdos307.Computational.QSChunk.C26
import Erdos307.Computational.QSChunk.C27
import Erdos307.Computational.QSChunk.C28
import Erdos307.Computational.QSChunk.C29
import Erdos307.Computational.QSChunk.C30
import Erdos307.Computational.QSChunk.C31
import Erdos307.Computational.QSChunk.C32
import Erdos307.Computational.QSChunk.C33
import Erdos307.Computational.QSChunk.C34
import Erdos307.Computational.QSChunk.C35
import Erdos307.Computational.QSChunk.C36

/-!
# Level 60 and the barrier 61, modulo Stage A (tier V2)

Everything about level 60 is now a theorem except Stage A:

* `pair_sector_empty` (`PairNative`): the pair sector is empty;
* `killCheck_run` (`KillNative`): every window base is Jacobi-killed or one of 3,698 listed pools;
* `chunk_0 … chunk_36` (`QSChunk`): the q-sieve returns `true` on every listed pool;
* `StageAList`: no listed pool carries a cycle with `α² 2^40 ≤ D`. This is the one statement still to be proved
  (computed by `code/splitmitm/split_mitm.rs` and re-run independently by `code/splitmitm/stageA2.rs`, not in Lean).

The axioms are the three standard ones and one `native_decide` axiom per compiled evaluation.

Paper: Proposition `prop:level60closed`.
-/

namespace Erdos307

theorem chunks_all : ∀ i < 37, chunkOK i = true
  := fun i hi => match i, hi with
  | 0, _ => chunk_0
  | 1, _ => chunk_1
  | 2, _ => chunk_2
  | 3, _ => chunk_3
  | 4, _ => chunk_4
  | 5, _ => chunk_5
  | 6, _ => chunk_6
  | 7, _ => chunk_7
  | 8, _ => chunk_8
  | 9, _ => chunk_9
  | 10, _ => chunk_10
  | 11, _ => chunk_11
  | 12, _ => chunk_12
  | 13, _ => chunk_13
  | 14, _ => chunk_14
  | 15, _ => chunk_15
  | 16, _ => chunk_16
  | 17, _ => chunk_17
  | 18, _ => chunk_18
  | 19, _ => chunk_19
  | 20, _ => chunk_20
  | 21, _ => chunk_21
  | 22, _ => chunk_22
  | 23, _ => chunk_23
  | 24, _ => chunk_24
  | 25, _ => chunk_25
  | 26, _ => chunk_26
  | 27, _ => chunk_27
  | 28, _ => chunk_28
  | 29, _ => chunk_29
  | 30, _ => chunk_30
  | 31, _ => chunk_31
  | 32, _ => chunk_32
  | 33, _ => chunk_33
  | 34, _ => chunk_34
  | 35, _ => chunk_35
  | 36, _ => chunk_36
  | _ + 37, h => absurd h (by omega)

theorem sieve_survivors : ∀ V ∈ survivorPools, sieveOK V = true :=
  sieve_all chunks_all

/-- Stage A on the listed pools: no cycle in the small-`ρ` regime. -/
def StageAList : Prop := ∀ V ∈ survivorPools, ¬ CycleLow (forced39 ++ V).toFinset

theorem tail_empty_of_stageA (hA : StageAList) : TailSectorEmpty :=
  tail_empty_of_survivors fun V hV hnd hp h2 hT =>
    ⟨hA V hV, fun q hq hlt ⟨hqD, hTA⟩ =>
      sieveBase_sound hnd hp h2 hT (sieve_survivors V hV) q hq hlt hqD hTA⟩

/-- **The barrier `61`, modulo Stage A.** -/
theorem erdos307_sixtyone_of_stageA (hA : StageAList) {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1) : 61 ≤ (P ∪ Q).card :=
  erdos307_sixtyone_of_sectors pair_sector_empty (tail_empty_of_stageA hA) hP hQ heq

end Erdos307
