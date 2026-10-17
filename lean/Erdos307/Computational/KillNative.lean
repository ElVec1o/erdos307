import Erdos307.KillSearch
import Erdos307.KillData

/-!
# Track B (V2): the kill stage of the level-60 tail sector

`killCheck_run` evaluates `checkAll` over the 49,961 pools of `enumA` with the generated certificates and survivor
list. The kernel evaluation of `enumA` needs several GB of cache, so it is run compiled (`native_decide`), as for the
pair sector: the extra axiom is the `native_decide` one. The soundness of the check is the kernel-proved
`tail_of_survivors`.

Paper: Proposition `prop:tailkill`, `prop:level60closed`.
-/

namespace Erdos307

set_option maxHeartbeats 0 in
theorem killCheck_run : checkAll (enumA pool99 20 0 []) killCerts survivorPools = true := by
  native_decide

/-- Level 60 tail sector, reduced to the listed survivor pools: if no survivor pool carries a low-`ρ` cycle or a
q-sieve solution, `TailSectorEmpty` holds. Everything else is killed by a Jacobi symbol (V2: one `native_decide`). -/
theorem tail_empty_of_survivors
    (hL : ∀ V ∈ survivorPools, (forced39 ++ V).Nodup → (∀ p ∈ forced39 ++ V, p.Prime) → 2 ∈ forced39 ++ V →
      2 * dprod (forced39 ++ V).toFinset ≤ csum (forced39 ++ V).toFinset →
      ¬ CycleLow (forced39 ++ V).toFinset ∧ ∀ q : ℕ, q.Prime →
      (∀ s ∈ forced39 ++ V, s < q) →
      ¬ (q * dprod (forced39 ++ V).toFinset ≤ csum (forced39 ++ V).toFinset * 2 ^ 40 ∧
        TailArith (forced39 ++ V).toFinset q)) : TailSectorEmpty :=
  tail_of_survivors killCheck_run hL

end Erdos307
