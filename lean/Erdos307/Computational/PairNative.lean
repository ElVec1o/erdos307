import Erdos307.Computational.PairSectorEmpty

/-!
# Track B (V2): the pair sector of level 60 is empty

The single compiled evaluation. `pairCheck` is the Boolean `pair_sector_empty_of_check` consumes; it is
discharged by `native_decide`, so `pair_sector_empty` depends on `Lean.ofReduceBool` in addition to the
three standard axioms. This module is not imported by `Erdos307.lean` or `Check.lean`; the V1 core is
unaffected. The expected cost is a few CPU-hours (one thread).

The trust added over V1 is the Lean compiler/evaluator for this one pure function; the independent
Rust checker `code/pairsector_close.rs` is a cross-check, not a dependency.

Paper: Proposition `prop:pairclosed`.
-/

namespace Erdos307

theorem pairCheck : pdfs (leaf (mkTabs 1667)) (primesUpTo 1667) 59 0 [] = true := by
  native_decide

/-- **The pair sector of level 60 is empty** (V2: kernel proof plus one compiled evaluation). -/
theorem pair_sector_empty : PairSectorEmpty := pair_sector_empty_of_check pairCheck

end Erdos307
