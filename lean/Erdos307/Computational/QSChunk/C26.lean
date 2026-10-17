import Erdos307.Computational.QSieveAll

/-! Chunk 26 of the q-sieve over the survivor pools (pools 2600 to 2699). One `native_decide`. -/

namespace Erdos307

theorem chunk_26 : chunkOK 26 = true := by native_decide

end Erdos307
