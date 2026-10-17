import Erdos307.Computational.QSieveAll

/-! Chunk 9 of the q-sieve over the survivor pools (pools 900 to 999). One `native_decide`. -/

namespace Erdos307

theorem chunk_9 : chunkOK 9 = true := by native_decide

end Erdos307
