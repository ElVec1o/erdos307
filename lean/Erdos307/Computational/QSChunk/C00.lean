import Erdos307.Computational.QSieveAll

/-! Chunk 0 of the q-sieve over the survivor pools (pools 0 to 99). One `native_decide`. -/

namespace Erdos307

theorem chunk_0 : chunkOK 0 = true := by native_decide

end Erdos307
