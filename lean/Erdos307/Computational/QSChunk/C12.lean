import Erdos307.Computational.QSieveAll

/-! Chunk 12 of the q-sieve over the survivor pools (pools 1200 to 1299). One `native_decide`. -/

namespace Erdos307

theorem chunk_12 : chunkOK 12 = true := by native_decide

end Erdos307
