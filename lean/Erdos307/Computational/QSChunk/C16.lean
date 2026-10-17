import Erdos307.Computational.QSieveAll

/-! Chunk 16 of the q-sieve over the survivor pools (pools 1600 to 1699). One `native_decide`. -/

namespace Erdos307

theorem chunk_16 : chunkOK 16 = true := by native_decide

end Erdos307
