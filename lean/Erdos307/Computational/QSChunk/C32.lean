import Erdos307.Computational.QSieveAll

/-! Chunk 32 of the q-sieve over the survivor pools (pools 3200 to 3299). One `native_decide`. -/

namespace Erdos307

theorem chunk_32 : chunkOK 32 = true := by native_decide

end Erdos307
