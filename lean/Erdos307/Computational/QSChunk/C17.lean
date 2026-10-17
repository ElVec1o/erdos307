import Erdos307.Computational.QSieveAll

/-! Chunk 17 of the q-sieve over the survivor pools (pools 1700 to 1799). One `native_decide`. -/

namespace Erdos307

theorem chunk_17 : chunkOK 17 = true := by native_decide

end Erdos307
