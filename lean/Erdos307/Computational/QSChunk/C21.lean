import Erdos307.Computational.QSieveAll

/-! Chunk 21 of the q-sieve over the survivor pools (pools 2100 to 2199). One `native_decide`. -/

namespace Erdos307

theorem chunk_21 : chunkOK 21 = true := by native_decide

end Erdos307
