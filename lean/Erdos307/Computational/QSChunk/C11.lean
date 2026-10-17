import Erdos307.Computational.QSieveAll

/-! Chunk 11 of the q-sieve over the survivor pools (pools 1100 to 1199). One `native_decide`. -/

namespace Erdos307

theorem chunk_11 : chunkOK 11 = true := by native_decide

end Erdos307
