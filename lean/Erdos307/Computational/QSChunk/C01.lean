import Erdos307.Computational.QSieveAll

/-! Chunk 1 of the q-sieve over the survivor pools (pools 100 to 199). One `native_decide`. -/

namespace Erdos307

theorem chunk_1 : chunkOK 1 = true := by native_decide

end Erdos307
