import Erdos307.Computational.QSieveAll

/-! Chunk 24 of the q-sieve over the survivor pools (pools 2400 to 2499). One `native_decide`. -/

namespace Erdos307

theorem chunk_24 : chunkOK 24 = true := by native_decide

end Erdos307
