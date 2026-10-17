import Erdos307.Computational.QSieveAll

/-! Chunk 14 of the q-sieve over the survivor pools (pools 1400 to 1499). One `native_decide`. -/

namespace Erdos307

theorem chunk_14 : chunkOK 14 = true := by native_decide

end Erdos307
