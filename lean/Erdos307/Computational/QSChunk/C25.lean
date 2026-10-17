import Erdos307.Computational.QSieveAll

/-! Chunk 25 of the q-sieve over the survivor pools (pools 2500 to 2599). One `native_decide`. -/

namespace Erdos307

theorem chunk_25 : chunkOK 25 = true := by native_decide

end Erdos307
