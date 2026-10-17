import Erdos307.Computational.QSieveAll

/-! Chunk 15 of the q-sieve over the survivor pools (pools 1500 to 1599). One `native_decide`. -/

namespace Erdos307

theorem chunk_15 : chunkOK 15 = true := by native_decide

end Erdos307
