import Erdos307.Computational.QSieveAll

/-! Chunk 18 of the q-sieve over the survivor pools (pools 1800 to 1899). One `native_decide`. -/

namespace Erdos307

theorem chunk_18 : chunkOK 18 = true := by native_decide

end Erdos307
