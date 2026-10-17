import Erdos307.Computational.QSieveAll

/-! Chunk 19 of the q-sieve over the survivor pools (pools 1900 to 1999). One `native_decide`. -/

namespace Erdos307

theorem chunk_19 : chunkOK 19 = true := by native_decide

end Erdos307
