import Erdos307.Computational.QSieveAll

/-! Chunk 35 of the q-sieve over the survivor pools (pools 3500 to 3599). One `native_decide`. -/

namespace Erdos307

theorem chunk_35 : chunkOK 35 = true := by native_decide

end Erdos307
