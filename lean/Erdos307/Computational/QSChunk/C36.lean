import Erdos307.Computational.QSieveAll

/-! Chunk 36 of the q-sieve over the survivor pools (pools 3600 to 3699). One `native_decide`. -/

namespace Erdos307

theorem chunk_36 : chunkOK 36 = true := by native_decide

end Erdos307
