import Erdos307.Computational.QSieveAll

/-! Chunk 22 of the q-sieve over the survivor pools (pools 2200 to 2299). One `native_decide`. -/

namespace Erdos307

theorem chunk_22 : chunkOK 22 = true := by native_decide

end Erdos307
