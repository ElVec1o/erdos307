import Erdos307.Computational.QSieveAll

/-! Chunk 4 of the q-sieve over the survivor pools (pools 400 to 499). One `native_decide`. -/

namespace Erdos307

theorem chunk_4 : chunkOK 4 = true := by native_decide

end Erdos307
