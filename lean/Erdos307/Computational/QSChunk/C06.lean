import Erdos307.Computational.QSieveAll

/-! Chunk 6 of the q-sieve over the survivor pools (pools 600 to 699). One `native_decide`. -/

namespace Erdos307

theorem chunk_6 : chunkOK 6 = true := by native_decide

end Erdos307
