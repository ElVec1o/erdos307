import Erdos307.Computational.QSieveAll

/-! Chunk 3 of the q-sieve over the survivor pools (pools 300 to 399). One `native_decide`. -/

namespace Erdos307

theorem chunk_3 : chunkOK 3 = true := by native_decide

end Erdos307
