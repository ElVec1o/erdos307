import Erdos307.Computational.QSieveAll

/-! Chunk 13 of the q-sieve over the survivor pools (pools 1300 to 1399). One `native_decide`. -/

namespace Erdos307

theorem chunk_13 : chunkOK 13 = true := by native_decide

end Erdos307
