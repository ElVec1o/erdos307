import Erdos307.Computational.QSieveAll

/-! Chunk 10 of the q-sieve over the survivor pools (pools 1000 to 1099). One `native_decide`. -/

namespace Erdos307

theorem chunk_10 : chunkOK 10 = true := by native_decide

end Erdos307
