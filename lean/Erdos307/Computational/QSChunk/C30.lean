import Erdos307.Computational.QSieveAll

/-! Chunk 30 of the q-sieve over the survivor pools (pools 3000 to 3099). One `native_decide`. -/

namespace Erdos307

theorem chunk_30 : chunkOK 30 = true := by native_decide

end Erdos307
