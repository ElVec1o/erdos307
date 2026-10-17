import Erdos307.Computational.QSieveAll

/-! Chunk 5 of the q-sieve over the survivor pools (pools 500 to 599). One `native_decide`. -/

namespace Erdos307

theorem chunk_5 : chunkOK 5 = true := by native_decide

end Erdos307
