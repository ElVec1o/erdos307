import Erdos307.Computational.QSieveAll

/-! Chunk 2 of the q-sieve over the survivor pools (pools 200 to 299). One `native_decide`. -/

namespace Erdos307

theorem chunk_2 : chunkOK 2 = true := by native_decide

end Erdos307
