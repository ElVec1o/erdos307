import Erdos307.Computational.QSieveAll

/-! Chunk 8 of the q-sieve over the survivor pools (pools 800 to 899). One `native_decide`. -/

namespace Erdos307

theorem chunk_8 : chunkOK 8 = true := by native_decide

end Erdos307
