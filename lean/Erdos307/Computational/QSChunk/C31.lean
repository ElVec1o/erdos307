import Erdos307.Computational.QSieveAll

/-! Chunk 31 of the q-sieve over the survivor pools (pools 3100 to 3199). One `native_decide`. -/

namespace Erdos307

theorem chunk_31 : chunkOK 31 = true := by native_decide

end Erdos307
