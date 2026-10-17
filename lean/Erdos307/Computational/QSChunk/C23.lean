import Erdos307.Computational.QSieveAll

/-! Chunk 23 of the q-sieve over the survivor pools (pools 2300 to 2399). One `native_decide`. -/

namespace Erdos307

theorem chunk_23 : chunkOK 23 = true := by native_decide

end Erdos307
