import Erdos307.Computational.QSieveAll

/-! Chunk 33 of the q-sieve over the survivor pools (pools 3300 to 3399). One `native_decide`. -/

namespace Erdos307

theorem chunk_33 : chunkOK 33 = true := by native_decide

end Erdos307
