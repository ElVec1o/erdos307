import Erdos307.Computational.QSieveAll

/-! Chunk 20 of the q-sieve over the survivor pools (pools 2000 to 2099). One `native_decide`. -/

namespace Erdos307

theorem chunk_20 : chunkOK 20 = true := by native_decide

end Erdos307
