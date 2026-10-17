import Erdos307.Computational.QSieveAll

/-! Chunk 7 of the q-sieve over the survivor pools (pools 700 to 799). One `native_decide`. -/

namespace Erdos307

theorem chunk_7 : chunkOK 7 = true := by native_decide

end Erdos307
