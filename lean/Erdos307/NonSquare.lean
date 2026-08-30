import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# A modular non-square certificate

`Sixty.lean` must certify, for each of the 49,961 admissible supports, that
`csum U + 2·dprod U` is not a perfect square. Doing that by `Nat.sqrt` forces the kernel through a
structural recursion of some hundreds of steps on a 130-digit number, which is why the check was
previously delegated to `native_decide` and carried the `Lean.ofReduceBool` axiom.

A residue certificate replaces it. If `n` is a square then `n % m` is a square modulo `m` for every
`m`, so exhibiting one `m` for which `n % m` is a non-residue proves `n` is not a square. The
residues are recorded as bitmasks, so the whole test is one `%`, one shift and one `and` per
modulus: arithmetic the kernel does through GMP.

Eleven moduli suffice for all 49,961 supports; the covering set was found greedily
(`code/nonsquare_cert.rs`), and `decide` on `dfsA_run` re-checks it from scratch.

Paper: Proposition `prop:close59`, the trust-boundary discussion in the Lean section.
-/

set_option maxRecDepth 100000

namespace Erdos307

/-- Moduli paired with the bitmask of their quadratic residues: bit `k` of the mask is set exactly
when `k` is a square modulo the modulus. -/
def certMods : List (ℕ × ℕ) :=
  [(8, 19),
   (19, 199411),
   (167, 6058870142380879454330449817022811454536025988063),
   (127, 30790515292689894969866990722818747159),
   (149, 441852139177177952668163358831104772057793267),
   (67, 61808106872519771731),
   (59, 156326468341437115),
   (101, 1550432784880709368503235994227),
   (73, 9059857384996697084767),
   (191, 26252236807386378396776436556232156846523662924177192831),
   (41, 1870503675703)]

/-- `n` is certified non-square when some listed modulus makes it a non-residue. -/
def nsqCert (n : ℕ) : Bool :=
  certMods.any fun q => !(q.2.testBit (n % q.1))

/-- Each mask really does record the squares of its modulus. Checked by the kernel. -/
lemma certMods_valid :
    ∀ q ∈ certMods, 0 < q.1 ∧ ∀ r < q.1, q.2.testBit (r * r % q.1) = true := by decide

/-- **The certificate is sound.** A certified number is not a perfect square. -/
theorem not_isSquare_of_nsqCert {n : ℕ} (h : nsqCert n = true) : ¬ ∃ k, n = k * k := by
  rintro ⟨k, rfl⟩
  rw [nsqCert, List.any_eq_true] at h
  obtain ⟨q, hq, hbit⟩ := h
  obtain ⟨hpos, hall⟩ := certMods_valid q hq
  have hmod : k * k % q.1 = (k % q.1) * (k % q.1) % q.1 := by rw [Nat.mul_mod]
  have := hall (k % q.1) (Nat.mod_lt _ hpos)
  rw [← hmod] at this
  simp [this] at hbit

end Erdos307
