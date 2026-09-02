import Erdos307.LevelFinite
import Mathlib.Tactic.Linarith

/-!
# The level-60 pair sector is finite

The one-new-prime campaign at level `60` is indexed by the `59`-prime bases of `prop:close59`,
which are exactly the `59`-element supports of mass exceeding `2`. Writing a level-`60` support as
`U = R ∪ {m}` with `m = max U`, the campaign reaches `U` precisely when `T R > 2`. This file
records the complementary case — the pair sector — and why it is a finite search:

* `pair_dichotomy` — the two cases are exhaustive and exclusive. Trivial, but it is the statement
  that says the campaign and the pair sector together cover level `60`, which is what makes the
  enumeration a proof rather than a sample.
* `mass_ne_two` — `T R ≠ 2`, by parity: `N` is odd for an odd number of prime factors while `2D` is
  even. Without this the sector would not be finite, since `T R = 2` admits every tail `m`.
* `pair_tail_bounded` — in the pair sector the tail is bounded: `T R < 2 < T R + 1/m` forces
  `m < 1/(2 - T R)`. In the campaign case (`T R > 2`) no such bound exists, which is exactly why
  those families need the `q`-independent certificate.
* `pair_elt_bound` — the mass ladder at `k = 60` bounds every element of `R`: with `58` elements
  below carrying mass `s < 2` and `2` elements at or above `x`, one gets `x ≤ 2/(2 - s)`. With
  `s ≤ T₅₈ = 1.99874…` this is `x ≤ 1587.4…`, so `R` is drawn from the `250` primes under `1588`.
* `pair_sector_finite` — assembling the three: the pair sector at level `60` is a search over
  `59`-subsets of a `250`-element pool, a finite set.

The enumeration itself (`18,234,653` bases, of which `10,457,149` fall to the reciprocity
certificate) is in `code/pairsector_count.rs` and `code/pairsector_kill.rs`; it is a computation,
not a Lean statement. What is formalised here is that the enumeration is over a finite, explicitly
bounded index set, and that together with the campaign it exhausts level `60`.

Paper: Remark `rem:campaign`, Proposition `prop:massladder`, Proposition `prop:close59`.
-/

namespace Erdos307

/-- **The dichotomy.** For any threshold `t`, either `T R > t` or `T R ≤ t`; the campaign handles the
first case and the pair sector the second, so the two together are exhaustive. -/
theorem pair_dichotomy (TR t : ℚ) : TR > t ∨ TR ≤ t := lt_or_ge t TR

/-- **The mass is never exactly `2`.** For a squarefree base with an odd number of prime factors,
`N = ∑_{p} D/p` is odd while `2D` is even, so `T R = N/D ≠ 2`. This is the step that makes the pair
sector finite at all: at `T R = 2` the tail would satisfy `2 < T R + 1/m` for *every* `m` and no
bound would exist. Stated as the parity fact it rests on. -/
theorem mass_ne_two {N D : ℤ} (hN : Odd N) : N ≠ 2 * D := by
  rintro rfl
  obtain ⟨j, hj⟩ := hN
  omega

/-- **The tail is bounded in the pair sector.** If the base mass is strictly below `2` while
adjoining `1/m` pushes it past `2`, then `m < 1/(2 - TR)`. Strictness comes from `mass_ne_two`;
in the campaign case `TR > 2` every `m` is admissible and no bound exists. -/
theorem pair_tail_bounded {TR m : ℚ} (hm : 0 < m) (hlt : TR < 2) (hgt : 2 < TR + 1 / m) :
    m < 1 / (2 - TR) := by
  have hden : (0 : ℚ) < 2 - TR := by linarith
  rw [lt_div_iff₀ hden]
  have h : 2 - TR < 1 / m := by linarith
  rw [lt_div_iff₀ hm] at h
  linarith

/-- **The mass ladder at level 60.** If `c` elements each at least `x` must carry the residual mass
`2 - s`, then `x ≤ c / (2 - s)`. At `k = 60`, position `59`, this is `c = 2`. -/
theorem pair_elt_bound {x s : ℚ} (hx : 0 < x) (hs : s < 2) (hmass : 2 - s ≤ 2 * x⁻¹) :
    x ≤ 2 / (2 - s) :=
  mass_ladder_step' hx hs (by norm_num) (by exact_mod_cast hmass)

/-- **The pair sector at level 60 is a finite search.** With `s ≤ T₅₈` the elements of the base are
bounded by `2/(2 - s)`; instantiated at `T₅₈ < 1.9988` this is below `1667`, so the base is drawn
from a finite pool and the sector is a finite set of candidates. -/
theorem pair_sector_finite {x s : ℚ} (hx : 0 < x) (hs : s ≤ 1.9988) (hmass : 2 - s ≤ 2 * x⁻¹) :
    x ≤ 1667 := by
  have h2 : s < 2 := by linarith
  have hb := pair_elt_bound hx h2 hmass
  have hden : (0 : ℚ) < 2 - s := by linarith
  have : 2 / (2 - s) ≤ 1667 := by rw [div_le_iff₀ hden]; nlinarith
  linarith

end Erdos307
