module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F2
public import MazyaRefinedCauchy.Pkg.F5
public import MazyaRefinedCauchy.Pkg.R1
public import MazyaRefinedCauchy.Pkg.G

@[expose] public section

/-!
# Work package R

The theorems stated in this file are the frozen contract of package R (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package R: interior decay from the refined data (Proposition R) -/

/-- **Proposition R.** Small conormal data, bounded by a regular nondecreasing profile `g`,
force interior decay at rate `√g`. -/
theorem HalfBallSolution.interior_decay (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg : RegularProfile g) :
    ∃ Cd r₀ : ℝ, 0 < Cd ∧ 0 < r₀ ∧ ∀ r ∈ Set.Ioc 0 r₀,
      ∫ x in halfBall n r, (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2) ≤ Cd * Real.sqrt (g (Cd * r)) := by
  sorry

end MazyaRefinedCauchy
