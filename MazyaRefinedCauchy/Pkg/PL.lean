module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F2
public import MazyaRefinedCauchy.Pkg.G

@[expose] public section

/-!
# Work package PL

The theorems stated in this file are the frozen contract of package PL (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package PL: inversion and the Phragmén–Lindelöf principle (Proposition PL) -/

/-- **Proposition PL.** Interior decay faster than every `e^{-N/r}` forces the solution to vanish
on a ball tangent to the flat boundary at `0`. -/
theorem HalfBallSolution.vanish_of_superexp (S : HalfBallSolution n)
    (hdecay : ∀ N : ℝ, ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 S.R,
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cn * Real.exp (-N / r)) :
    ∃ r' > 0, ∀ x ∈ Metric.ball (r' • ed n) r', S.v x = 0 := by
  sorry

end MazyaRefinedCauchy
