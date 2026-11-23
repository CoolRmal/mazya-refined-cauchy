module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F4

The theorems stated in this file are the frozen contract of package F4 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F4: harmonic functions: a sup bound from `L²` -/

/-- A harmonic function is bounded at the centre of a ball by its `L²` norm on the ball. -/
theorem harmonic_abs_le_L2 (n : ℕ) : ∃ Cn : ℝ, ∀ (u : Space n → ℝ) (x : Space n) (r : ℝ),
    0 < r → HarmonicOnNhd u (Metric.closedBall x r) →
      |u x| ≤ Cn * r ^ (-((n + 1 : ℝ) / 2)) * Real.sqrt (∫ y in Metric.ball x r, u y ^ 2) := by
  sorry

end MazyaRefinedCauchy
