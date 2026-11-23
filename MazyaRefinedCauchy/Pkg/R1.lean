module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F3
public import MazyaRefinedCauchy.Pkg.F4
public import MazyaRefinedCauchy.Pkg.U
public import MazyaRefinedCauchy.Pkg.G

@[expose] public section

/-!
# Work package R1

The theorems stated in this file are the frozen contract of package R1 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package R1: infinite order vanishing (Lemma R1) -/

/-- **Lemma R1.** Flat Dirichlet data and flat conormal data force infinite order vanishing. -/
theorem HalfBallSolution.integral_sq_le_pow (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) :
    ∀ M : ℕ, ∃ Cm : ℝ, ∀ r ∈ Set.Ioc 0 (S.R / 2), ∫ x in halfBall n r, S.v x ^ 2 ≤ Cm * r ^ M := by
  sorry

end MazyaRefinedCauchy
