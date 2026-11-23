module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Definitions of the advertised statement

These definitions must stay *identical* to the ones in `Challenge.lean`: the statements proved in
`Solution.lean` refer to them, and Comparator checks that they match. `scripts/check-defs-sync.py`
checks this in CI.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace

namespace MazyaRefinedCauchy

/-- The space `ℝⁿ⁺¹` with its Euclidean structure. -/
abbrev Space (n : ℕ) : Type := EuclideanSpace ℝ (Fin (n + 1))

/-- The defining function `Γ(x₁, …, xₙ) - xₙ₊₁` of the graph of `Γ`. It is negative exactly above
the graph and zero exactly on it. -/
noncomputable def graphFn {n : ℕ} (Γ : (Fin n → ℝ) → ℝ) (x : Space n) : ℝ :=
  Γ (fun i => x (Fin.castSucc i)) - x (Fin.last n)

/-- The domain near the boundary point `0`: the points of the open ball `B(0, ρ)` lying strictly
above the graph of `Γ`. -/
def domain {n : ℕ} (Γ : (Fin n → ℝ) → ℝ) (ρ : ℝ) : Set (Space n) :=
  {x | ‖x‖ < ρ ∧ graphFn Γ x < 0}

/-- The boundary piece carrying the Cauchy data: the points of `B(0, ρ)` on the graph of `Γ`. -/
def boundaryPiece {n : ℕ} (Γ : (Fin n → ℝ) → ℝ) (ρ : ℝ) : Set (Space n) :=
  {x | ‖x‖ < ρ ∧ graphFn Γ x = 0}

/-- The domain together with its boundary piece: the points of `B(0, ρ)` on or above the graph. -/
def domainWithBoundary {n : ℕ} (Γ : (Fin n → ℝ) → ℝ) (ρ : ℝ) : Set (Space n) :=
  {x | ‖x‖ < ρ ∧ graphFn Γ x ≤ 0}

/-- The outward unit normal at a point of the graph: the normalized gradient of `graphFn Γ`. -/
noncomputable def outerNormal {n : ℕ} (Γ : (Fin n → ℝ) → ℝ) (x : Space n) : Space n :=
  ‖gradient (graphFn Γ) x‖⁻¹ • gradient (graphFn Γ) x

/-- The divergence `div F(x) = tr DF(x)` of a vector field `F` on `ℝⁿ⁺¹`. -/
noncomputable def divergence {n : ℕ} (F : Space n → Space n) (x : Space n) : ℝ :=
  LinearMap.trace ℝ (Space n) (fderiv ℝ F x : Space n →ₗ[ℝ] Space n)

end MazyaRefinedCauchy
