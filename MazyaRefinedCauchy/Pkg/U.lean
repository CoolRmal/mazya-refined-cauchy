module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F2

@[expose] public section

/-!
# Work package U

The theorems stated in this file are the frozen contract of package U (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package U: weak unique continuation -/

/-- **Weak unique continuation.** A `C²` solution of `div(A ∇v) + B · ∇v + C v = 0` on a connected
open set, with `A` symmetric, `C²` and positive definite and `B`, `C` continuous, which vanishes
near one point, vanishes everywhere. -/
theorem weak_ucp {U : Set (Space n)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n) (C : Space n → ℝ)
    (hA : ContDiffOn ℝ 2 A U) (hsymm : ∀ x ∈ U, ∀ ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (hpos : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫_ℝ)
    (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (v : Space n → ℝ) (hv : ContDiffOn ℝ 2 v U) (heq : ∀ x ∈ U, ellOp A B C v x = 0)
    (x₀ : Space n) (hx₀ : x₀ ∈ U) (hloc : ∀ᶠ x in 𝓝 x₀, v x = 0) :
    ∀ x ∈ U, v x = 0 := by
  sorry

end MazyaRefinedCauchy
