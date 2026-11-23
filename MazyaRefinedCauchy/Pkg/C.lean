module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1

@[expose] public section

/-!
# Work package C

The theorems stated in this file are the frozen contract of package C (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package C: the conormal collar -/

/-- **Collar reduction.** The data of Theorem I yield a half-ball solution `S` and a map `F`
from the half-ball onto a neighbourhood of `0` in the domain, transporting `v` to `u`, the flat
piece to the boundary piece, and comparing conormal derivatives and `L²` norms. -/
theorem collar_reduction (hn : 0 < n) (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ) (hΓ0 : Γ 0 = 0)
    (ρ : ℝ) (hρ : 0 < ρ)
    (a : Space n → Space n →L[ℝ] Space n) (ha : ContDiff ℝ ∞ a)
    (ha_symm : ∀ x ξ η, ⟪a x ξ, η⟫_ℝ = ⟪ξ, a x η⟫_ℝ)
    (ha_ell : ∃ lam > 0, ∀ x ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x ξ, ξ⟫_ℝ)
    (b : Space n → Space n) (hb : Continuous b) (c : Space n → ℝ) (hc : Continuous c)
    (u : Space n → ℝ) (Du : Space n → Space n)
    (hu : ContDiffOn ℝ 2 u (domain Γ ρ))
    (hu_cont : ContinuousOn u (domainWithBoundary Γ ρ))
    (hDu_cont : ContinuousOn Du (domainWithBoundary Γ ρ))
    (hDu : ∀ x ∈ domain Γ ρ, gradient u x = Du x)
    (hL : ∀ x ∈ domain Γ ρ,
      divergence (fun y => a y (gradient u y)) x + ⟪b x, gradient u x⟫_ℝ + c x * u x = 0)
    (hDir : ∀ N : ℕ, ∃ C : ℝ, ∀ x ∈ boundaryPiece Γ ρ, |u x| ≤ C * ‖x‖ ^ N)
    :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ R₁ > 0, ∃ (S : HalfBallSolution n) (F : Space n → Space n), S.R ≤ R₁ ∧
      (∀ X ∈ halfBall n S.R, F X ∈ domain Γ ρ ∧ S.v X = u (F X)) ∧
      (∀ X ∈ flatPiece n S.R, F X ∈ boundaryPiece Γ ρ ∧ ‖F X‖ ≤ κ * ‖X‖ ∧ ‖X‖ ≤ κ * ‖F X‖ ∧
        |⟪S.A X (S.Dv X), ed n⟫_ℝ| ≤ κ * |⟪a (F X) (Du (F X)), outerNormal Γ (F X)⟫_ℝ|) ∧
      (∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → ∃ X ∈ halfBall n S.R, F X = x) ∧
      (∀ W : Set (Space n), IsOpen W → (W ∩ F '' halfBall n S.R).Nonempty →
        ∃ V : Set (Space n), IsOpen V ∧ V.Nonempty ∧ V ⊆ halfBall n S.R ∧ ∀ X ∈ V, F X ∈ W) ∧
      (∀ r ∈ Set.Ioc 0 S.R,
        ∫ x in domain Γ ρ ∩ Metric.ball 0 (r / κ), u x ^ 2 ≤ κ * ∫ X in halfBall n r, S.v X ^ 2) := by
  sorry

end MazyaRefinedCauchy
