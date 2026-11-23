module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F4
public import MazyaRefinedCauchy.Pkg.F6

@[expose] public section

/-!
# Work package L

The theorems stated in this file are the frozen contract of package L (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package L: the Laplacian, quasianalyticity (Lemma DC) -/

/-- The inner unit normal of the graph of `Γ` at `0`. -/
noncomputable def innerNormalZero (Γ : (Fin n → ℝ) → ℝ) : Space n :=
  -outerNormal Γ 0

/-- Balls tangent to the boundary at `0` from inside lie in the domain. -/
theorem tangent_ball_subset_domain (hn : 0 < n) (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ)
    (hΓ0 : Γ 0 = 0) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R₀ > 0, ∀ R ∈ Set.Ioc 0 R₀, Metric.ball (R • innerNormalZero Γ) R ⊆ domain Γ ρ := by
  sorry

/-- **Kelvin transform.** If `u` is harmonic on an open set `W` not containing `0`, then
`|y|^{1-n} u(y/|y|²)` is harmonic on the image of `W` under inversion. -/
theorem kelvin_harmonicOnNhd {W : Set (Space n)} (hW : IsOpen W) (h0 : (0 : Space n) ∉ W)
    (u : Space n → ℝ) (hu : HarmonicOnNhd u W) :
    HarmonicOnNhd (fun y => ‖y‖ ^ (1 - (n : ℝ)) * u (‖y‖⁻¹ ^ 2 • y))
      {y | y ≠ 0 ∧ ‖y‖⁻¹ ^ 2 • y ∈ W} := by
  sorry

/-- **Lemma DC.** A harmonic function on a half-space `{⟪y, ν⟫ > λ}` that decays like
`e^{-ψ(|y|)}`, with `∫^∞ ψ(s)/s² ds = ∞` and `ψ` regular, vanishes on `{⟪y, ν⟫ > λ + 1}`. -/
theorem harmonic_halfSpace_eq_zero (hn : 0 < n) (ν : Space n) (hν : ‖ν‖ = 1) (lam : ℝ)
    (hlam : 1 ≤ lam) (U : Space n → ℝ) (hU : HarmonicOnNhd U {y | lam < ⟪y, ν⟫_ℝ})
    (ψ : ℝ → ℝ) (Cu : ℝ) (hdecay : ∀ y, lam < ⟪y, ν⟫_ℝ → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)))
    (hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1)) :
    ∀ y, lam + 1 < ⟪y, ν⟫_ℝ → U y = 0 := by
  sorry

end MazyaRefinedCauchy
