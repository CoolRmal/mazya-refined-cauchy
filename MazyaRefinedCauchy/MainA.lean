module

public import MazyaRefinedCauchy.Interfaces

/-!
# Theorem I(a)

Assembly of the proof from the package interfaces in `MazyaRefinedCauchy.Interfaces`.
-/

public section

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazyaRefinedCauchy

/-- **Theorem I(a).** Let `L u = div(a ∇u) + b · ∇u + c u`, where the matrix field `a` is smooth,
symmetric and uniformly elliptic, and `b`, `c` are continuous. Let `u` be `C²` in the domain above
the graph of a smooth `Γ`, with `u` and `∇u` (written `Du`) continuous up to the graph, and
`L u = 0` in the domain. Suppose the Dirichlet data vanish to infinite order at `0`, and the
conormal derivative `a ∇u · n` is bounded by `h(|x|)` on the graph, where `h(r) ≤ e^{-M/r}` for
small `r`, for every `M` (for positive `h` this says `r log(1/h(r)) → ∞`). Then `u = 0` near
`0`. -/
theorem mainA {n : ℕ} (hn : 0 < n)
    (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ) (hΓ0 : Γ 0 = 0) (ρ : ℝ) (hρ : 0 < ρ)
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
    (h : ℝ → ℝ)
    (hNeu : ∀ x ∈ boundaryPiece Γ ρ, |⟪a x (Du x), outerNormal Γ x⟫_ℝ| ≤ h ‖x‖)
    (hh : ∀ M : ℝ, ∀ᶠ r in 𝓝[>] 0, h r ≤ Real.exp (-M / r)) :
    ∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → u x = 0 := by
  sorry

end MazyaRefinedCauchy
