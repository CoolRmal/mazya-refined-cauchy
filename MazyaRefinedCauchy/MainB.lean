module

public import MazyaRefinedCauchy.Interfaces

@[expose] public section

/-!
# Theorem I(b)

Assembly of the proof from the package interfaces in `MazyaRefinedCauchy.Interfaces`.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

/-- **Theorem I(b).** Let `u` be harmonic in the domain above the graph of a smooth `Γ`, with `u`
and `∇u` (written `Du`) continuous up to the graph. Suppose the Dirichlet data vanish to infinite
order at `0` and the normal derivative is bounded by `h(|x|)` on the graph. Assume `h` is positive
and nondecreasing on `(0, ρ)`, and that `Λ(σ) = log(1/h(e^{-σ}))` satisfies `Λ(σ)/σ → ∞`, is convex
for large `σ`, and has at most exponential growth `Λ(σ + t) ≤ e^{C t} Λ(σ)` (that is, `Λ' ≤ C Λ`).
If `∫₀ log h = -∞`, then `u = 0` near `0`. -/
theorem mainB {n : ℕ} (hn : 0 < n)
    (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ) (hΓ0 : Γ 0 = 0) (ρ : ℝ) (hρ : 0 < ρ)
    (u : Space n → ℝ) (Du : Space n → Space n)
    (hu : HarmonicOnNhd u (domain Γ ρ))
    (hu_cont : ContinuousOn u (domainWithBoundary Γ ρ))
    (hDu_cont : ContinuousOn Du (domainWithBoundary Γ ρ))
    (hDu : ∀ x ∈ domain Γ ρ, gradient u x = Du x)
    (hDir : ∀ N : ℕ, ∃ C : ℝ, ∀ x ∈ boundaryPiece Γ ρ, |u x| ≤ C * ‖x‖ ^ N)
    (h : ℝ → ℝ)
    (hNeu : ∀ x ∈ boundaryPiece Γ ρ, |⟪Du x, outerNormal Γ x⟫_ℝ| ≤ h ‖x‖)
    (hh_pos : ∀ r ∈ Set.Ioo 0 ρ, 0 < h r)
    (hh_mono : MonotoneOn h (Set.Ioo 0 ρ))
    (hΛ_super : Tendsto (fun σ => Real.log (1 / h (Real.exp (-σ))) / σ) atTop atTop)
    (hΛ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => Real.log (1 / h (Real.exp (-σ)))))
    (hΛ_growth : ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ t ≥ 0,
      Real.log (1 / h (Real.exp (-(σ + t)))) ≤ Real.exp (C * t) * Real.log (1 / h (Real.exp (-σ))))
    (hlog : Tendsto (fun ε => ∫ r in ε..ρ, Real.log (h r)) (𝓝[>] 0) atBot) :
    ∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → u x = 0 := by
  sorry

end MazyaRefinedCauchy
