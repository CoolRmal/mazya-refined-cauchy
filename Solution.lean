module

public import MazyaRefinedCauchy
public import MazyaRefinedCauchy.MainA
public import MazyaRefinedCauchy.MainB

/-!
# Proved solution

The two theorems below have exactly the statements of `Challenge.lean`; Comparator checks this
and that the proofs use only the permitted axioms. The definitions they mention come from
`MazyaRefinedCauchy.Defs`, which repeats the definitions of `Challenge.lean`.
-/

public section

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace

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
theorem refined_cauchy_superexp {n : ℕ} (hn : 0 < n)
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
    ∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → u x = 0 :=
  mainA hn Γ hΓ hΓ0 ρ hρ a ha ha_symm ha_ell b hb c hc u Du hu hu_cont hDu_cont hDu hL hDir h
    hNeu hh

/-- **Theorem I(b).** Let `u` be harmonic in the domain above the graph of a smooth `Γ`, with `u`
and `∇u` (written `Du`) continuous up to the graph. Suppose the Dirichlet data vanish to infinite
order at `0` and the normal derivative is bounded by `h(|x|)` on the graph. Assume `h` is positive
and nondecreasing on `(0, ρ)`, and that `Λ(σ) = log(1/h(e^{-σ}))` satisfies `Λ(σ)/σ → ∞`, is convex
for large `σ`, and has at most exponential growth `Λ(σ + t) ≤ e^{C t} Λ(σ)` (that is, `Λ' ≤ C Λ`).
If `∫₀ log h = -∞` (stated on `(0, ρ/2)`), then `u = 0` near `0`. -/
theorem refined_cauchy_laplace {n : ℕ} (hn : 0 < n)
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
    (hΛ_convex : ∃ σ₀ : ℝ,
      ConvexOn ℝ (Set.Ici σ₀) (fun σ => Real.log (1 / h (Real.exp (-σ)))))
    (hΛ_growth : ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ t ≥ 0,
      Real.log (1 / h (Real.exp (-(σ + t))))
        ≤ Real.exp (C * t) * Real.log (1 / h (Real.exp (-σ))))
    (hlog : Tendsto (fun ε => ∫ r in ε..(ρ / 2), Real.log (h r)) (𝓝[>] 0) atBot) :
    ∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → u x = 0 :=
  mainB hn Γ hΓ hΓ0 ρ hρ u Du hu hu_cont hDu_cont hDu hDir h hNeu hh_pos hh_mono hΛ_super
    hΛ_convex hΛ_growth hlog

end MazyaRefinedCauchy
