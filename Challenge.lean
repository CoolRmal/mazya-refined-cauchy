module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Maz'ya's refined Cauchy uniqueness problem at a boundary point

We work in `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))` with `n ≥ 1`, and call the last coordinate
`xₙ₊₁` vertical. Near the boundary point `0`, the domain is the region above the graph of a smooth
function `Γ : ℝⁿ → ℝ` with `Γ 0 = 0`, intersected with the ball `B(0, ρ)`.

A function `u` is `C²` in the domain, and `u` and its gradient extend continuously to the boundary
piece (the graph). Its Dirichlet data vanish to infinite order at `0`, and only its Neumann
(conormal) data are assumed small, bounded by `h(|x|)`.

* `refined_cauchy_superexp` (Theorem I(a)): for an elliptic operator
  `L u = div(a ∇u) + b · ∇u + c u` with smooth symmetric uniformly elliptic `a` and continuous `b`,
  `c`, if `r log(1/h(r)) → ∞` as `r → 0⁺`, then `u` vanishes near `0`.
* `refined_cauchy_laplace` (Theorem I(b)): for harmonic `u`, if `∫₀ log h = -∞` and `h` is regular,
  then `u` vanishes near `0`.

This is the setting of V. Maz'ya, *Seventy five (thousand) unsolved problems in analysis and
partial differential equations*, Integral Equations Operator Theory (2018), Problem 5.3.
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

/-- **Theorem I(a).** Let `L u = div(a ∇u) + b · ∇u + c u`, where the matrix field `a` is smooth,
symmetric and uniformly elliptic, and `b`, `c` are continuous. Let `u` be `C²` in the domain above
the graph of a smooth `Γ`, with `u` and `∇u` (written `Du`) continuous up to the graph, and
`L u = 0` in the domain. Suppose the Dirichlet data vanish to infinite order at `0`, and the
conormal derivative `a ∇u · n` is bounded by `h(|x|)` on the graph, where `r log(1/h(r)) → ∞`
as `r → 0⁺`. Then `u = 0` near `0`. -/
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
    (hh : Tendsto (fun r => r * Real.log (1 / h r)) (𝓝[>] 0) atTop) :
    ∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → u x = 0 := by
  sorry

/-- **Theorem I(b).** Let `u` be harmonic in the domain above the graph of a smooth `Γ`, with `u`
and `∇u` (written `Du`) continuous up to the graph. Suppose the Dirichlet data vanish to infinite
order at `0` and the normal derivative is bounded by `h(|x|)` on the graph. Assume `h` is positive
and nondecreasing on `(0, ρ)`, and that `Λ(σ) = log(1/h(e^{-σ}))` satisfies `Λ(σ)/σ → ∞`, is convex
for large `σ`, and has at most exponential growth `Λ(σ + t) ≤ e^{C t} Λ(σ)` (that is, `Λ' ≤ C Λ`).
If `∫₀ log h = -∞`, then `u = 0` near `0`. -/
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
    (hΛ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => Real.log (1 / h (Real.exp (-σ)))))
    (hΛ_growth : ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ t ≥ 0,
      Real.log (1 / h (Real.exp (-(σ + t)))) ≤ Real.exp (C * t) * Real.log (1 / h (Real.exp (-σ))))
    (hlog : Tendsto (fun ε => ∫ r in ε..ρ, Real.log (h r)) (𝓝[>] 0) atBot) :
    ∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → u x = 0 := by
  sorry

end MazyaRefinedCauchy
