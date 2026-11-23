module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F5

The theorems stated in this file are the frozen contract of package F5 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F5: regular profiles and the majorant -/

/-- Regularity of a decay profile `h`: `Λ(σ) = log(1/h(e^{-σ}))` is eventually convex,
superlinear, and satisfies `Λ(σ + t) ≤ e^{Ct} Λ(σ)` for large `σ` and `t ≥ 0`. -/
structure RegularProfile (h : ℝ → ℝ) : Prop where
  convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => Real.log (1 / h (Real.exp (-σ))))
  super : Tendsto (fun σ => Real.log (1 / h (Real.exp (-σ))) / σ) atTop atTop
  growth : ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ t ≥ 0,
    Real.log (1 / h (Real.exp (-(σ + t)))) ≤ Real.exp (C * t) * Real.log (1 / h (Real.exp (-σ)))

/-- A profile with `h(r) ≤ e^{-M/r}` eventually, for every `M`, has a positive, nondecreasing,
regular majorant `g` with `r log(1/g(r)) → ∞`. -/
theorem exists_regular_majorant (h : ℝ → ℝ)
    (hh : ∀ M : ℝ, ∀ᶠ r in 𝓝[>] 0, h r ≤ Real.exp (-M / r)) :
    ∃ g : ℝ → ℝ, ∃ r₀ > 0, (∀ r ∈ Set.Ioo 0 r₀, h r ≤ g r) ∧ (∀ r, 0 < r → 0 < g r) ∧
      MonotoneOn g (Set.Ioi 0) ∧ RegularProfile g ∧
      Tendsto (fun r => r * Real.log (1 / g r)) (𝓝[>] 0) atTop := by
  sorry

end MazyaRefinedCauchy
