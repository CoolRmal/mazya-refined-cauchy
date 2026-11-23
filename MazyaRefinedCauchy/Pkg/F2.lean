module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F2

The theorems stated in this file are the frozen contract of package F2 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F2: the Carleman conjugation identities (Lemma 2.1 of the note, with a density)

For a density `μ`, a matrix field `B`, a weight `φ` and `τ : ℝ`, put `V = B ∇φ`,
`q = ⟪B ∇φ, ∇φ⟫`, `div_μ W = μ⁻¹ div(μ W)`, and
`S w = div_μ(B ∇w) + τ² q w`, `T w = -2τ ⟪V, ∇w⟫ - τ (div_μ V) w`. -/

/-- `V = B ∇φ`. -/
noncomputable def carlV (B : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (x : Space n) :
    Space n :=
  B x (gradient φ x)

/-- `q = ⟪B ∇φ, ∇φ⟫`. -/
noncomputable def carlQ (B : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (x : Space n) : ℝ :=
  ⟪B x (gradient φ x), gradient φ x⟫_ℝ

/-- The weighted divergence `div_μ W = μ⁻¹ div(μ W)`. -/
noncomputable def divMu (μ : Space n → ℝ) (W : Space n → Space n) (x : Space n) : ℝ :=
  (μ x)⁻¹ * divergence (fun y => μ y • W y) x

/-- The symmetric part `S w = div_μ(B ∇w) + τ² q w` of the conjugated operator. -/
noncomputable def carlS (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n) : ℝ :=
  divMu μ (fun y => B y (gradient w y)) x + τ ^ 2 * carlQ B φ x * w x

/-- The antisymmetric part `T w = -2τ ⟪V, ∇w⟫ - τ (div_μ V) w` of the conjugated operator. -/
noncomputable def carlT (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n) : ℝ :=
  -2 * τ * ⟪carlV B φ x, gradient w x⟫_ℝ - τ * divMu μ (carlV B φ) x * w x

/-- The bulk term of `2 ∫ S w T w μ`. -/
noncomputable def carlJ (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n) : ℝ :=
  μ x * (2 * τ ^ 3 * ⟪carlV B φ x, gradient (carlQ B φ) x⟫_ℝ * w x ^ 2
    + 4 * τ * ⟪fderiv ℝ (carlV B φ) x (B x (gradient w x)), gradient w x⟫_ℝ
    - 2 * τ * ⟪fderiv ℝ B x (carlV B φ x) (gradient w x), gradient w x⟫_ℝ
    + 2 * τ * w x * ⟪B x (gradient w x), gradient (divMu μ (carlV B φ)) x⟫_ℝ)

/-- The flux of `2 S w T w μ`: `2 S w T w μ = carlJ + div carlFlux`. -/
noncomputable def carlFlux (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n) : Space n :=
  μ x • ((-4 * τ * ⟪carlV B φ x, gradient w x⟫_ℝ) • B x (gradient w x)
    + (2 * τ * ⟪B x (gradient w x), gradient w x⟫_ℝ) • carlV B φ x
    - (2 * τ * divMu μ (carlV B φ) x * w x) • B x (gradient w x)
    - (2 * τ ^ 3 * carlQ B φ x * w x ^ 2) • carlV B φ x)

/-- Lemma 2.1(1): conjugation. -/
theorem carleman_conj (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 1 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 1 B x)
    (hφ : ContDiffAt ℝ 2 φ x) (hw : ContDiffAt ℝ 2 w x) :
    Real.exp (τ * φ x)
        * divMu μ (fun y => B y (gradient (fun z => Real.exp (-τ * φ z) * w z) y)) x
      = carlS μ B φ τ w x + carlT μ B φ τ w x := by
  sorry

/-- Lemma 2.1(2), pointwise: `2 (S w)(T w) μ = J + div(flux)`. Requires `B` symmetric. -/
theorem carleman_pointwise (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 2 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 2 B x)
    (hsymm : ∀ y ξ η, ⟪B y ξ, η⟫_ℝ = ⟪ξ, B y η⟫_ℝ)
    (hφ : ContDiffAt ℝ 3 φ x) (hw : ContDiffAt ℝ 2 w x) :
    2 * carlS μ B φ τ w x * carlT μ B φ τ w x * μ x
      = carlJ μ B φ τ w x + divergence (carlFlux μ B φ τ w) x := by
  sorry

/-- Lemma 2.1(3), pointwise: for a scalar `ϱ`,
`ϱ μ ⟪B ∇w, ∇w⟫ = -(S w) ϱ w μ + τ² q ϱ w² μ - μ w ⟪B ∇w, ∇ϱ⟫ + div(μ ϱ w B ∇w)`. -/
theorem carleman_gradient_pointwise (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w ϱ : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 1 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 1 B x)
    (hw : ContDiffAt ℝ 2 w x) (hϱ : ContDiffAt ℝ 1 ϱ x) :
    ϱ x * μ x * ⟪B x (gradient w x), gradient w x⟫_ℝ
      = -(carlS μ B φ τ w x * ϱ x * w x * μ x) + τ ^ 2 * carlQ B φ x * ϱ x * w x ^ 2 * μ x
        - μ x * w x * ⟪B x (gradient w x), gradient ϱ x⟫_ℝ
        + divergence (fun y => (μ y * ϱ y * w y) • B y (gradient w y)) x := by
  sorry

end MazyaRefinedCauchy
