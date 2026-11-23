module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F1

The theorems stated in this file are the frozen contract of package F1 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F1: coordinates and integration by parts on half-spaces -/

/-- The point of `ℝⁿ⁺¹` with horizontal coordinates `y ∈ ℝⁿ` and vertical coordinate `t`. -/
noncomputable def lift (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Space n :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => y i) t)

theorem vcoord_lift (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) : vcoord (lift y t) = t := by
  sorry

theorem norm_lift_sq (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖lift y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  sorry

/-- Fubini in the splitting `ℝⁿ⁺¹ = ℝⁿ × ℝ`. -/
theorem integral_eq_integral_lift (f : Space n → ℝ) (hf : Integrable f) :
    ∫ x, f x = ∫ y : EuclideanSpace ℝ (Fin n), ∫ t : ℝ, f (lift y t) := by
  sorry

/-- Divergence theorem on the half-space `{t > η}` for a compactly supported field that is `C¹`
on a neighbourhood of the closed half-space; the outer normal is `-e_d`. -/
theorem integral_divergence_halfSpace (η : ℝ) (F : Space n → Space n)
    (hF : ∀ x, η ≤ vcoord x → ContDiffAt ℝ 1 F x) (hsupp : HasCompactSupport F) :
    ∫ x in {x : Space n | η < vcoord x}, divergence F x
      = -∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y η), ed n⟫_ℝ := by
  sorry

/-- Divergence theorem on `{t > 0}` for a compactly supported field that is `C¹` in the open
half-space and only continuous up to `{t = 0}`, provided its divergence is integrable. -/
theorem integral_divergence_halfSpace_of_continuousOn (F : Space n → Space n)
    (hF : ∀ x, 0 < vcoord x → ContDiffAt ℝ 1 F x)
    (hFc : ContinuousOn F {x | 0 ≤ vcoord x}) (hsupp : HasCompactSupport F)
    (hint : IntegrableOn (divergence F) {x | 0 < vcoord x}) :
    ∫ x in {x : Space n | 0 < vcoord x}, divergence F x
      = -∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y 0), ed n⟫_ℝ := by
  sorry

/-- The integral of the divergence of a compactly supported `C¹` field vanishes. -/
theorem integral_divergence_eq_zero (F : Space n → Space n) (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) : ∫ x, divergence F x = 0 := by
  sorry

end MazyaRefinedCauchy
