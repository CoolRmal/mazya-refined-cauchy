module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F5


@[expose] public section

/-!
# Work package G

The theorems stated in this file are the frozen contract of package G (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package G: glue lemmas used by the assembly -/

/-- Restricting a half-ball solution to a smaller radius. -/
noncomputable def HalfBallSolution.shrink (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) : HalfBallSolution n where
  A := S.A
  B := S.B
  C := S.C
  lam := S.lam
  K := S.K
  coeffs := S.coeffs
  A_zero := S.A_zero
  R := R'
  R_pos := hR'
  conormal := fun x hx => S.conormal x ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  v := S.v
  Dv := S.Dv
  v_contDiffOn := S.v_contDiffOn.mono fun _ hx => ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  v_continuousOn := S.v_continuousOn.mono fun _ hx => ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  Dv_continuousOn := S.Dv_continuousOn.mono fun _ hx => ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  gradient_eq := fun x hx => S.gradient_eq x ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  eqn := fun x hx => S.eqn x ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  dirichlet_flat := fun N => (S.dirichlet_flat N).imp fun _ hC x hx =>
    hC x ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩

theorem HalfBallSolution.shrink_R (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) : (S.shrink R' hR' hle).R = R' := rfl

theorem HalfBallSolution.shrink_data (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) :
    (S.shrink R' hR' hle).A = S.A ∧ (S.shrink R' hR' hle).v = S.v ∧
      (S.shrink R' hR' hle).Dv = S.Dv := ⟨rfl, rfl, rfl⟩

/-- Rescaling a regular profile: `r ↦ κ g(κ r)` is again regular, positive and nondecreasing. -/
theorem RegularProfile.scale (g : ℝ → ℝ) (κ : ℝ) (hκ : 1 ≤ κ) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (hg_mono : MonotoneOn g (Set.Ioi 0)) (hg : RegularProfile g) :
    RegularProfile (fun r => κ * g (κ * r)) := by
  sorry

/-- If `r log(1/g(r)) → ∞`, then `r⁻² √(g(Cr))` is eventually below every `e^{-N/r}`. -/
theorem superexp_of_tendsto (g : ℝ → ℝ) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (hg : Tendsto (fun r => r * Real.log (1 / g r)) (𝓝[>] 0) atTop) (C : ℝ) (hC : 0 < C)
    (N : ℝ) : ∀ᶠ r in 𝓝[>] 0, (r ^ 2)⁻¹ * Real.sqrt (g (C * r)) ≤ Real.exp (-N / r) := by
  sorry

end MazyaRefinedCauchy
