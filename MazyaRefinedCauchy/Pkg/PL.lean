module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F2
public import MazyaRefinedCauchy.Pkg.G

@[expose] public section

/-!
# Work package PL

The theorems stated in this file are the frozen contract of package PL (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## Plan of the proof (Proposition PL of the note)

All helpers live in the namespace `MazyaRefinedCauchy.PL`.

1. *Inversion.* `invMap y = y / ‖y‖²` is an involution; it maps the tangent ball
   `B(r e_d, r)` onto the half-space `H n (1/(2r)) = {y_d > 1/(2r)}` and back
   (`invMap_mem_ball`, `invMap_mem_H`), and `B(r e_d, r) ⊆ halfBall n (2r)`.
2. *Transformed equation.* For `U = v ∘ invMap`,
   `ellOp (tA A) (tB A B) (tC C) U y = ‖y‖⁻⁴ (ellOp A B C v) (invMap y)` (`ellOp_comp_invMap`),
   and the coefficients satisfy the bounds `CarlCoeffs` of the half-space Carleman estimate
   (`carlCoeffs_t`).
3. *Carleman estimate in a half-space* (`carleman`, from `carleman_P0`), weight
   `gw C₀ s = s - C₀ log s`.
4. *Cutoff argument* (`PL_core`): with `v_M = cutM l M · U`, the Carleman estimate, the bound
   `cutoff_bound` for the commutator, and the decay on shells give `U = 0` on `H n (l + 3)`.
5. *Decay on shells* (`shell_decay`): change of variables `x = invMap y` in the decay hypothesis.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

namespace PL

/-! ### The inversion `Φ(y) = y / ‖y‖²` -/

/-- The inversion `Φ(y) = y / ‖y‖²` (with `Φ 0 = 0`). -/
noncomputable def invMap (y : Space n) : Space n := (‖y‖ ^ 2)⁻¹ • y

theorem norm_invMap (y : Space n) : ‖invMap y‖ = ‖y‖⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [invMap]
  · have h : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [invMap, norm_smul, norm_inv, norm_pow, norm_norm]
    field_simp

theorem invMap_invMap (y : Space n) : invMap (invMap y) = y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [invMap]
  · have h : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
    rw [invMap, norm_invMap, invMap, smul_smul, inv_pow, inv_inv, mul_inv_cancel₀ h2, one_smul]

theorem vcoord_invMap (y : Space n) : vcoord (invMap y) = vcoord y / ‖y‖ ^ 2 := by
  simp only [vcoord, invMap, PiLp.smul_apply, smul_eq_mul]
  ring

theorem invMap_ne_zero {y : Space n} (hy : y ≠ 0) : invMap y ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [norm_invMap, norm_zero] at this
  exact inv_ne_zero (norm_ne_zero_iff.mpr hy) this

theorem invMap_eq_inversion :
    (invMap : Space n → Space n) = EuclideanGeometry.inversion (0 : Space n) 1 := by
  funext y
  simp only [invMap, EuclideanGeometry.inversion, dist_zero_right, vsub_eq_sub, sub_zero,
    vadd_eq_add, add_zero, one_div]
  rw [inv_pow]

/-! ### Half-spaces and tangent balls -/

/-- The open half-space `{y_d > l}`. -/
def H (n : ℕ) (l : ℝ) : Set (Space n) := {y | l < vcoord y}

theorem isOpen_H (l : ℝ) : IsOpen (H n l) := isOpen_lt continuous_const F1.continuous_vcoord

theorem measurableSet_H (l : ℝ) : MeasurableSet (H n l) := (isOpen_H l).measurableSet

theorem H_mono {l l' : ℝ} (h : l ≤ l') : H n l' ⊆ H n l := fun _ hy => lt_of_le_of_lt h hy

theorem vcoord_le_norm (y : Space n) : vcoord y ≤ ‖y‖ := by
  have h := PiLp.norm_apply_le y (Fin.last n)
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

theorem ne_zero_of_mem_H {l : ℝ} (hl : 0 ≤ l) {y : Space n} (hy : y ∈ H n l) : y ≠ 0 := by
  rintro rfl
  have : l < vcoord (0 : Space n) := hy
  simp [vcoord] at this
  linarith

theorem norm_ed : ‖ed n‖ = 1 := by simp [ed]

theorem norm_sub_smul_ed_sq (x : Space n) (r : ℝ) :
    ‖x - r • ed n‖ ^ 2 = ‖x‖ ^ 2 - 2 * r * vcoord x + r ^ 2 := by
  rw [@norm_sub_sq_real, inner_smul_right, F1.inner_ed, norm_smul, norm_ed, mul_one,
    Real.norm_eq_abs, sq_abs]
  simp only [vcoord]
  ring

theorem isOpen_halfBall (R : ℝ) : IsOpen (halfBall n R) :=
  show IsOpen ({x : Space n | ‖x‖ < R} ∩ {x | 0 < vcoord x}) from
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const F1.continuous_vcoord)

theorem halfBall_mono {R R' : ℝ} (h : R ≤ R') : halfBall n R ⊆ halfBall n R' :=
  fun _ hx => ⟨lt_of_lt_of_le hx.1 h, hx.2⟩

theorem mem_ball_iff {r : ℝ} (hr : 0 < r) (x : Space n) :
    x ∈ Metric.ball (r • ed n) r ↔ ‖x‖ ^ 2 < 2 * r * vcoord x := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hsq := norm_sub_smul_ed_sq x r
  constructor
  · intro h
    have h0 : 0 ≤ ‖x - r • ed n‖ := norm_nonneg _
    have : ‖x - r • ed n‖ ^ 2 < r ^ 2 := by nlinarith
    linarith
  · intro h
    have h1 : ‖x - r • ed n‖ ^ 2 < r ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 hr.le h1

theorem invMap_mem_ball {r : ℝ} (hr : 0 < r) {y : Space n} (hy : y ∈ H n (1 / (2 * r))) :
    invMap y ∈ Metric.ball (r • ed n) r := by
  have hy0 : y ≠ 0 := ne_zero_of_mem_H (by positivity) hy
  have hN : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have h1 : 1 < 2 * r * vcoord y := by
    have : 1 / (2 * r) < vcoord y := hy
    rw [div_lt_iff₀ (by positivity)] at this
    linarith
  rw [mem_ball_iff hr, norm_invMap, vcoord_invMap, inv_pow, ← mul_div_assoc,
    lt_div_iff₀ (by positivity), inv_mul_cancel₀ (by positivity)]
  exact h1

theorem invMap_mem_H {r : ℝ} (hr : 0 < r) {x : Space n} (hx : x ∈ Metric.ball (r • ed n) r) :
    invMap x ∈ H n (1 / (2 * r)) := by
  rw [mem_ball_iff hr] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [vcoord] at hx
  have hN : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  show 1 / (2 * r) < vcoord (invMap x)
  rw [vcoord_invMap, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem ball_subset_halfBall {r : ℝ} (hr : 0 < r) :
    Metric.ball (r • ed n) r ⊆ halfBall n (2 * r) := by
  intro x hx
  have hx' := (mem_ball_iff hr x).mp hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [vcoord] at hx'
  have hN : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨?_, ?_⟩
  · have hb : ‖x - r • ed n‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    calc ‖x‖ = ‖(x - r • ed n) + r • ed n‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - r • ed n‖ + ‖r • ed n‖ := norm_add_le _ _
      _ < r + r := by
          rw [norm_smul, norm_ed, mul_one, Real.norm_of_nonneg hr.le]
          linarith
      _ = 2 * r := by ring
  · show 0 < vcoord x
    by_contra h
    push Not at h
    have : 0 < ‖x‖ ^ 2 := by positivity
    nlinarith

/-! ### The derivative of the inversion -/

/-- The reflection `ℛ(y) = I - 2 ŷ ŷᵀ`. -/
noncomputable def refl (y : Space n) : Space n →L[ℝ] Space n :=
  ContinuousLinearMap.id ℝ (Space n) - (2 * (‖y‖ ^ 2)⁻¹) • (innerSL ℝ y).smulRight y

theorem refl_apply (y ξ : Space n) : refl y ξ = ξ - (2 * (‖y‖ ^ 2)⁻¹ * ⟪y, ξ⟫_ℝ) • y := by
  simp [refl, smul_smul]

theorem inner_refl_refl {y : Space n} (hy : y ≠ 0) (ξ η : Space n) :
    ⟪refl y ξ, refl y η⟫_ℝ = ⟪ξ, η⟫_ℝ := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have hyy : ⟪y, y⟫_ℝ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  simp only [refl_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hyy]
  rw [real_inner_comm ξ y, real_inner_comm η y]
  field_simp
  ring

theorem refl_symm (y ξ η : Space n) : ⟪refl y ξ, η⟫_ℝ = ⟪ξ, refl y η⟫_ℝ := by
  simp only [refl_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm ξ y, real_inner_comm η y]
  ring

theorem norm_refl_apply {y : Space n} (hy : y ≠ 0) (ξ : Space n) : ‖refl y ξ‖ = ‖ξ‖ := by
  have h := inner_refl_refl hy ξ ξ
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h1 : 0 ≤ ‖refl y ξ‖ := norm_nonneg _
  have h2 : 0 ≤ ‖ξ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖refl y ξ‖ - ‖ξ‖), sq_nonneg (‖refl y ξ‖ + ‖ξ‖)]

theorem hasFDerivAt_invMap {y : Space n} (hy : y ≠ 0) :
    HasFDerivAt invMap ((‖y‖ ^ 2)⁻¹ • refl y) y := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun x : Space n => ‖x‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hinv := (hasDerivAt_inv h2).comp_hasFDerivAt y h1
  have h3 := hinv.smul (hasFDerivAt_id y)
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun ξ => ?_
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, refl_apply, innerSL_apply_apply, Function.comp_apply, id]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  module

theorem contDiffAt_invMap {y : Space n} (hy : y ≠ 0) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k invMap y := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have : ContDiffAt ℝ k (fun x : Space n => (‖x‖ ^ 2)⁻¹) y :=
    (contDiff_norm_sq ℝ).contDiffAt.inv h2
  exact this.smul contDiffAt_id

/-! ### The transformed equation -/

/-- The transformed principal coefficient `Ã = ℛ (A ∘ Φ) ℛ`. -/
noncomputable def tA (A : Space n → Space n →L[ℝ] Space n) (y : Space n) :
    Space n →L[ℝ] Space n :=
  refl y ∘L A (invMap y) ∘L refl y

/-- The transformed drift `b̃ = (4 - 2d) Ã y / ‖y‖² + ℛ (B ∘ Φ) / ‖y‖²` (with `d = n + 1`). -/
noncomputable def tB (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n)
    (y : Space n) : Space n :=
  ((4 - 2 * ((n : ℝ) + 1)) * (‖y‖ ^ 2)⁻¹) • tA A y y + (‖y‖ ^ 2)⁻¹ • refl y (B (invMap y))

/-- The transformed potential `c̃ = (C ∘ Φ) / ‖y‖⁴`. -/
noncomputable def tC (C : Space n → ℝ) (y : Space n) : ℝ := (‖y‖ ^ 4)⁻¹ * C (invMap y)

theorem tA_symm (A : Space n → Space n →L[ℝ] Space n)
    (hsymm : ∀ x ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ) (y ξ η : Space n) :
    ⟪tA A y ξ, η⟫_ℝ = ⟪ξ, tA A y η⟫_ℝ := by
  simp only [tA, ContinuousLinearMap.comp_apply]
  rw [refl_symm, hsymm, refl_symm]

/-- The gradient of `v ∘ Φ`: `∇(v ∘ Φ)(y) = ‖y‖⁻² ℛ(y) ∇v(Φ y)`. -/
theorem gradient_comp_invMap (v : Space n → ℝ) {y : Space n} (hy : y ≠ 0)
    (hv : DifferentiableAt ℝ v (invMap y)) :
    gradient (v ∘ invMap) y = (‖y‖ ^ 2)⁻¹ • refl y (gradient v (invMap y)) := by
  have hc : HasFDerivAt (v ∘ invMap) ((fderiv ℝ v (invMap y)).comp ((‖y‖ ^ 2)⁻¹ • refl y)) y :=
    hv.hasFDerivAt.comp y (hasFDerivAt_invMap hy)
  refine ext_inner_right ℝ fun ξ => ?_
  rw [inner_gradient_left, hc.fderiv, ContinuousLinearMap.comp_apply,
    smul_apply, map_smul, ← inner_gradient_left, real_inner_smul_left, refl_symm, smul_eq_mul]

/-- **Lemma inversion (pointwise form).** The operator transforms under `Φ` as
`L̃(v ∘ Φ)(y) = ‖y‖⁻⁴ (L v)(Φ y)`. -/
theorem ellOp_comp_invMap (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n)
    (C : Space n → ℝ) (hA : ContDiff ℝ 1 A) (hsymm : ∀ x ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (v : Space n → ℝ) {y : Space n} (hy : y ≠ 0) (hv : ContDiffAt ℝ 2 v (invMap y)) :
    ellOp (tA A) (tB A B) (tC C) (v ∘ invMap) y = (‖y‖ ^ 4)⁻¹ * ellOp A B C v (invMap y) := by
  sorry

/-! ### Coefficient bounds for the half-space Carleman estimate -/

/-- Bounds on the coefficients of `ellOp A β γ` on the half-space `H n l` (Proposition carleman,
with `|y|` replaced by the smaller `y_d`). -/
structure CarlCoeffs (A : Space n → Space n →L[ℝ] Space n) (β : Space n → Space n)
    (γ : Space n → ℝ) (K l : ℝ) : Prop where
  contDiffAt : ∀ y ∈ H n l, ContDiffAt ℝ 2 A y
  symm : ∀ y ∈ H n l, ∀ ξ η : Space n, ⟪A y ξ, η⟫_ℝ = ⟪ξ, A y η⟫_ℝ
  bound_A : ∀ y ∈ H n l, ‖A y - ContinuousLinearMap.id ℝ (Space n)‖ ≤ K / vcoord y
  bound_dA : ∀ y ∈ H n l, ‖fderiv ℝ A y‖ ≤ K / vcoord y ^ 2
  bound_d2A : ∀ y ∈ H n l, ‖iteratedFDeriv ℝ 2 A y‖ ≤ K / vcoord y ^ 3
  cont_β : ContinuousOn β (H n l)
  cont_γ : ContinuousOn γ (H n l)
  bound_β : ∀ y ∈ H n l, ‖β y‖ ≤ K / vcoord y
  bound_γ : ∀ y ∈ H n l, |γ y| ≤ K / vcoord y

theorem CarlCoeffs.mono {A : Space n → Space n →L[ℝ] Space n} {β : Space n → Space n}
    {γ : Space n → ℝ} {K l l' : ℝ} (h : CarlCoeffs A β γ K l) (hl : l ≤ l') :
    CarlCoeffs A β γ K l' where
  contDiffAt y hy := h.contDiffAt y (H_mono hl hy)
  symm y hy := h.symm y (H_mono hl hy)
  bound_A y hy := h.bound_A y (H_mono hl hy)
  bound_dA y hy := h.bound_dA y (H_mono hl hy)
  bound_d2A y hy := h.bound_d2A y (H_mono hl hy)
  cont_β := h.cont_β.mono (H_mono hl)
  cont_γ := h.cont_γ.mono (H_mono hl)
  bound_β y hy := h.bound_β y (H_mono hl hy)
  bound_γ y hy := h.bound_γ y (H_mono hl hy)

/-- Regularity and size bounds of the transformed coefficients on `{‖y‖ ≥ 1}` (Lemma inversion). -/
theorem coeff_bounds (S : HalfBallSolution n) : ∃ K' : ℝ, 0 ≤ K' ∧ ∀ y : Space n, 1 ≤ ‖y‖ →
    ‖tA S.A y - ContinuousLinearMap.id ℝ (Space n)‖ ≤ K' / ‖y‖ ∧
    ‖fderiv ℝ (tA S.A) y‖ ≤ K' / ‖y‖ ^ 2 ∧
    ‖iteratedFDeriv ℝ 2 (tA S.A) y‖ ≤ K' / ‖y‖ ^ 3 ∧
    ‖tB S.A S.B y‖ ≤ K' / ‖y‖ ∧
    |tC S.C y| ≤ K' / ‖y‖ ^ 2 := by
  sorry

theorem contDiffAt_refl {y : Space n} (hy : y ≠ 0) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (refl (n := n)) y := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have hinv : ContDiffAt ℝ k (fun x : Space n => 2 * (‖x‖ ^ 2)⁻¹) y :=
    contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.inv h2)
  have hin : ContDiff ℝ k (fun x : Space n => innerSL ℝ x) :=
    (innerSL ℝ : Space n →L[ℝ] Space n →L[ℝ] ℝ).contDiff
  have hsr : ContDiffAt ℝ k (fun x : Space n => (innerSL ℝ x).smulRight x) y :=
    (hin.smulRight contDiff_id).contDiffAt
  exact contDiffAt_const.sub (hinv.smul hsr)

theorem contDiffAt_tA (A : Space n → Space n →L[ℝ] Space n) (hA : ContDiff ℝ 2 A) {y : Space n}
    (hy : y ≠ 0) : ContDiffAt ℝ 2 (tA A) y := by
  have hR : ContDiffAt ℝ 2 (refl (n := n)) y := contDiffAt_refl hy
  have hAi : ContDiffAt ℝ 2 (fun x => A (invMap x)) y :=
    hA.contDiffAt.comp y (contDiffAt_invMap hy)
  exact hR.clm_comp (hAi.clm_comp hR)

theorem continuousAt_tA (A : Space n → Space n →L[ℝ] Space n) (hA : Continuous A) {y : Space n}
    (hy : y ≠ 0) : ContinuousAt (tA A) y := by
  have hR : ContinuousAt (refl (n := n)) y := (contDiffAt_refl hy (k := 0)).continuousAt
  have hAi : ContinuousAt (fun x => A (invMap x)) y :=
    hA.continuousAt.comp (contDiffAt_invMap hy (k := 0)).continuousAt
  exact hR.clm_comp (hAi.clm_comp hR)

theorem continuousAt_tB (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n)
    (hA : Continuous A) (hB : Continuous B) {y : Space n} (hy : y ≠ 0) :
    ContinuousAt (tB A B) y := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have hinv : ContinuousAt (fun x : Space n => (‖x‖ ^ 2)⁻¹) y :=
    ((continuous_norm.pow 2).continuousAt).inv₀ h2
  have hR : ContinuousAt (refl (n := n)) y := (contDiffAt_refl hy (k := 0)).continuousAt
  have hBi : ContinuousAt (fun x => B (invMap x)) y :=
    hB.continuousAt.comp (contDiffAt_invMap hy (k := 0)).continuousAt
  have h1 : ContinuousAt (fun x => tA A x x) y :=
    (continuousAt_tA A hA hy).clm_apply continuousAt_id
  have h3 : ContinuousAt (fun x => refl x (B (invMap x))) y := hR.clm_apply hBi
  exact ((continuousAt_const.mul hinv).smul h1).add (hinv.smul h3)

theorem continuousAt_tC (C : Space n → ℝ) (hC : Continuous C) {y : Space n} (hy : y ≠ 0) :
    ContinuousAt (tC C) y := by
  have h4 : ‖y‖ ^ 4 ≠ 0 := by positivity
  have hinv : ContinuousAt (fun x : Space n => (‖x‖ ^ 4)⁻¹) y :=
    ((continuous_norm.pow 4).continuousAt).inv₀ h4
  exact hinv.mul (hC.continuousAt.comp (contDiffAt_invMap hy (k := 0)).continuousAt)

/-- The transformed coefficients satisfy the hypotheses of the half-space Carleman estimate on
`H n 1`. -/
theorem carlCoeffs_t (S : HalfBallSolution n) :
    ∃ K' : ℝ, 0 ≤ K' ∧ CarlCoeffs (tA S.A) (tB S.A S.B) (tC S.C) K' 1 := by
  obtain ⟨K', hK', hb⟩ := coeff_bounds S
  have hpos : ∀ y ∈ H n 1, 0 < vcoord y := fun y hy => lt_trans one_pos hy
  have hle : ∀ y ∈ H n 1, vcoord y ≤ ‖y‖ := fun y _ => vcoord_le_norm y
  have h1 : ∀ y ∈ H n 1, 1 ≤ ‖y‖ := fun y hy => le_trans (le_of_lt hy) (vcoord_le_norm y)
  have hne : ∀ y ∈ H n 1, y ≠ 0 := fun y hy => ne_zero_of_mem_H zero_le_one hy
  refine ⟨K', hK', ?_⟩
  exact
    { contDiffAt := fun y hy => contDiffAt_tA S.A S.coeffs.contDiff_A (hne y hy)
      symm := fun y _ ξ η => tA_symm S.A S.coeffs.symm y ξ η
      bound_A := fun y hy => by
        refine (hb y (h1 y hy)).1.trans ?_
        have := hpos y hy; have := hle y hy
        gcongr
      bound_dA := fun y hy => by
        refine (hb y (h1 y hy)).2.1.trans ?_
        have := hpos y hy; have := hle y hy
        gcongr
      bound_d2A := fun y hy => by
        refine (hb y (h1 y hy)).2.2.1.trans ?_
        have := hpos y hy; have := hle y hy
        gcongr
      cont_β := fun y hy => (continuousAt_tB S.A S.B S.coeffs.contDiff_A.continuous
        S.coeffs.cont_B (hne y hy)).continuousWithinAt
      cont_γ := fun y hy => (continuousAt_tC S.C S.coeffs.cont_C (hne y hy)).continuousWithinAt
      bound_β := fun y hy => by
        refine (hb y (h1 y hy)).2.2.2.1.trans ?_
        have := hpos y hy; have := hle y hy
        gcongr
      bound_γ := fun y hy => by
        refine (hb y (h1 y hy)).2.2.2.2.trans ?_
        have h0 := hpos y hy
        have hl := hle y hy
        have hy1 := h1 y hy
        calc K' / ‖y‖ ^ 2 ≤ K' / ‖y‖ := by
              apply div_le_div_of_nonneg_left hK' (by linarith)
              nlinarith
          _ ≤ K' / vcoord y := by gcongr }

/-- The weight `g(s) = s - C₀ log s`. -/
noncomputable def gw (C₀ s : ℝ) : ℝ := s - C₀ * Real.log s

/-! ### Locality and integrability helpers -/

theorem eventually_eq_zero_of_not_mem_tsupport {v : Space n → ℝ} {y : Space n}
    (hy : y ∉ tsupport v) : ∀ᶠ z in 𝓝 y, z ∉ tsupport v :=
  (isClosed_tsupport v).isOpen_compl.mem_nhds hy

theorem eventually_gradient_eq_zero {v : Space n → ℝ} {y : Space n} (hy : y ∉ tsupport v) :
    ∀ᶠ z in 𝓝 y, gradient v z = 0 := by
  filter_upwards [eventually_eq_zero_of_not_mem_tsupport hy] with z hz
  have h0 : v =ᶠ[𝓝 z] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hz
  rw [h0.gradient_eq, gradient_fun_const]

theorem divergence_eq_zero_of_not_mem_tsupport (A : Space n → Space n →L[ℝ] Space n)
    {v : Space n → ℝ} {y : Space n} (hy : y ∉ tsupport v) :
    divergence (fun z => A z (gradient v z)) y = 0 := by
  have h : (fun z => A z (gradient v z)) =ᶠ[𝓝 y] fun _ => (0 : Space n) := by
    filter_upwards [eventually_gradient_eq_zero hy] with z hz
    rw [hz, map_zero]
  rw [F2.divergence_congr h]
  simp [divergence]

theorem ellOp_eq_zero_of_not_mem_tsupport (A : Space n → Space n →L[ℝ] Space n)
    (β : Space n → Space n) (γ : Space n → ℝ) {v : Space n → ℝ} {y : Space n}
    (hy : y ∉ tsupport v) : ellOp A β γ v y = 0 := by
  have hg : gradient v y = 0 := (eventually_gradient_eq_zero hy).self_of_nhds
  have hv : v y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp only [ellOp, divergence_eq_zero_of_not_mem_tsupport A hy, hg, hv, inner_zero_right,
    mul_zero, add_zero]

theorem continuousAt_divergence {F : Space n → Space n} {y : Space n} (hF : ContDiffAt ℝ 1 F y) :
    ContinuousAt (fun z => divergence F z) y := by
  have h : ContinuousAt (fderiv ℝ F) y := (hF.fderiv_right (m := 0) (by norm_num)).continuousAt
  exact (F2.traceCLM (n := n)).continuous.continuousAt.comp h

theorem continuous_gradient_of_contDiff {v : Space n → ℝ} (hv : ContDiff ℝ 2 v) :
    Continuous (gradient v) := by
  rw [continuous_iff_continuousAt]
  intro y
  exact (F2.contDiffAt_gradient hv.contDiffAt (m := 0) (by norm_num)).continuousAt

/-- A function continuous on an open set `O ⊇ tsupport v` and vanishing off `tsupport v` is
integrable when `v` has compact support. -/
theorem integrable_of_tsupport {O : Set (Space n)} (hO : IsOpen O) {v : Space n → ℝ}
    (hvc : HasCompactSupport v) (hvO : tsupport v ⊆ O) {f : Space n → ℝ}
    (hf : ContinuousOn f O) (h0 : ∀ y, y ∉ tsupport v → f y = 0) : Integrable f := by
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ O
    · exact hf.continuousAt (hO.mem_nhds hy)
    · have hy' : y ∉ tsupport v := fun h => hy (hvO h)
      have hev : f =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_eq_zero_of_not_mem_tsupport hy'] with z hz
        exact h0 z hz
      exact continuousAt_const.congr hev.symm
  have hcs : HasCompactSupport f := HasCompactSupport.intro hvc fun y hy => h0 y hy
  exact hcont.integrable_of_hasCompactSupport hcs

theorem continuousOn_weight (C₀ τ : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    ContinuousOn (fun y : Space n => Real.exp (2 * τ * gw C₀ (vcoord y))) (H n l) := by
  intro y hy
  have hs : vcoord y ≠ 0 := (lt_of_le_of_lt hl hy).ne'
  have hv : ContinuousAt (vcoord : Space n → ℝ) y := F1.continuous_vcoord.continuousAt
  have hlog : ContinuousAt (fun y : Space n => Real.log (vcoord y)) y :=
    (Real.continuousAt_log hs).comp hv
  refine ContinuousAt.continuousWithinAt ?_
  unfold gw
  exact Real.continuous_exp.continuousAt.comp
    (continuousAt_const.mul (hv.sub (continuousAt_const.mul hlog)))

theorem continuousOn_inv_sq {l : ℝ} (hl : 0 ≤ l) :
    ContinuousOn (fun y : Space n => (vcoord y ^ 2)⁻¹) (H n l) := by
  intro y hy
  have hs : vcoord y ^ 2 ≠ 0 := pow_ne_zero 2 (lt_of_le_of_lt hl hy).ne'
  exact ((F1.continuous_vcoord.pow 2).continuousAt.inv₀ hs).continuousWithinAt

/-! ### The half-space Carleman estimate (Proposition carleman) -/

/-- Proposition carleman for the principal part `P₀ v = div(A ∇v)`. -/
theorem carleman_P0 (K : ℝ) (hK : 0 ≤ K) :
    ∃ C₀ l₁ τ₁ : ℝ, 0 < C₀ ∧ 1 ≤ l₁ ∧ 4 * C₀ ≤ l₁ ∧ 1 ≤ τ₁ ∧
    ∀ l : ℝ, l₁ ≤ l → ∀ (A : Space n → Space n →L[ℝ] Space n) (β : Space n → Space n)
      (γ : Space n → ℝ), CarlCoeffs A β γ K l →
      ∀ τ : ℝ, τ₁ ≤ τ → ∀ v : Space n → ℝ, ContDiff ℝ 2 v → HasCompactSupport v →
        tsupport v ⊆ H n l →
        τ ^ 3 * (∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y)) * v y ^ 2)
          + τ * (∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y))
              * ‖gradient v y‖ ^ 2)
          ≤ 15 * ∫ y, Real.exp (2 * τ * gw C₀ (vcoord y))
              * divergence (fun z => A z (gradient v z)) y ^ 2 := by
  sorry

/-- **Proposition carleman.** -/
theorem carleman (K : ℝ) (hK : 0 ≤ K) :
    ∃ C₀ l₁ τ₁ C₄ : ℝ, 0 < C₀ ∧ 1 ≤ l₁ ∧ 4 * C₀ ≤ l₁ ∧ 1 ≤ τ₁ ∧ 0 < C₄ ∧
    ∀ l : ℝ, l₁ ≤ l → ∀ (A : Space n → Space n →L[ℝ] Space n) (β : Space n → Space n)
      (γ : Space n → ℝ), CarlCoeffs A β γ K l →
      ∀ τ : ℝ, τ₁ ≤ τ → ∀ v : Space n → ℝ, ContDiff ℝ 2 v → HasCompactSupport v →
        tsupport v ⊆ H n l →
        τ ^ 3 * (∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y)) * v y ^ 2)
          + τ * (∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y))
              * ‖gradient v y‖ ^ 2)
          ≤ C₄ * ∫ y, Real.exp (2 * τ * gw C₀ (vcoord y)) * ellOp A β γ v y ^ 2 := by
  obtain ⟨C₀, l₁, τ₁, hC₀, hl₁, hl₁C, hτ₁, hP0⟩ := carleman_P0 (n := n) K hK
  refine ⟨C₀, l₁, max τ₁ (120 * K ^ 2 + 1), 60, hC₀, hl₁, hl₁C, le_trans hτ₁ (le_max_left _ _),
    by norm_num, ?_⟩
  intro l hl A β γ hc τ hτ v hv hvc hvs
  have hτ1 : τ₁ ≤ τ := le_trans (le_max_left _ _) hτ
  have hτK : 120 * K ^ 2 + 1 ≤ τ := le_trans (le_max_right _ _) hτ
  have hl0 : 0 ≤ l := by linarith
  have key := hP0 l hl A β γ hc τ hτ1 v hv hvc hvs
  set E : Space n → ℝ := fun y => Real.exp (2 * τ * gw C₀ (vcoord y)) with hE
  set W : Space n → ℝ := fun y => (vcoord y ^ 2)⁻¹ with hW
  set P : Space n → ℝ := fun y => divergence (fun z => A z (gradient v z)) y with hP
  have hEc : ContinuousOn E (H n l) := continuousOn_weight C₀ τ hl0
  have hWc : ContinuousOn W (H n l) := continuousOn_inv_sq hl0
  have hgc : Continuous (gradient v) := continuous_gradient_of_contDiff hv
  have hPc : ContinuousOn P (H n l) := by
    intro y hy
    have hF : ContDiffAt ℝ 1 (fun z => A z (gradient v z)) y :=
      ((hc.contDiffAt y hy).of_le (by norm_num)).clm_apply
        (F2.contDiffAt_gradient hv.contDiffAt (m := 1) (by norm_num))
    exact (continuousAt_divergence hF).continuousWithinAt
  have hLc : ContinuousOn (fun y => ellOp A β γ v y) (H n l) := by
    have h1 : ContinuousOn (fun y => ⟪β y, gradient v y⟫_ℝ) (H n l) :=
      hc.cont_β.inner hgc.continuousOn
    have h2 : ContinuousOn (fun y => γ y * v y) (H n l) := hc.cont_γ.mul hv.continuous.continuousOn
    exact (hPc.add h1).add h2
  have hv0 : ∀ y, y ∉ tsupport v → v y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hg0 : ∀ y, y ∉ tsupport v → gradient v y = 0 :=
    fun y hy => (eventually_gradient_eq_zero hy).self_of_nhds
  have hP0' : ∀ y, y ∉ tsupport v → P y = 0 :=
    fun y hy => divergence_eq_zero_of_not_mem_tsupport A hy
  have hL0 : ∀ y, y ∉ tsupport v → ellOp A β γ v y = 0 :=
    fun y hy => ellOp_eq_zero_of_not_mem_tsupport A β γ hy
  have hi1 : Integrable (fun y => W y * E y * v y ^ 2) :=
    integrable_of_tsupport (isOpen_H l) hvc hvs
      ((hWc.mul hEc).mul (hv.continuous.continuousOn.pow 2))
      (fun y hy => by simp [hv0 y hy])
  have hi2 : Integrable (fun y => W y * E y * ‖gradient v y‖ ^ 2) :=
    integrable_of_tsupport (isOpen_H l) hvc hvs
      ((hWc.mul hEc).mul ((hgc.norm.pow 2).continuousOn))
      (fun y hy => by simp [hg0 y hy])
  have hi3 : Integrable (fun y => E y * P y ^ 2) :=
    integrable_of_tsupport (isOpen_H l) hvc hvs (hEc.mul (hPc.pow 2))
      (fun y hy => by simp [hP0' y hy])
  have hi4 : Integrable (fun y => E y * ellOp A β γ v y ^ 2) :=
    integrable_of_tsupport (isOpen_H l) hvc hvs (hEc.mul (hLc.pow 2))
      (fun y hy => by simp [hL0 y hy])
  -- pointwise comparison of `P₀ v` and `L̃ v`
  have hpt : ∀ y, E y * P y ^ 2 ≤
      2 * (E y * ellOp A β γ v y ^ 2)
        + 4 * K ^ 2 * (W y * E y * v y ^ 2 + W y * E y * ‖gradient v y‖ ^ 2) := by
    intro y
    have hEy : 0 < E y := Real.exp_pos _
    have hWy : 0 ≤ W y := inv_nonneg.mpr (sq_nonneg _)
    by_cases hy : y ∈ tsupport v
    · have hyH : y ∈ H n l := hvs hy
      have hs : 0 < vcoord y := lt_of_le_of_lt hl0 hyH
      have hβ := hc.bound_β y hyH
      have hγ := hc.bound_γ y hyH
      have hdec : P y = ellOp A β γ v y - ⟪β y, gradient v y⟫_ℝ - γ y * v y := by
        simp only [hP, ellOp]; ring
      have hb1 : |⟪β y, gradient v y⟫_ℝ| ≤ K / vcoord y * ‖gradient v y‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hβ (norm_nonneg _))
      have hb2 : |γ y * v y| ≤ K / vcoord y * |v y| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hγ (abs_nonneg _)
      have hWK : (K / vcoord y) ^ 2 = K ^ 2 * W y := by
        simp only [hW]; field_simp
      have hsq : P y ^ 2 ≤ 2 * ellOp A β γ v y ^ 2
          + 4 * K ^ 2 * W y * (v y ^ 2 + ‖gradient v y‖ ^ 2) := by
        rw [hdec]
        have e1 : ⟪β y, gradient v y⟫_ℝ ^ 2 ≤ (K / vcoord y) ^ 2 * ‖gradient v y‖ ^ 2 := by
          rw [← mul_pow]; exact sq_le_sq' (by linarith [abs_le.mp hb1]) (abs_le.mp hb1).2
        have e2 : (γ y * v y) ^ 2 ≤ (K / vcoord y) ^ 2 * v y ^ 2 := by
          rw [← sq_abs (v y), ← mul_pow]
          exact sq_le_sq' (by linarith [abs_le.mp hb2]) (abs_le.mp hb2).2
        rw [hWK] at e1 e2
        nlinarith [sq_nonneg (ellOp A β γ v y + ⟪β y, gradient v y⟫_ℝ + γ y * v y),
          sq_nonneg (⟪β y, gradient v y⟫_ℝ - γ y * v y)]
      calc E y * P y ^ 2 ≤ E y * (2 * ellOp A β γ v y ^ 2
              + 4 * K ^ 2 * W y * (v y ^ 2 + ‖gradient v y‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq hEy.le
        _ = _ := by ring
    · rw [hP0' y hy, hL0 y hy, hv0 y hy, hg0 y hy]
      simp
  have h3 : ∫ y, E y * P y ^ 2 ≤
      2 * (∫ y, E y * ellOp A β γ v y ^ 2)
        + 4 * K ^ 2 * ((∫ y, W y * E y * v y ^ 2) + ∫ y, W y * E y * ‖gradient v y‖ ^ 2) := by
    have hs12 : Integrable (fun y => W y * E y * v y ^ 2 + W y * E y * ‖gradient v y‖ ^ 2) :=
      hi1.add hi2
    have hg1 : Integrable (fun y => 2 * (E y * ellOp A β γ v y ^ 2)) := hi4.const_mul 2
    have hg2 : Integrable (fun y => 4 * K ^ 2 *
        (W y * E y * v y ^ 2 + W y * E y * ‖gradient v y‖ ^ 2)) := hs12.const_mul _
    have hg : Integrable (fun y => 2 * (E y * ellOp A β γ v y ^ 2) + 4 * K ^ 2 *
        (W y * E y * v y ^ 2 + W y * E y * ‖gradient v y‖ ^ 2)) := hg1.add hg2
    have hm := integral_mono hi3 hg hpt
    rw [integral_add hg1 hg2, integral_const_mul, integral_const_mul, integral_add hi1 hi2] at hm
    exact hm
  have hI1 : 0 ≤ ∫ y, W y * E y * v y ^ 2 :=
    integral_nonneg fun y => by
      have : 0 ≤ W y := inv_nonneg.mpr (sq_nonneg _)
      have : 0 < E y := Real.exp_pos _
      positivity
  have hI2 : 0 ≤ ∫ y, W y * E y * ‖gradient v y‖ ^ 2 :=
    integral_nonneg fun y => by
      have : 0 ≤ W y := inv_nonneg.mpr (sq_nonneg _)
      have : 0 < E y := Real.exp_pos _
      positivity
  have hK0 : 0 ≤ K ^ 2 := sq_nonneg K
  have hτ0 : 1 ≤ τ := by linarith
  have hτ3 : τ ≤ τ ^ 3 := by
    have h1 : 0 ≤ τ * (τ - 1) * (τ + 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have hK1 : 0 ≤ (τ ^ 3 - 120 * K ^ 2) * ∫ y, W y * E y * v y ^ 2 :=
    mul_nonneg (by linarith) hI1
  have hK2 : 0 ≤ (τ - 120 * K ^ 2) * ∫ y, W y * E y * ‖gradient v y‖ ^ 2 :=
    mul_nonneg (by linarith) hI2
  nlinarith [key, h3, hK1, hK2]

/-! ### Cutoffs, slabs and shells -/

/-- The cutoff `v_M = cutM l M · U`: equal to `1` on `{y_d ≥ l + 2, ‖y‖ ≤ M}` and to `0` on
`{y_d ≤ l + 1}` and on `{‖y‖² ≥ 2 M²}`. -/
noncomputable def cutM (l M : ℝ) (y : Space n) : ℝ :=
  (1 - Real.smoothTransition (‖y‖ ^ 2 / M ^ 2 - 1)) * Real.smoothTransition (vcoord y - (l + 1))

/-- The truncated slab `{l + 1 ≤ y_d ≤ l + 2, ‖y‖ ≤ 2M}`. -/
def slab (n : ℕ) (l M : ℝ) : Set (Space n) :=
  {y | l + 1 ≤ vcoord y ∧ vcoord y ≤ l + 2 ∧ ‖y‖ ≤ 2 * M}

/-- The shell `{y_d ≥ l + 1, M ≤ ‖y‖ ≤ 2M}`. -/
def shell (n : ℕ) (l M : ℝ) : Set (Space n) := {y | l + 1 ≤ vcoord y ∧ M ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * M}

/-! ### Properties of the weight and of the cutoff -/

theorem gw_le_self {C₀ s : ℝ} (hC₀ : 0 ≤ C₀) (hs : 1 ≤ s) : gw C₀ s ≤ s := by
  unfold gw
  have : 0 ≤ Real.log s := Real.log_nonneg hs
  nlinarith

theorem gw_mono {C₀ a b : ℝ} (hC₀ : 0 < C₀) (ha : C₀ ≤ a) (hab : a ≤ b) : gw C₀ a ≤ gw C₀ b := by
  unfold gw
  have ha0 : 0 < a := lt_of_lt_of_le hC₀ ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hlog : Real.log b - Real.log a ≤ (b - a) / a := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [sub_div, div_self ha0.ne'] at *
    linarith
  have h1 : C₀ * ((b - a) / a) ≤ b - a := by
    rw [mul_div_assoc', div_le_iff₀ ha0]
    nlinarith
  nlinarith

theorem contDiff_vcoord_any {k : WithTop ℕ∞} : ContDiff ℝ k (vcoord : Space n → ℝ) := by
  rw [F1.vcoord_eq_proj]
  exact (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).contDiff

theorem contDiff_cutM (l M : ℝ) : ContDiff ℝ 2 (cutM (n := n) l M) := by
  have h1 : ContDiff ℝ 2 (fun y : Space n => Real.smoothTransition (‖y‖ ^ 2 / M ^ 2 - 1)) :=
    (Real.smoothTransition.contDiff (n := 2)).comp
      (((contDiff_norm_sq ℝ).div_const _).sub contDiff_const)
  have h2 : ContDiff ℝ 2 (fun y : Space n => Real.smoothTransition (vcoord y - (l + 1))) :=
    (Real.smoothTransition.contDiff (n := 2)).comp (contDiff_vcoord_any.sub contDiff_const)
  exact (contDiff_const.sub h1).mul h2

theorem cutM_eq_one {l M : ℝ} (hM : 0 < M) {y : Space n} (hy : l + 2 ≤ vcoord y)
    (hyM : ‖y‖ ≤ M) : cutM l M y = 1 := by
  unfold cutM
  have h1 : ‖y‖ ^ 2 / M ^ 2 - 1 ≤ 0 := by
    have : ‖y‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyM 2
    rw [sub_nonpos, div_le_one (by positivity)]
    exact this
  rw [Real.smoothTransition.zero_of_nonpos h1, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem support_cutM_subset {l M : ℝ} (hM : 0 < M) :
    Function.support (cutM (n := n) l M) ⊆ {y | l + 1 ≤ vcoord y ∧ ‖y‖ ^ 2 ≤ 2 * M ^ 2} := by
  intro y hy
  rw [Function.mem_support] at hy
  unfold cutM at hy
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    apply hy
    rw [Real.smoothTransition.zero_of_nonpos (x := vcoord y - (l + 1)) (by linarith), mul_zero]
  · by_contra h
    push Not at h
    apply hy
    have h1 : 1 ≤ ‖y‖ ^ 2 / M ^ 2 - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      linarith
    rw [Real.smoothTransition.one_of_one_le h1, sub_self, zero_mul]

theorem tsupport_cutM_subset {l M : ℝ} (hM : 0 < M) :
    tsupport (cutM (n := n) l M) ⊆ {y | l + 1 ≤ vcoord y ∧ ‖y‖ ^ 2 ≤ 2 * M ^ 2} := by
  apply closure_minimal (support_cutM_subset hM)
  exact (isClosed_le continuous_const F1.continuous_vcoord).inter
    (isClosed_le (continuous_norm.pow 2) continuous_const)

theorem isCompact_cutM_set (l M : ℝ) :
    IsCompact {y : Space n | l + 1 ≤ vcoord y ∧ ‖y‖ ^ 2 ≤ 2 * M ^ 2} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_const F1.continuous_vcoord).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : Space n)) (r := Real.sqrt (2 * M ^ 2))).subset ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Real.le_sqrt_of_sq_le hy.2

/-- `v_M = cutM l M · U` is a `C²` function with compact support in `H n l`. -/
theorem cutM_mul_props {l M : ℝ} (hl : 0 ≤ l) (hM : 0 < M) {U : Space n → ℝ}
    (hU : ∀ y ∈ H n l, ContDiffAt ℝ 2 U y) :
    ContDiff ℝ 2 (fun z => cutM l M z * U z) ∧ HasCompactSupport (fun z => cutM l M z * U z) ∧
      tsupport (fun z => cutM l M z * U z) ⊆ H n l := by
  have hts : tsupport (fun z => cutM l M z * U z) ⊆ tsupport (cutM (n := n) l M) :=
    tsupport_mul_subset_left
  have hF : {y : Space n | l + 1 ≤ vcoord y ∧ ‖y‖ ^ 2 ≤ 2 * M ^ 2} ⊆ H n l :=
    fun y hy => show l < vcoord y by linarith [hy.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ H n l
    · exact (contDiff_cutM l M).contDiffAt.mul (hU y hy)
    · have hy' : y ∉ tsupport (cutM (n := n) l M) := fun h => hy (hF (tsupport_cutM_subset hM h))
      have hev : (fun z => cutM l M z * U z) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_eq_zero_of_not_mem_tsupport hy'] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (isCompact_cutM_set l M).of_isClosed_subset (isClosed_tsupport _)
      (hts.trans (tsupport_cutM_subset hM))
  · exact hts.trans ((tsupport_cutM_subset hM).trans hF)

/-- Integrability of the terms of the Carleman estimate for `v` with compact support in `H n l`. -/
theorem carleman_integrable {l : ℝ} (hl0 : 0 ≤ l) {K C₀ τ : ℝ}
    {A : Space n → Space n →L[ℝ] Space n} {β : Space n → Space n} {γ : Space n → ℝ}
    (hc : CarlCoeffs A β γ K l) {v : Space n → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hvs : tsupport v ⊆ H n l) :
    Integrable (fun y => (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y)) * v y ^ 2) ∧
    Integrable (fun y => Real.exp (2 * τ * gw C₀ (vcoord y)) * ellOp A β γ v y ^ 2) := by
  have hEc : ContinuousOn (fun y : Space n => Real.exp (2 * τ * gw C₀ (vcoord y))) (H n l) :=
    continuousOn_weight C₀ τ hl0
  have hWc : ContinuousOn (fun y : Space n => (vcoord y ^ 2)⁻¹) (H n l) := continuousOn_inv_sq hl0
  have hgc : Continuous (gradient v) := continuous_gradient_of_contDiff hv
  have hPc : ContinuousOn (fun y => divergence (fun z => A z (gradient v z)) y) (H n l) := by
    intro y hy
    have hF : ContDiffAt ℝ 1 (fun z => A z (gradient v z)) y :=
      ((hc.contDiffAt y hy).of_le (by norm_num)).clm_apply
        (F2.contDiffAt_gradient hv.contDiffAt (m := 1) (by norm_num))
    exact (continuousAt_divergence hF).continuousWithinAt
  have hLc : ContinuousOn (fun y => ellOp A β γ v y) (H n l) := by
    have h1 : ContinuousOn (fun y => ⟪β y, gradient v y⟫_ℝ) (H n l) :=
      hc.cont_β.inner hgc.continuousOn
    have h2 : ContinuousOn (fun y => γ y * v y) (H n l) := hc.cont_γ.mul hv.continuous.continuousOn
    exact (hPc.add h1).add h2
  refine ⟨?_, ?_⟩
  · exact integrable_of_tsupport (isOpen_H l) hvc hvs
      ((hWc.mul hEc).mul (hv.continuous.continuousOn.pow 2))
      (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])
  · exact integrable_of_tsupport (isOpen_H l) hvc hvs (hEc.mul (hLc.pow 2))
      (fun y hy => by simp [ellOp_eq_zero_of_not_mem_tsupport A β γ hy])

theorem slab_subset_H {l M : ℝ} : slab n l M ⊆ H n l :=
  fun y hy => show l < vcoord y by linarith [hy.1]

theorem shell_subset_H {l M : ℝ} : shell n l M ⊆ H n l :=
  fun y hy => show l < vcoord y by linarith [hy.1]

theorem isClosed_slab (l M : ℝ) : IsClosed (slab n l M) :=
  show IsClosed ({y : Space n | l + 1 ≤ vcoord y} ∩ ({y | vcoord y ≤ l + 2} ∩ {y | ‖y‖ ≤ 2 * M}))
  from (isClosed_le continuous_const F1.continuous_vcoord).inter
    ((isClosed_le F1.continuous_vcoord continuous_const).inter
      (isClosed_le continuous_norm continuous_const))

theorem isClosed_shell (l M : ℝ) : IsClosed (shell n l M) :=
  show IsClosed ({y : Space n | l + 1 ≤ vcoord y} ∩ ({y | M ≤ ‖y‖} ∩ {y | ‖y‖ ≤ 2 * M}))
  from (isClosed_le continuous_const F1.continuous_vcoord).inter
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))

theorem isCompact_slab (l M : ℝ) : IsCompact (slab n l M) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_slab l M)
    ((Metric.isBounded_closedBall (x := (0 : Space n)) (r := 2 * M)).subset fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hy.2.2)

theorem isCompact_shell (l M : ℝ) : IsCompact (shell n l M) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_shell l M)
    ((Metric.isBounded_closedBall (x := (0 : Space n)) (r := 2 * M)).subset fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hy.2.2)

theorem continuousOn_energy {l : ℝ} {U : Space n → ℝ} (hU : ∀ y ∈ H n l, ContDiffAt ℝ 2 U y) :
    ContinuousOn (fun y => U y ^ 2 + ‖gradient U y‖ ^ 2) (H n l) := by
  intro y hy
  have h1 : ContinuousAt U y := (hU y hy).continuousAt
  have h2 : ContinuousAt (gradient U) y :=
    (F2.contDiffAt_gradient (hU y hy) (m := 0) (by norm_num)).continuousAt
  exact ((h1.pow 2).add (h2.norm.pow 2)).continuousWithinAt

/-! ### The commutator with the cutoff -/

/-- Locality of `ellOp`. -/
theorem ellOp_congr (A : Space n → Space n →L[ℝ] Space n) (β : Space n → Space n)
    (γ : Space n → ℝ) {u w : Space n → ℝ} {y : Space n} (h : u =ᶠ[𝓝 y] w) :
    ellOp A β γ u y = ellOp A β γ w y := by
  have hg : ∀ᶠ z in 𝓝 y, gradient u z = gradient w z := by
    filter_upwards [h.eventuallyEq_nhds] with z hz using hz.gradient_eq
  have hF : (fun z => A z (gradient u z)) =ᶠ[𝓝 y] fun z => A z (gradient w z) := by
    filter_upwards [hg] with z hz
    rw [hz]
  simp only [ellOp, F2.divergence_congr hF, hg.self_of_nhds, h.self_of_nhds]

/-- The product rule `L(φ U) = φ L U + 2⟨A∇φ, ∇U⟩ + U (div(A∇φ) + ⟨β, ∇φ⟩)` for symmetric `A`. -/
theorem ellOp_mul (A : Space n → Space n →L[ℝ] Space n) (β : Space n → Space n)
    (γ : Space n → ℝ) {φ U : Space n → ℝ} {y : Space n} (hA : ContDiffAt ℝ 1 A y)
    (hsymm : ∀ ξ η, ⟪A y ξ, η⟫_ℝ = ⟪ξ, A y η⟫_ℝ) (hφ : ContDiffAt ℝ 2 φ y)
    (hU : ContDiffAt ℝ 2 U y) :
    ellOp A β γ (fun z => φ z * U z) y = φ y * ellOp A β γ U y
      + 2 * ⟪A y (gradient φ y), gradient U y⟫_ℝ
      + U y * (divergence (fun z => A z (gradient φ z)) y + ⟪β y, gradient φ y⟫_ℝ) := by
  have hAd : DifferentiableAt ℝ A y := hA.differentiableAt one_ne_zero
  have hφd : DifferentiableAt ℝ φ y := hφ.differentiableAt (by simp)
  have hUd : DifferentiableAt ℝ U y := hU.differentiableAt (by simp)
  have hgφ : DifferentiableAt ℝ (gradient φ) y := F2.differentiableAt_gradient hφ
  have hgU : DifferentiableAt ℝ (gradient U) y := F2.differentiableAt_gradient hU
  have hgrad : ∀ᶠ z in 𝓝 y, gradient (fun z => φ z * U z) z
      = φ z • gradient U z + U z • gradient φ z := by
    filter_upwards [hφ.eventually (by simp), hU.eventually (by simp)] with z hφz hUz
    have hφz' : DifferentiableAt ℝ φ z := hφz.differentiableAt (by simp)
    have hUz' : DifferentiableAt ℝ U z := hUz.differentiableAt (by simp)
    refine ext_inner_right ℝ fun ξ => ?_
    have hd : HasFDerivAt (fun z => φ z * U z) (φ z • fderiv ℝ U z + U z • fderiv ℝ φ z) z :=
      hφz'.hasFDerivAt.mul hUz'.hasFDerivAt
    rw [inner_gradient_left, hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, inner_add_left, real_inner_smul_left,
      inner_gradient_left]
  have hF : (fun z => A z (gradient (fun z => φ z * U z) z)) =ᶠ[𝓝 y]
      fun z => φ z • A z (gradient U z) + U z • A z (gradient φ z) := by
    filter_upwards [hgrad] with z hz
    rw [hz, map_add, map_smul, map_smul]
  have h1 : DifferentiableAt ℝ (fun z => A z (gradient U z)) y := hAd.clm_apply hgU
  have h2 : DifferentiableAt ℝ (fun z => A z (gradient φ z)) y := hAd.clm_apply hgφ
  have hdiv : divergence (fun z => A z (gradient (fun z => φ z * U z) z)) y
      = φ y * divergence (fun z => A z (gradient U z)) y + fderiv ℝ φ y (A y (gradient U y))
        + (U y * divergence (fun z => A z (gradient φ z)) y
          + fderiv ℝ U y (A y (gradient φ y))) := by
    have h1' : DifferentiableAt ℝ (fun z => φ z • A z (gradient U z)) y := hφd.smul h1
    have h2' : DifferentiableAt ℝ (fun z => U z • A z (gradient φ z)) y := hUd.smul h2
    rw [F2.divergence_congr hF, F2.divergence_add h1' h2',
      F2.divergence_smul hφd h1, F2.divergence_smul hUd h2]
  have e1 : fderiv ℝ φ y (A y (gradient U y)) = ⟪A y (gradient φ y), gradient U y⟫_ℝ := by
    rw [← inner_gradient_left, hsymm]
  have e2 : fderiv ℝ U y (A y (gradient φ y)) = ⟪A y (gradient φ y), gradient U y⟫_ℝ := by
    rw [← inner_gradient_left, real_inner_comm]
  have hgy := hgrad.self_of_nhds
  simp only [ellOp]
  rw [hdiv, e1, e2, hgy, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  ring

theorem norm_fderiv_clm_apply_le {A : Space n → Space n →L[ℝ] Space n} {g : Space n → Space n}
    {y : Space n} (hA : DifferentiableAt ℝ A y) (hg : DifferentiableAt ℝ g y) :
    ‖fderiv ℝ (fun z => A z (g z)) y‖ ≤ ‖fderiv ℝ A y‖ * ‖g y‖ + ‖A y‖ * ‖fderiv ℝ g y‖ := by
  rw [fderiv_clm_apply hA hg]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  calc ‖A y (fderiv ℝ g y ξ) + fderiv ℝ A y ξ (g y)‖
      ≤ ‖A y (fderiv ℝ g y ξ)‖ + ‖fderiv ℝ A y ξ (g y)‖ := norm_add_le _ _
    _ ≤ ‖A y‖ * (‖fderiv ℝ g y‖ * ‖ξ‖) + ‖fderiv ℝ A y ξ‖ * ‖g y‖ := by
        gcongr
        · exact (A y).le_of_opNorm_le (le_refl _) _ |>.trans (by
            gcongr; exact (fderiv ℝ g y).le_opNorm ξ)
        · exact (fderiv ℝ A y ξ).le_opNorm _
    _ ≤ ‖A y‖ * (‖fderiv ℝ g y‖ * ‖ξ‖) + ‖fderiv ℝ A y‖ * ‖ξ‖ * ‖g y‖ := by
        gcongr
        exact (fderiv ℝ A y).le_opNorm ξ
    _ = (‖fderiv ℝ A y‖ * ‖g y‖ + ‖A y‖ * ‖fderiv ℝ g y‖) * ‖ξ‖ := by ring

theorem abs_divergence_le (F : Space n → Space n) (y : Space n) :
    |divergence F y| ≤ ‖F2.traceCLM (n := n)‖ * ‖fderiv ℝ F y‖ := by
  rw [F2.divergence_eq_traceCLM, ← Real.norm_eq_abs]
  exact (F2.traceCLM (n := n)).le_opNorm _

theorem st_deriv_bound (i : ℕ) (hi : i ≠ 0) :
    ∃ C : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i Real.smoothTransition t‖ ≤ C := by
  have hcont : Continuous (iteratedFDeriv ℝ i Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hsupp : HasCompactSupport (iteratedFDeriv ℝ i Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun t ht => ?_
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      rw [(h.iteratedFDeriv ℝ i).self_of_nhds, iteratedFDeriv_const_of_ne hi]
      rfl
    · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [(h.iteratedFDeriv ℝ i).self_of_nhds, iteratedFDeriv_const_of_ne hi]
      rfl
  exact hcont.bounded_above_of_compact_support hsupp

theorem norm_iteratedFDeriv_comp_clm_le {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f : E' → ℝ} (hf : ContDiff ℝ ∞ f) (L : Space n →L[ℝ] E') (hL : ‖L‖ ≤ 1) (i : ℕ) {C : ℝ}
    (hC : ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ C) (y : Space n) :
    ‖iteratedFDeriv ℝ i (f ∘ L) y‖ ≤ C := by
  rw [L.iteratedFDeriv_comp_right hf y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _j : Fin i, ‖L‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hL
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (L y))
  calc ‖iteratedFDeriv ℝ i f (L y)‖ * ∏ _j : Fin i, ‖L‖ ≤ C * 1 :=
        mul_le_mul (hC _) hp (Finset.prod_nonneg fun _ _ => norm_nonneg _) hC0
    _ = C := mul_one C

theorem norm_iteratedFDeriv_mul_le_of_bound {f g : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {C : ℝ} (hfC : ∀ i ≤ 2, ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ C)
    (hgC : ∀ i ≤ 2, ∀ z, ‖iteratedFDeriv ℝ i g z‖ ≤ C) {k : ℕ} (hk : k ≤ 2) (y : Space n) :
    ‖iteratedFDeriv ℝ k (fun z => f z * g z) y‖ ≤ 2 ^ k * C ^ 2 := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hfC 0 (by norm_num) y)
  refine (norm_iteratedFDeriv_mul_le hf hg y (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖
          * ‖iteratedFDeriv ℝ (k - i) g y‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C * C := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 := hfC i (by omega) y
        have h2 := hgC (k - i) (by omega) y
        have hch : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
        calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ * ‖iteratedFDeriv ℝ (k - i) g y‖
            ≤ (k.choose i : ℝ) * C * C := by gcongr
          _ = _ := rfl
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * C ^ 2 := by
        rw [Finset.sum_mul]; congr 1; funext i; ring
    _ = 2 ^ k * C ^ 2 := by
        congr 1
        exact_mod_cast Nat.sum_range_choose k

/-- Uniform bounds for the cutoff `cutM l M`, `M ≥ 1`. -/
theorem cutM_deriv_bounds (l : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℝ, 1 ≤ M → ∀ y : Space n,
    ‖gradient (cutM l M) y‖ ≤ B ∧ ‖fderiv ℝ (gradient (cutM l M)) y‖ ≤ B := by
  -- the two factors
  set θ : Space n → ℝ := fun z => 1 - Real.smoothTransition (‖z‖ ^ 2 - 1) with hθ
  have hθs : ContDiff ℝ ∞ θ :=
    contDiff_const.sub ((Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_norm_sq ℝ).sub contDiff_const))
  have hθcs : HasCompactSupport θ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space n) 2) fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    simp only [hθ]
    rw [Real.smoothTransition.one_of_one_le (by nlinarith), sub_self]
  have hθb : ∀ i : ℕ, ∃ C : ℝ, ∀ z, ‖iteratedFDeriv ℝ i θ z‖ ≤ C := fun i =>
    (hθs.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hθcs.iteratedFDeriv i)
  set ψ : ℝ → ℝ := fun t => Real.smoothTransition (t - (l + 1)) with hψ
  have hψs : ContDiff ℝ ∞ ψ :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)
  have hψb : ∀ i : ℕ, ∃ C : ℝ, ∀ t, ‖iteratedFDeriv ℝ i ψ t‖ ≤ C := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · refine ⟨1, fun t => ?_⟩
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · obtain ⟨C, hC⟩ := st_deriv_bound i hi
      exact ⟨C, fun t => by
        rw [hψ, iteratedFDeriv_comp_sub (f := Real.smoothTransition) i (l + 1) t]
        exact hC _⟩
  choose Cθ hCθ using hθb
  choose Cψ hCψ using hψb
  set C : ℝ := max (max (Cθ 0) (max (Cθ 1) (Cθ 2))) (max (Cψ 0) (max (Cψ 1) (Cψ 2))) with hC
  have hCθ' : ∀ i ≤ 2, ∀ z, ‖iteratedFDeriv ℝ i θ z‖ ≤ C := by
    intro i hi z
    interval_cases i
    · exact (hCθ 0 z).trans (le_max_left _ _ |>.trans (le_max_left _ _))
    · exact (hCθ 1 z).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    · exact (hCθ 2 z).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have hCψ' : ∀ i ≤ 2, ∀ t, ‖iteratedFDeriv ℝ i ψ t‖ ≤ C := by
    intro i hi t
    interval_cases i
    · exact (hCψ 0 t).trans (le_max_left _ _ |>.trans (le_max_right _ _))
    · exact (hCψ 1 t).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · exact (hCψ 2 t).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCψ' 0 (by norm_num) 0)
  refine ⟨4 * C ^ 2, by positivity, fun M hM y => ?_⟩
  have hM0 : 0 < M := by linarith
  set L : Space n →L[ℝ] Space n := M⁻¹ • ContinuousLinearMap.id ℝ (Space n) with hL
  have hLn : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM0)]
    calc M⁻¹ * ‖ContinuousLinearMap.id ℝ (Space n)‖ ≤ M⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_pos.mpr hM0).le
      _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ hM
  set P : Space n →L[ℝ] ℝ := (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ) with hP
  have hPn : ‖P‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul, hP]
    exact PiLp.norm_apply_le x (Fin.last n)
  have hform : cutM (n := n) l M = fun z => (θ ∘ L) z * (ψ ∘ P) z := by
    funext z
    have hv : vcoord z = P z := by rw [hP]; exact congrFun F1.vcoord_eq_proj z
    have hn : ‖L z‖ ^ 2 = ‖z‖ ^ 2 / M ^ 2 := by
      rw [hL, smul_apply, ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hM0)]
      field_simp
    simp only [cutM, Function.comp_apply, hθ, hψ, hn, hv]
  have hf1 : ContDiff ℝ ∞ (θ ∘ L) := hθs.comp L.contDiff
  have hf2 : ContDiff ℝ ∞ (ψ ∘ P) := hψs.comp P.contDiff
  have hb1 : ∀ i ≤ 2, ∀ z, ‖iteratedFDeriv ℝ i (θ ∘ L) z‖ ≤ C := fun i hi z =>
    norm_iteratedFDeriv_comp_clm_le hθs L hLn i (hCθ' i hi) z
  have hb2 : ∀ i ≤ 2, ∀ z, ‖iteratedFDeriv ℝ i (ψ ∘ P) z‖ ≤ C := fun i hi z =>
    norm_iteratedFDeriv_comp_clm_le hψs P hPn i (hCψ' i hi) z
  have hD1 := norm_iteratedFDeriv_mul_le_of_bound hf1 hf2 hb1 hb2 (k := 1) (by norm_num) y
  have hD2 := norm_iteratedFDeriv_mul_le_of_bound hf1 hf2 hb1 hb2 (k := 2) (by norm_num) y
  rw [← hform] at hD1 hD2
  have hcd : ContDiff ℝ 2 (cutM (n := n) l M) := contDiff_cutM l M
  refine ⟨?_, ?_⟩
  · show ‖(InnerProductSpace.toDual ℝ (Space n)).symm (fderiv ℝ (cutM l M) y)‖ ≤ 4 * C ^ 2
    rw [LinearIsometryEquiv.norm_map, ← norm_iteratedFDeriv_one]
    calc _ ≤ 2 ^ 1 * C ^ 2 := hD1
      _ ≤ 4 * C ^ 2 := by nlinarith [sq_nonneg C]
  · have hdd : DifferentiableAt ℝ (fderiv ℝ (cutM (n := n) l M)) y :=
      (hcd.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [(F2.hasFDerivAt_gradient hdd).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
    rw [ContinuousLinearMap.comp_apply]
    have hiso : ‖(F2.toDualSymmCLE (n := n) : StrongDual ℝ (Space n) →L[ℝ] Space n)
        (fderiv ℝ (fderiv ℝ (cutM (n := n) l M)) y ξ)‖
        = ‖fderiv ℝ (fderiv ℝ (cutM (n := n) l M)) y ξ‖ := by
      simp [F2.toDualSymmCLE]
    rw [hiso]
    have h2 : ‖fderiv ℝ (fderiv ℝ (cutM (n := n) l M)) y‖ ≤ 4 * C ^ 2 := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      calc _ ≤ 2 ^ 2 * C ^ 2 := hD2
        _ = 4 * C ^ 2 := by norm_num
    exact ((fderiv ℝ (fderiv ℝ (cutM (n := n) l M)) y).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- The commutator `L̃(cutM · U) - cutM · L̃U` is supported in the slab and the shell and is
bounded by `|U| + |∇U|`, uniformly in `M ≥ 1`. -/
theorem cutoff_bound {K l : ℝ} (hK : 0 ≤ K) (hl : 1 ≤ l) {A : Space n → Space n →L[ℝ] Space n}
    {β : Space n → Space n} {γ : Space n → ℝ} (hc : CarlCoeffs A β γ K l) {U : Space n → ℝ}
    (hU : ∀ y ∈ H n l, ContDiffAt ℝ 2 U y) (hLU : ∀ y ∈ H n l, ellOp A β γ U y = 0) :
    ∃ Ccut : ℝ, 0 ≤ Ccut ∧ ∀ M : ℝ, 1 ≤ M → ∀ y : Space n,
      ellOp A β γ (fun z => cutM l M z * U z) y ^ 2 ≤
        Ccut * ((slab n l M).indicator (fun z => U z ^ 2 + ‖gradient U z‖ ^ 2) y
          + (shell n l M).indicator (fun z => U z ^ 2 + ‖gradient U z‖ ^ 2) y) := by
  obtain ⟨B, hB0, hB⟩ := cutM_deriv_bounds (n := n) l
  set T : ℝ := ‖F2.traceCLM (n := n)‖ with hT
  have hT0 : 0 ≤ T := norm_nonneg (F2.traceCLM (n := n))
  set C₁ : ℝ := 2 * (1 + K) * B + T * (K * B + (1 + K) * B) + K * B with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨2 * C₁ ^ 2, by positivity, ?_⟩
  intro M hM y
  have hM0 : 0 < M := by linarith
  set f : Space n → ℝ := fun z => U z ^ 2 + ‖gradient U z‖ ^ 2 with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => by positivity
  have hind0 : ∀ (S : Set (Space n)), 0 ≤ S.indicator f y :=
    fun S => Set.indicator_nonneg (fun z _ => hf0 z) y
  have hRHS0 : 0 ≤ 2 * C₁ ^ 2 * ((slab n l M).indicator f y + (shell n l M).indicator f y) :=
    mul_nonneg (by positivity) (add_nonneg (hind0 _) (hind0 _))
  by_cases hyt : y ∈ tsupport (fun z => cutM l M z * U z)
  swap
  · rw [ellOp_eq_zero_of_not_mem_tsupport A β γ hyt]
    simpa using hRHS0
  have hyF : l + 1 ≤ vcoord y ∧ ‖y‖ ^ 2 ≤ 2 * M ^ 2 :=
    tsupport_cutM_subset hM0 (tsupport_mul_subset_left hyt)
  have hyH : y ∈ H n l := show l < vcoord y by linarith [hyF.1]
  have hs1 : 1 ≤ vcoord y := by linarith [hyF.1]
  have hs0 : 0 < vcoord y := by linarith
  by_cases hgood : l + 2 < vcoord y ∧ ‖y‖ < M
  · -- `cutM = 1` near `y`
    have hev : (fun z => cutM l M z * U z) =ᶠ[𝓝 y] U := by
      have hopen : IsOpen {z : Space n | l + 2 < vcoord z ∧ ‖z‖ < M} :=
        (isOpen_lt continuous_const F1.continuous_vcoord).inter
          (isOpen_lt continuous_norm continuous_const)
      filter_upwards [hopen.mem_nhds hgood] with z hz
      rw [cutM_eq_one hM0 hz.1.le hz.2.le, one_mul]
    rw [ellOp_congr A β γ hev, hLU y hyH]
    simpa using hRHS0
  -- `y` lies in the slab or in the shell
  have hy2M : ‖y‖ ≤ 2 * M := by
    have h1 : ‖y‖ ^ 2 ≤ (2 * M) ^ 2 := by nlinarith [hyF.2]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) (by norm_num)).mp h1
  have hmem : f y ≤ (slab n l M).indicator f y + (shell n l M).indicator f y := by
    by_cases h2 : vcoord y ≤ l + 2
    · rw [Set.indicator_of_mem (show y ∈ slab n l M from ⟨hyF.1, h2, hy2M⟩)]
      linarith [hind0 (shell n l M)]
    · have hMy : M ≤ ‖y‖ := by
        by_contra h3
        push Not at h2 h3
        exact hgood ⟨h2, h3⟩
      rw [Set.indicator_of_mem (show y ∈ shell n l M from ⟨hyF.1, hMy, hy2M⟩)]
      linarith [hind0 (slab n l M)]
  -- the product rule and the bounds
  have hAy : ContDiffAt ℝ 2 A y := hc.contDiffAt y hyH
  have hφ : ContDiffAt ℝ 2 (cutM l M) y := (contDiff_cutM l M).contDiffAt
  have hprod := ellOp_mul A β γ (hAy.of_le (by norm_num)) (hc.symm y hyH) hφ (hU y hyH)
  rw [hLU y hyH, mul_zero, zero_add] at hprod
  obtain ⟨hgφ, hDgφ⟩ := hB M hM y
  have hnA : ‖A y‖ ≤ 1 + K := by
    have h1 := hc.bound_A y hyH
    have h2 : K / vcoord y ≤ K := div_le_self hK hs1
    calc ‖A y‖ = ‖(A y - ContinuousLinearMap.id ℝ (Space n)) + ContinuousLinearMap.id ℝ (Space n)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖A y - ContinuousLinearMap.id ℝ (Space n)‖ + ‖ContinuousLinearMap.id ℝ (Space n)‖ :=
          norm_add_le _ _
      _ ≤ K + 1 := add_le_add (h1.trans h2) ContinuousLinearMap.norm_id_le
      _ = 1 + K := by ring
  have hnDA : ‖fderiv ℝ A y‖ ≤ K := by
    have h1 := hc.bound_dA y hyH
    have h2 : K / vcoord y ^ 2 ≤ K := div_le_self hK (by nlinarith)
    linarith
  have hnβ : ‖β y‖ ≤ K := (hc.bound_β y hyH).trans (div_le_self hK hs1)
  have hdivb : |divergence (fun z => A z (gradient (cutM l M) z)) y| ≤ T * (K * B + (1 + K) * B) := by
    refine (abs_divergence_le _ y).trans ?_
    apply mul_le_mul_of_nonneg_left _ hT0
    refine (norm_fderiv_clm_apply_le (hAy.differentiableAt (by simp))
      (F2.differentiableAt_gradient hφ)).trans ?_
    gcongr
  have hbound : |ellOp A β γ (fun z => cutM l M z * U z) y| ≤ C₁ * (|U y| + ‖gradient U y‖) := by
    rw [hprod]
    have e1 : |2 * ⟪A y (gradient (cutM l M) y), gradient U y⟫_ℝ| ≤ 2 * (1 + K) * B * ‖gradient U y‖ := by
      rw [abs_mul, abs_two]
      have h2 : ‖A y (gradient (cutM l M) y)‖ ≤ (1 + K) * B :=
        ((A y).le_opNorm _).trans (mul_le_mul hnA hgφ (norm_nonneg _) (by linarith))
      calc 2 * |⟪A y (gradient (cutM l M) y), gradient U y⟫_ℝ|
          ≤ 2 * (‖A y (gradient (cutM l M) y)‖ * ‖gradient U y‖) := by
            gcongr; exact abs_real_inner_le_norm _ _
        _ ≤ 2 * ((1 + K) * B * ‖gradient U y‖) := by gcongr
        _ = 2 * (1 + K) * B * ‖gradient U y‖ := by ring
    have e2 : |U y * (divergence (fun z => A z (gradient (cutM l M) z)) y
        + ⟪β y, gradient (cutM l M) y⟫_ℝ)| ≤ |U y| * (T * (K * B + (1 + K) * B) + K * B) := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine (abs_add_le _ _).trans (add_le_add hdivb ?_)
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hnβ hgφ (norm_nonneg _) hK)
    calc _ ≤ |2 * ⟪A y (gradient (cutM l M) y), gradient U y⟫_ℝ|
          + |U y * (divergence (fun z => A z (gradient (cutM l M) z)) y
            + ⟪β y, gradient (cutM l M) y⟫_ℝ)| := abs_add_le _ _
      _ ≤ 2 * (1 + K) * B * ‖gradient U y‖ + |U y| * (T * (K * B + (1 + K) * B) + K * B) :=
          add_le_add e1 e2
      _ ≤ C₁ * (|U y| + ‖gradient U y‖) := by
          have hu := abs_nonneg (U y)
          have hg := norm_nonneg (gradient U y)
          have hb1 : 0 ≤ 2 * (1 + K) * B := by positivity
          have hb2 : 0 ≤ T * (K * B + (1 + K) * B) + K * B := by positivity
          calc 2 * (1 + K) * B * ‖gradient U y‖ + |U y| * (T * (K * B + (1 + K) * B) + K * B)
              ≤ 2 * (1 + K) * B * ‖gradient U y‖ + |U y| * (T * (K * B + (1 + K) * B) + K * B)
                + (2 * (1 + K) * B * |U y| + (T * (K * B + (1 + K) * B) + K * B)
                  * ‖gradient U y‖) :=
                le_add_of_nonneg_right (add_nonneg (mul_nonneg hb1 hu) (mul_nonneg hb2 hg))
            _ = C₁ * (|U y| + ‖gradient U y‖) := by rw [hC₁]; ring
  have hsq : ellOp A β γ (fun z => cutM l M z * U z) y ^ 2 ≤ 2 * C₁ ^ 2 * f y := by
    have h1 : ellOp A β γ (fun z => cutM l M z * U z) y ^ 2 ≤ (C₁ * (|U y| + ‖gradient U y‖)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
    have h2 : (C₁ * (|U y| + ‖gradient U y‖)) ^ 2 ≤ 2 * C₁ ^ 2 * f y := by
      have h3 : (|U y| + ‖gradient U y‖) ^ 2 ≤ 2 * (U y ^ 2 + ‖gradient U y‖ ^ 2) := by
        rw [← sq_abs (U y)]
        nlinarith [sq_nonneg (|U y| - ‖gradient U y‖)]
      calc (C₁ * (|U y| + ‖gradient U y‖)) ^ 2 = C₁ ^ 2 * (|U y| + ‖gradient U y‖) ^ 2 := by ring
        _ ≤ C₁ ^ 2 * (2 * (U y ^ 2 + ‖gradient U y‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = 2 * C₁ ^ 2 * f y := by simp only [hf]; ring
    linarith
  calc _ ≤ 2 * C₁ ^ 2 * f y := hsq
    _ ≤ _ := mul_le_mul_of_nonneg_left hmem (by positivity)

/-- Integrability of `U² + |∇U|²` on `{y_d ≥ l + 1}`, from the decay on shells. -/
theorem integrableOn_E {l : ℝ} (hl : 0 ≤ l) {U : Space n → ℝ}
    (hU : ∀ y ∈ H n l, ContDiffAt ℝ 2 U y)
    (hshell : ∀ N : ℝ, ∃ CN M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
        ∫ y in shell n l M, (U y ^ 2 + ‖gradient U y‖ ^ 2) ≤ CN * Real.exp (-N * M)) :
    IntegrableOn (fun y => U y ^ 2 + ‖gradient U y‖ ^ 2) {y | l + 1 ≤ vcoord y} := by
  set f : Space n → ℝ := fun y => U y ^ 2 + ‖gradient U y‖ ^ 2 with hf
  have hfc : ContinuousOn f (H n l) := continuousOn_energy hU
  have hf0 : ∀ y, 0 ≤ f y := fun y => by positivity
  obtain ⟨C₁, M₀, hC₁⟩ := hshell 1
  set M₁ : ℝ := max M₀ 1 with hM₁
  have hM₁1 : 1 ≤ M₁ := le_max_right _ _
  -- the bounded part
  set A : Set (Space n) := {y | l + 1 ≤ vcoord y ∧ ‖y‖ ≤ M₁} with hA
  have hAH : A ⊆ H n l := fun y hy => show l < vcoord y by linarith [hy.1]
  have hAc : IsCompact A := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const F1.continuous_vcoord).inter
        (isClosed_le continuous_norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : Space n)) (r := M₁)).subset fun y hy => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hy.2
  have hfA : IntegrableOn f A := (hfc.mono hAH).integrableOn_compact hAc
  -- the dyadic shells
  set sh : ℕ → Set (Space n) := fun k => shell n l (2 ^ k * M₁) with hsh
  have hfsh : ∀ k, IntegrableOn f (sh k) := fun k =>
    (hfc.mono shell_subset_H).integrableOn_compact (isCompact_shell l _)
  have hbound : ∀ k : ℕ, ∫ y in sh k, ‖f y‖ ≤ max C₁ 0 * Real.exp (-1) ^ k := by
    intro k
    have hk1 : (k : ℝ) ≤ 2 ^ k * M₁ := by
      have h1 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      have h2 : (2 : ℝ) ^ k ≤ 2 ^ k * M₁ := le_mul_of_one_le_right (by positivity) hM₁1
      linarith
    have hkM : M₀ ≤ 2 ^ k * M₁ := by
      have h2 : M₁ ≤ 2 ^ k * M₁ :=
        le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
      linarith [le_max_left M₀ 1]
    have hnorm : ∫ y in sh k, ‖f y‖ = ∫ y in sh k, f y := by
      congr 1
      funext y
      exact Real.norm_of_nonneg (hf0 y)
    rw [hnorm]
    calc ∫ y in sh k, f y ≤ C₁ * Real.exp (-1 * (2 ^ k * M₁)) := hC₁ _ hkM
      _ ≤ max C₁ 0 * Real.exp (-1 * (2 ^ k * M₁)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C₁ 0 * Real.exp (-1) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          rw [← Real.exp_nat_mul]
          exact Real.exp_le_exp.mpr (by linarith)
  have hsum : Summable fun k : ℕ => ∫ y in sh k, ‖f y‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _) hbound ?_
    exact (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _
  have hfU : IntegrableOn f (⋃ k, sh k) := integrableOn_iUnion_of_summable_integral_norm hfsh hsum
  refine (hfA.union hfU).mono_set ?_
  intro y hy
  have hy1 : l + 1 ≤ vcoord y := hy
  by_cases hyM : ‖y‖ ≤ M₁
  · exact Or.inl ⟨hy1, hyM⟩
  · push Not at hyM
    have hM₁0 : 0 < M₁ := by linarith
    have hx : 1 ≤ ‖y‖ / M₁ := by rw [le_div_iff₀ hM₁0]; linarith
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    refine Or.inr (Set.mem_iUnion.mpr ⟨k, hy1, ?_, ?_⟩)
    · rw [le_div_iff₀ hM₁0] at hk1
      exact hk1
    · rw [div_lt_iff₀ hM₁0, pow_succ] at hk2
      linarith

/-- **The cutoff argument of Proposition PL**, in the half-space. -/
theorem PL_core (K : ℝ) (hK : 0 ≤ K) : ∃ l₂ : ℝ, 1 ≤ l₂ ∧ ∀ l : ℝ, l₂ ≤ l →
    ∀ (A : Space n → Space n →L[ℝ] Space n) (β : Space n → Space n) (γ : Space n → ℝ),
      CarlCoeffs A β γ K l →
      ∀ U : Space n → ℝ, (∀ y ∈ H n l, ContDiffAt ℝ 2 U y) →
      (∀ y ∈ H n l, ellOp A β γ U y = 0) →
      (∀ N : ℝ, ∃ CN M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
        ∫ y in shell n l M, (U y ^ 2 + ‖gradient U y‖ ^ 2) ≤ CN * Real.exp (-N * M)) →
      ∀ y ∈ H n (l + 3), U y = 0 := by
  obtain ⟨C₀, l₁, τ₁, C₄, hC₀, hl₁, hl₁C, hτ₁, hC₄, hcarl⟩ := carleman (n := n) K hK
  refine ⟨l₁, hl₁, ?_⟩
  intro l hl A β γ hc U hU hLU hshell y₀ hy₀
  have hl1 : 1 ≤ l := le_trans hl₁ hl
  have hl0 : 0 ≤ l := by linarith
  have hC₀l : C₀ ≤ l := by linarith
  have hy₀s : l + 3 < vcoord y₀ := hy₀
  obtain ⟨Ccut, hCcut, hcut⟩ := cutoff_bound hK hl1 hc hU hLU
  set f : Space n → ℝ := fun z => U z ^ 2 + ‖gradient U z‖ ^ 2 with hf
  have hfE : IntegrableOn f {z | l + 1 ≤ vcoord z} := integrableOn_E hl0 hU hshell
  set I : ℝ := ∫ z in {z : Space n | l + 1 ≤ vcoord z}, f z with hI
  have hI0 : 0 ≤ I :=
    setIntegral_nonneg (measurableSet_le measurable_const F1.continuous_vcoord.measurable)
      (fun z _ => by positivity)
  by_contra hne
  -- a small ball around `y₀` on which `W U² ≥ c`
  obtain ⟨ρ, hρ, c, hc0, hQH, hQc⟩ : ∃ ρ > 0, ∃ c > 0, Metric.ball y₀ ρ ⊆ H n (l + 3) ∧
      ∀ z ∈ Metric.ball y₀ ρ, c ≤ (vcoord z ^ 2)⁻¹ * U z ^ 2 := by
    have hs : 0 < vcoord y₀ := by linarith
    have hFc : ContinuousAt (fun z : Space n => (vcoord z ^ 2)⁻¹ * U z ^ 2) y₀ :=
      ((F1.continuous_vcoord.pow 2).continuousAt.inv₀ (pow_ne_zero 2 hs.ne')).mul
        ((hU y₀ (H_mono (by linarith) hy₀)).continuousAt.pow 2)
    have hu : 0 < U y₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    have ha : 0 < (vcoord y₀ ^ 2)⁻¹ * U y₀ ^ 2 := by positivity
    have hev1 : ∀ᶠ z in 𝓝 y₀, (vcoord y₀ ^ 2)⁻¹ * U y₀ ^ 2 / 2 < (vcoord z ^ 2)⁻¹ * U z ^ 2 :=
      hFc.eventually (lt_mem_nhds (half_lt_self ha))
    have hev2 : ∀ᶠ z in 𝓝 y₀, z ∈ H n (l + 3) := (isOpen_H (l + 3)).mem_nhds hy₀
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hev1.and hev2)
    exact ⟨ρ, hρ, _, by positivity, fun z hz => (hball z hz).2, fun z hz => (hball z hz).1.le⟩
  set m : ℝ := c * volume.real (Metric.ball y₀ ρ) with hm
  have hm0 : 0 < m := by
    have h1 : 0 < volume (Metric.ball y₀ ρ) := Metric.measure_ball_pos volume y₀ hρ
    have h2 : volume (Metric.ball y₀ ρ) < ⊤ := measure_ball_lt_top
    have h3 : 0 < volume.real (Metric.ball y₀ ρ) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos h1.ne' h2.ne
    exact mul_pos hc0 h3
  have hmono : gw C₀ (l + 2) ≤ gw C₀ (l + 3) := gw_mono hC₀ (by linarith) (by linarith)
  -- the main inequality
  have hmain : ∀ τ : ℝ, τ₁ ≤ τ → ∀ ε > 0, τ ^ 3 * Real.exp (2 * τ * gw C₀ (l + 3)) * m ≤
      C₄ * Ccut * (Real.exp (2 * τ * gw C₀ (l + 2)) * I) + ε := by
    intro τ hτ ε hε
    have hτ0 : 0 < τ := by linarith
    obtain ⟨CN, M₀, hCN⟩ := hshell (5 * τ)
    -- choose `M`
    obtain ⟨M, hM1, hM0, hMy, hMε⟩ : ∃ M : ℝ, 1 ≤ M ∧ M₀ ≤ M ∧ ‖y₀‖ + ρ ≤ M ∧
        C₄ * Ccut * (Real.exp (2 * τ * (2 * M)) * (CN * Real.exp (-(5 * τ) * M))) ≤ ε := by
      have heq : (fun M : ℝ => C₄ * Ccut * (Real.exp (2 * τ * (2 * M))
          * (CN * Real.exp (-(5 * τ) * M)))) = fun M => C₄ * Ccut * CN * Real.exp (-(τ * M)) := by
        funext M
        rw [show -(τ * M) = 2 * τ * (2 * M) + -(5 * τ) * M by ring, Real.exp_add]
        ring
      have hlim : Tendsto (fun M : ℝ => C₄ * Ccut * (Real.exp (2 * τ * (2 * M))
          * (CN * Real.exp (-(5 * τ) * M)))) atTop (𝓝 0) := by
        rw [heq]
        have h1 : Tendsto (fun M : ℝ => τ * M) atTop atTop := tendsto_id.const_mul_atTop hτ0
        have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (C₄ * Ccut * CN)
        simpa [Function.comp_def] using h2
      obtain ⟨M, h1, h2, h3, h4⟩ := ((hlim.eventually (gt_mem_nhds hε)).and
        ((eventually_ge_atTop 1).and ((eventually_ge_atTop M₀).and
          (eventually_ge_atTop (‖y₀‖ + ρ))))).exists
      exact ⟨M, h2, h3, h4, h1.le⟩
    have hMpos : 0 < M := by linarith
    set vM : Space n → ℝ := fun z => cutM l M z * U z with hvM
    obtain ⟨hvM2, hvMc, hvMs⟩ := cutM_mul_props hl0 hMpos hU
    have hC := hcarl l hl A β γ hc τ hτ vM hvM2 hvMc hvMs
    -- lower bound for the left side
    have hlow : τ ^ 3 * Real.exp (2 * τ * gw C₀ (l + 3)) * m ≤
        τ ^ 3 * (∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y)) * vM y ^ 2)
          + τ * (∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y))
              * ‖gradient vM y‖ ^ 2) := by
      have hint := (carleman_integrable hl0 (C₀ := C₀) (τ := τ) hc hvM2 hvMc hvMs).1
      have hG : 0 ≤ ∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y))
          * ‖gradient vM y‖ ^ 2 :=
        integral_nonneg fun y => by positivity
      have hQsub : ∫ y in Metric.ball y₀ ρ, (vcoord y ^ 2)⁻¹
            * Real.exp (2 * τ * gw C₀ (vcoord y)) * vM y ^ 2
          ≤ ∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y)) * vM y ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun y => by positivity)
      have hQlow : Real.exp (2 * τ * gw C₀ (l + 3)) * c * volume.real (Metric.ball y₀ ρ)
          ≤ ∫ y in Metric.ball y₀ ρ, (vcoord y ^ 2)⁻¹
            * Real.exp (2 * τ * gw C₀ (vcoord y)) * vM y ^ 2 := by
        apply setIntegral_ge_of_const_le_real measurableSet_ball measure_ball_lt_top.ne
        · intro z hz
          have hzs : l + 3 < vcoord z := hQH hz
          have hznorm : ‖z‖ ≤ M := by
            have h1 : dist z y₀ < ρ := hz
            rw [dist_eq_norm] at h1
            have h2 := norm_sub_norm_le z y₀
            linarith
          have hcut1 : cutM l M z = 1 := cutM_eq_one hMpos (by linarith) hznorm
          have hvMz : vM z = U z := by simp only [hvM, hcut1, one_mul]
          have hE : Real.exp (2 * τ * gw C₀ (l + 3)) ≤ Real.exp (2 * τ * gw C₀ (vcoord z)) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (gw_mono hC₀ (by linarith) hzs.le)
              (by linarith))
          have hcz := hQc z hz
          rw [hvMz]
          calc Real.exp (2 * τ * gw C₀ (l + 3)) * c
              ≤ Real.exp (2 * τ * gw C₀ (vcoord z)) * ((vcoord z ^ 2)⁻¹ * U z ^ 2) :=
                mul_le_mul hE hcz hc0.le (Real.exp_pos _).le
            _ = _ := by ring
        · exact hint.integrableOn
      have hτ3 : 0 ≤ τ ^ 3 := by positivity
      calc τ ^ 3 * Real.exp (2 * τ * gw C₀ (l + 3)) * m
          = τ ^ 3 * (Real.exp (2 * τ * gw C₀ (l + 3)) * c * volume.real (Metric.ball y₀ ρ)) := by
            rw [hm]; ring
        _ ≤ τ ^ 3 * ∫ y, (vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y)) * vM y ^ 2 :=
            mul_le_mul_of_nonneg_left (hQlow.trans hQsub) hτ3
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hτ0.le hG)
    -- upper bound for the right side
    have hup : ∫ y, Real.exp (2 * τ * gw C₀ (vcoord y)) * ellOp A β γ vM y ^ 2 ≤
        Ccut * (Real.exp (2 * τ * gw C₀ (l + 2)) * I
          + Real.exp (2 * τ * (2 * M)) * (CN * Real.exp (-(5 * τ) * M))) := by
      have hint4 := (carleman_integrable hl0 (C₀ := C₀) (τ := τ) hc hvM2 hvMc hvMs).2
      have hfcont : ContinuousOn f (H n l) := continuousOn_energy hU
      have hfs : IntegrableOn f (slab n l M) :=
        (hfcont.mono slab_subset_H).integrableOn_compact (isCompact_slab l M)
      have hfsh : IntegrableOn f (shell n l M) :=
        (hfcont.mono shell_subset_H).integrableOn_compact (isCompact_shell l M)
      have hslab_meas : MeasurableSet (slab n l M) := (isClosed_slab l M).measurableSet
      have hshell_meas : MeasurableSet (shell n l M) := (isClosed_shell l M).measurableSet
      set e2 := Real.exp (2 * τ * gw C₀ (l + 2)) with he2
      set e4 := Real.exp (2 * τ * (2 * M)) with he4
      have hpt : ∀ y, Real.exp (2 * τ * gw C₀ (vcoord y)) * ellOp A β γ vM y ^ 2 ≤
          Ccut * (e2 * (slab n l M).indicator f y + e4 * (shell n l M).indicator f y) := by
        intro y
        have h1 := hcut M hM1 y
        have hEy := Real.exp_pos (2 * τ * gw C₀ (vcoord y))
        have hs1 : Real.exp (2 * τ * gw C₀ (vcoord y)) * (slab n l M).indicator f y
            ≤ e2 * (slab n l M).indicator f y := by
          by_cases hy : y ∈ slab n l M
          · rw [Set.indicator_of_mem hy]
            have hfy : 0 ≤ f y := by positivity
            apply mul_le_mul_of_nonneg_right _ hfy
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
              (gw_mono hC₀ (by linarith [hy.1]) hy.2.1) (by linarith))
          · rw [Set.indicator_of_notMem hy]
            simp
        have hs2 : Real.exp (2 * τ * gw C₀ (vcoord y)) * (shell n l M).indicator f y
            ≤ e4 * (shell n l M).indicator f y := by
          by_cases hy : y ∈ shell n l M
          · rw [Set.indicator_of_mem hy]
            have hfy : 0 ≤ f y := by positivity
            apply mul_le_mul_of_nonneg_right _ hfy
            apply Real.exp_le_exp.mpr
            have : gw C₀ (vcoord y) ≤ 2 * M :=
              (gw_le_self hC₀.le (by linarith [hy.1])).trans ((vcoord_le_norm y).trans hy.2.2)
            nlinarith
          · rw [Set.indicator_of_notMem hy]
            simp
        calc Real.exp (2 * τ * gw C₀ (vcoord y)) * ellOp A β γ vM y ^ 2
            ≤ Real.exp (2 * τ * gw C₀ (vcoord y))
              * (Ccut * ((slab n l M).indicator f y + (shell n l M).indicator f y)) :=
              mul_le_mul_of_nonneg_left h1 hEy.le
          _ = Ccut * (Real.exp (2 * τ * gw C₀ (vcoord y)) * (slab n l M).indicator f y
              + Real.exp (2 * τ * gw C₀ (vcoord y)) * (shell n l M).indicator f y) := by ring
          _ ≤ Ccut * (e2 * (slab n l M).indicator f y + e4 * (shell n l M).indicator f y) :=
              mul_le_mul_of_nonneg_left (add_le_add hs1 hs2) hCcut
      have hg1 : Integrable (fun y => e2 * (slab n l M).indicator f y) :=
        (hfs.integrable_indicator hslab_meas).const_mul e2
      have hg2 : Integrable (fun y => e4 * (shell n l M).indicator f y) :=
        (hfsh.integrable_indicator hshell_meas).const_mul e4
      have hg12 : Integrable (fun y => e2 * (slab n l M).indicator f y
          + e4 * (shell n l M).indicator f y) := hg1.add hg2
      have hg : Integrable (fun y => Ccut * (e2 * (slab n l M).indicator f y
          + e4 * (shell n l M).indicator f y)) := hg12.const_mul Ccut
      have hmon := integral_mono hint4 hg hpt
      rw [integral_const_mul, integral_add hg1 hg2, integral_const_mul, integral_const_mul,
        integral_indicator hslab_meas, integral_indicator hshell_meas] at hmon
      have hslabI : ∫ y in slab n l M, f y ≤ I :=
        setIntegral_mono_set hfE (Eventually.of_forall fun y => by positivity)
          (Filter.eventuallySubset_iff.2 (Eventually.of_forall fun y hy => hy.1))
      have hshellI : ∫ y in shell n l M, f y ≤ CN * Real.exp (-(5 * τ) * M) := hCN M hM0
      calc _ ≤ _ := hmon
        _ ≤ Ccut * (e2 * I + e4 * (CN * Real.exp (-(5 * τ) * M))) := by
          apply mul_le_mul_of_nonneg_left _ hCcut
          exact add_le_add (mul_le_mul_of_nonneg_left hslabI (Real.exp_pos _).le)
            (mul_le_mul_of_nonneg_left hshellI (Real.exp_pos _).le)
    calc τ ^ 3 * Real.exp (2 * τ * gw C₀ (l + 3)) * m ≤ _ := hlow
      _ ≤ C₄ * ∫ y, Real.exp (2 * τ * gw C₀ (vcoord y)) * ellOp A β γ vM y ^ 2 := hC
      _ ≤ C₄ * (Ccut * (Real.exp (2 * τ * gw C₀ (l + 2)) * I
          + Real.exp (2 * τ * (2 * M)) * (CN * Real.exp (-(5 * τ) * M)))) :=
            mul_le_mul_of_nonneg_left hup hC₄.le
      _ = C₄ * Ccut * (Real.exp (2 * τ * gw C₀ (l + 2)) * I)
          + C₄ * Ccut * (Real.exp (2 * τ * (2 * M)) * (CN * Real.exp (-(5 * τ) * M))) := by ring
      _ ≤ _ := by linarith [hMε]
  have hfin : ∀ τ : ℝ, τ₁ ≤ τ → τ ^ 3 * m ≤ C₄ * Ccut * I := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := by linarith
    have h1 : τ ^ 3 * Real.exp (2 * τ * gw C₀ (l + 3)) * m ≤
        C₄ * Ccut * (Real.exp (2 * τ * gw C₀ (l + 2)) * I) :=
      le_of_forall_pos_le_add fun ε hε => hmain τ hτ ε hε
    have h2 : Real.exp (2 * τ * gw C₀ (l + 2)) ≤ Real.exp (2 * τ * gw C₀ (l + 3)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hexp := Real.exp_pos (2 * τ * gw C₀ (l + 3))
    have hCI : 0 ≤ C₄ * Ccut * I := by positivity
    have h3 : C₄ * Ccut * (Real.exp (2 * τ * gw C₀ (l + 2)) * I)
        ≤ C₄ * Ccut * I * Real.exp (2 * τ * gw C₀ (l + 3)) := by
      calc C₄ * Ccut * (Real.exp (2 * τ * gw C₀ (l + 2)) * I)
          = C₄ * Ccut * I * Real.exp (2 * τ * gw C₀ (l + 2)) := by ring
        _ ≤ C₄ * Ccut * I * Real.exp (2 * τ * gw C₀ (l + 3)) := mul_le_mul_of_nonneg_left h2 hCI
    have h4 : τ ^ 3 * m * Real.exp (2 * τ * gw C₀ (l + 3))
        ≤ C₄ * Ccut * I * Real.exp (2 * τ * gw C₀ (l + 3)) := by
      calc τ ^ 3 * m * Real.exp (2 * τ * gw C₀ (l + 3))
          = τ ^ 3 * Real.exp (2 * τ * gw C₀ (l + 3)) * m := by ring
        _ ≤ _ := h1
        _ ≤ _ := h3
    exact le_of_mul_le_mul_right h4 hexp
  -- contradiction for large `τ`
  set τ : ℝ := max τ₁ (C₄ * Ccut * I / m + 1) with hτdef
  have hτ1 : τ₁ ≤ τ := le_max_left _ _
  have hτ2 : C₄ * Ccut * I / m + 1 ≤ τ := le_max_right _ _
  have hτ0 : 1 ≤ τ := le_trans hτ₁ hτ1
  have h := hfin τ hτ1
  have hτ3 : τ ≤ τ ^ 3 := by
    have h1 : 0 ≤ τ * (τ - 1) * (τ + 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have hlt : C₄ * Ccut * I < τ * m := by
    have : C₄ * Ccut * I / m < τ := by linarith
    rwa [div_lt_iff₀ hm0] at this
  nlinarith [mul_le_mul_of_nonneg_right hτ3 hm0.le]

/-- **Decay on shells** for `U = v ∘ Φ`: the change of variables `x = Φ(y)` in the decay
hypothesis. -/
theorem shell_decay (S : HalfBallSolution n)
    (hdecay : ∀ N : ℝ, ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 S.R,
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cn * Real.exp (-N / r))
    {l : ℝ} (hl : 1 ≤ l) (hlR : 1 / l < S.R) :
    ∀ N : ℝ, ∃ CN M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
      ∫ y in shell n l M, ((S.v ∘ invMap) y ^ 2 + ‖gradient (S.v ∘ invMap) y‖ ^ 2)
        ≤ CN * Real.exp (-N * M) := by
  sorry

end PL

open PL in
/-- **Proposition PL.** Interior decay faster than every `e^{-N/r}` forces the solution to vanish
on a ball tangent to the flat boundary at `0`. -/
theorem HalfBallSolution.vanish_of_superexp (S : HalfBallSolution n)
    (hdecay : ∀ N : ℝ, ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 S.R,
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cn * Real.exp (-N / r)) :
    ∃ r' > 0, ∀ x ∈ Metric.ball (r' • ed n) r', S.v x = 0 := by
  obtain ⟨K', hK', hcoef⟩ := carlCoeffs_t S
  obtain ⟨l₂, hl₂, hcore⟩ := PL_core (n := n) K' hK'
  set l : ℝ := max l₂ (2 / S.R) with hl_def
  have hl1 : 1 ≤ l := le_trans hl₂ (le_max_left _ _)
  have hl0 : 0 < l := lt_of_lt_of_le one_pos hl1
  have hlR : 1 / l < S.R := by
    have h2 : 2 / S.R ≤ l := le_max_right _ _
    have hR := S.R_pos
    rw [div_lt_iff₀ hl0]
    rw [div_le_iff₀ hR] at h2
    linarith
  -- `U = v ∘ Φ` on `H n l`
  have hr : (0 : ℝ) < 1 / (2 * l) := by positivity
  have hHl : H n (1 / (2 * (1 / (2 * l)))) = H n l := by
    congr 1
    field_simp
  have hmemhB : ∀ y ∈ H n l, invMap y ∈ halfBall n S.R := by
    intro y hy
    rw [← hHl] at hy
    have h1 := ball_subset_halfBall hr (invMap_mem_ball hr hy)
    refine halfBall_mono ?_ h1
    have : 2 * (1 / (2 * l)) = 1 / l := by field_simp
    rw [this]
    exact hlR.le
  have hU2 : ∀ y ∈ H n l, ContDiffAt ℝ 2 (S.v ∘ invMap) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_zero_of_mem_H hl0.le hy
    have hv : ContDiffAt ℝ 2 S.v (invMap y) :=
      S.v_contDiffOn.contDiffAt ((isOpen_halfBall S.R).mem_nhds (hmemhB y hy))
    exact hv.comp y (contDiffAt_invMap hy0)
  have hLU : ∀ y ∈ H n l, ellOp (tA S.A) (tB S.A S.B) (tC S.C) (S.v ∘ invMap) y = 0 := by
    intro y hy
    have hy0 : y ≠ 0 := ne_zero_of_mem_H hl0.le hy
    have hv : ContDiffAt ℝ 2 S.v (invMap y) :=
      S.v_contDiffOn.contDiffAt ((isOpen_halfBall S.R).mem_nhds (hmemhB y hy))
    rw [ellOp_comp_invMap S.A S.B S.C (S.coeffs.contDiff_A.of_le (by norm_num)) S.coeffs.symm
      S.v hy0 hv, S.eqn _ (hmemhB y hy), mul_zero]
  have hzero := hcore l (le_max_left _ _) (tA S.A) (tB S.A S.B) (tC S.C) (hcoef.mono hl1)
    (S.v ∘ invMap) hU2 hLU (shell_decay S hdecay hl1 hlR)
  refine ⟨1 / (2 * (l + 3)), by positivity, fun x hx => ?_⟩
  have hx' := invMap_mem_H (by positivity) hx
  have hH3 : H n (1 / (2 * (1 / (2 * (l + 3))))) = H n (l + 3) := by
    congr 1
    field_simp
  rw [hH3] at hx'
  have := hzero _ hx'
  simpa [Function.comp_apply, invMap_invMap] using this

end MazyaRefinedCauchy
