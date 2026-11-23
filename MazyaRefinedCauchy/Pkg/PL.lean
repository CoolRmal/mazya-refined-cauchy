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

Status: the contract theorem is proved from the helpers; the only two helpers still open are
`tA_deriv_bounds` (derivative bounds of the transformed matrix, part of Lemma inversion) and
`carleman_P0` (the half-space Carleman estimate for `div(A∇·)`, Proposition carleman).

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

theorem refl_refl {y : Space n} (hy : y ≠ 0) (ξ : Space n) : refl y (refl y ξ) = ξ := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have hyy : ⟪y, y⟫_ℝ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  rw [refl_apply, refl_apply, inner_sub_right, real_inner_smul_right, hyy]
  have : 2 * (‖y‖ ^ 2)⁻¹ * (⟪y, ξ⟫_ℝ - 2 * (‖y‖ ^ 2)⁻¹ * ⟪y, ξ⟫_ℝ * ‖y‖ ^ 2)
      = -(2 * (‖y‖ ^ 2)⁻¹ * ⟪y, ξ⟫_ℝ) := by
    field_simp
    ring
  rw [this, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem refl_self {y : Space n} (hy : y ≠ 0) : refl y y = -y := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  rw [refl_apply, real_inner_self_eq_norm_sq]
  have : 2 * (‖y‖ ^ 2)⁻¹ * ‖y‖ ^ 2 = 2 := by field_simp
  rw [this, two_smul]
  abel

theorem hasFDerivAt_normSqInv {y : Space n} (hy : y ≠ 0) :
    HasFDerivAt (fun z : Space n => (‖z‖ ^ 2)⁻¹)
      ((-(2 * ((‖y‖ ^ 2)⁻¹) ^ 2)) • innerSL ℝ y) y := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun x : Space n => ‖x‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hinv := (hasDerivAt_inv h2).comp_hasFDerivAt y h1
  refine hinv.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun ξ => ?_
  simp only [smul_apply, innerSL_apply_apply, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  ring

theorem traceCLM_smulRight (f : Space n →L[ℝ] ℝ) (w : Space n) :
    F2.traceCLM (f.smulRight w) = f w := by
  rw [F2.traceCLM_apply]
  have := LinearMap.trace_smulRight (R := ℝ) (M := Space n) (f : Space n →ₗ[ℝ] ℝ) w
  convert this using 2
  ext v
  simp

theorem traceCLM_comp_refl (L : Space n →L[ℝ] Space n) (y : Space n) :
    F2.traceCLM (L ∘L ((‖y‖ ^ 2)⁻¹ • refl y))
      = (‖y‖ ^ 2)⁻¹ * (F2.traceCLM L - 2 * (‖y‖ ^ 2)⁻¹ * ⟪y, L y⟫_ℝ) := by
  have hdec : L ∘L ((‖y‖ ^ 2)⁻¹ • refl y)
      = (‖y‖ ^ 2)⁻¹ • (L - (2 * (‖y‖ ^ 2)⁻¹) • (innerSL ℝ y).smulRight (L y)) := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    simp only [ContinuousLinearMap.comp_apply, smul_apply, sub_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, refl_apply, map_sub, map_smul]
    module
  rw [hdec, map_smul, map_sub, map_smul, traceCLM_smulRight, innerSL_apply_apply, smul_eq_mul,
    smul_eq_mul]

theorem divergence_id' (y : Space n) : divergence (fun z : Space n => z) y = n + 1 := by
  rw [F2.divergence_eq_traceCLM, fderiv_fun_id, F2.traceCLM_apply, ContinuousLinearMap.coe_id,
    LinearMap.trace_id, finrank_euclideanSpace_fin]
  push_cast
  ring

/-- **Lemma inversion (pointwise form).** The operator transforms under `Φ` as
`L̃(v ∘ Φ)(y) = ‖y‖⁻⁴ (L v)(Φ y)`. -/
theorem ellOp_comp_invMap (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n)
    (C : Space n → ℝ) (hA : ContDiff ℝ 1 A) (hsymm : ∀ x ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (v : Space n → ℝ) {y : Space n} (hy : y ≠ 0) (hv : ContDiffAt ℝ 2 v (invMap y)) :
    ellOp (tA A) (tB A B) (tC C) (v ∘ invMap) y = (‖y‖ ^ 4)⁻¹ * ellOp A B C v (invMap y) := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have hyy : ⟪y, y⟫_ℝ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  set x₀ := invMap y with hx₀
  -- regularity at `x₀`
  have hgv : DifferentiableAt ℝ (gradient v) x₀ := F2.differentiableAt_gradient hv
  have hAd : DifferentiableAt ℝ A x₀ := (hA.differentiable one_ne_zero) x₀
  set F : Space n → Space n := fun x => A x (gradient v x) with hF
  have hFd : DifferentiableAt ℝ F x₀ := hAd.clm_apply hgv
  set H : Space n → Space n := fun z => F (invMap z) with hH
  have hHd : HasFDerivAt H ((fderiv ℝ F x₀).comp ((‖y‖ ^ 2)⁻¹ • refl y)) y := by
    have := HasFDerivAt.comp y (g := F) hFd.hasFDerivAt (hasFDerivAt_invMap hy)
    exact this
  -- the transformed field near `y`
  have hev : ∀ᶠ z in 𝓝 y, z ≠ 0 ∧ DifferentiableAt ℝ v (invMap z) := by
    have h1 : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 2 v x := hv.eventually (by simp)
    have h3 : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 v (invMap z) :=
      (contDiffAt_invMap hy (k := 0)).continuousAt.tendsto.eventually h1
    filter_upwards [eventually_ne_nhds hy, h3] with z hz hz3
    exact ⟨hz, hz3.differentiableAt (by simp)⟩
  set c : Space n → ℝ := fun z => 2 * ((‖z‖ ^ 2)⁻¹) ^ 2 * ⟪z, H z⟫_ℝ with hc
  have hfield : (fun z => tA A z (gradient (v ∘ invMap) z)) =ᶠ[𝓝 y]
      fun z => (‖z‖ ^ 2)⁻¹ • H z - c z • z := by
    filter_upwards [hev] with z ⟨hz, hvz⟩
    rw [gradient_comp_invMap v hz hvz]
    simp only [tA, ContinuousLinearMap.comp_apply, map_smul, refl_refl hz]
    rw [refl_apply]
    simp only [hH, hF, hc, smul_sub, smul_smul]
    congr 2
    ring
  -- derivatives of the pieces
  have hN := hasFDerivAt_normSqInv hy
  have hHd' : DifferentiableAt ℝ H y := hHd.differentiableAt
  have hcd : HasFDerivAt c _ y :=
    ((hN.pow 2).const_mul 2).mul ((hasFDerivAt_id y).inner ℝ hHd)
  have hdiv : divergence (fun z => tA A z (gradient (v ∘ invMap) z)) y
      = ((‖y‖ ^ 2)⁻¹ * divergence H y + fderiv ℝ (fun z : Space n => (‖z‖ ^ 2)⁻¹) y (H y))
        - (c y * divergence (fun z : Space n => z) y + fderiv ℝ c y y) := by
    rw [F2.divergence_congr hfield]
    have hd1 : DifferentiableAt ℝ (fun z => (‖z‖ ^ 2)⁻¹ • H z) y := hN.differentiableAt.smul hHd'
    have hd2 : DifferentiableAt ℝ (fun z => c z • z) y := hcd.differentiableAt.smul differentiableAt_id
    rw [F2.divergence_sub hd1 hd2, F2.divergence_smul hN.differentiableAt hHd',
      F2.divergence_smul hcd.differentiableAt differentiableAt_fun_id]
  have hdivH : divergence H y = (‖y‖ ^ 2)⁻¹
      * (F2.traceCLM (fderiv ℝ F x₀) - 2 * (‖y‖ ^ 2)⁻¹ * ⟪y, fderiv ℝ F x₀ y⟫_ℝ) := by
    rw [F2.divergence_eq_traceCLM, hHd.fderiv, traceCLM_comp_refl]
  have hDN : fderiv ℝ (fun z : Space n => (‖z‖ ^ 2)⁻¹) y (H y)
      = -(2 * ((‖y‖ ^ 2)⁻¹) ^ 2) * ⟪y, H y⟫_ℝ := by
    rw [hN.fderiv]
    simp
  have hDH : fderiv ℝ H y y = -((‖y‖ ^ 2)⁻¹ • fderiv ℝ F x₀ y) := by
    rw [hHd.fderiv, ContinuousLinearMap.comp_apply, smul_apply, refl_self hy, smul_neg, map_neg,
      map_smul]
  have hDc : fderiv ℝ c y y = 2 * (2 * (‖y‖ ^ 2)⁻¹ * (-(2 * ((‖y‖ ^ 2)⁻¹) ^ 2) * ⟪y, y⟫_ℝ))
        * ⟪y, H y⟫_ℝ + 2 * ((‖y‖ ^ 2)⁻¹) ^ 2 * (⟪y, H y⟫_ℝ
          - (‖y‖ ^ 2)⁻¹ * ⟪y, fderiv ℝ F x₀ y⟫_ℝ) := by
    rw [hcd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, id, nsmul_eq_mul, Nat.cast_ofNat, refl_self hy, map_neg, map_smul,
      inner_neg_right, real_inner_smul_right]
    norm_num
    ring
  have hgy : gradient (v ∘ invMap) y = (‖y‖ ^ 2)⁻¹ • refl y (gradient v x₀) :=
    gradient_comp_invMap v hy (hv.differentiableAt (by simp))
  have hq : ⟪tA A y y, refl y (gradient v x₀)⟫_ℝ = -⟪y, H y⟫_ℝ := by
    simp only [tA, ContinuousLinearMap.comp_apply]
    rw [inner_refl_refl hy, refl_self hy, map_neg, inner_neg_left, hsymm]
  have hb : ⟪refl y (B x₀), refl y (gradient v x₀)⟫_ℝ = ⟪B x₀, gradient v x₀⟫_ℝ :=
    inner_refl_refl hy _ _
  have hHy : H y = F x₀ := rfl
  have hcy : c y = 2 * ((‖y‖ ^ 2)⁻¹) ^ 2 * ⟪y, H y⟫_ℝ := rfl
  simp only [ellOp]
  rw [hdiv, hdivH, hDN, hDc, divergence_id', hgy, hcy]
  simp only [tB, tC, Function.comp_apply, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, hq, ← hx₀, hb]
  rw [hyy, F2.divergence_eq_traceCLM (fun z => A z (gradient v z)), ← hF, hHy]
  field_simp
  ring

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

theorem norm_refl_le {y : Space n} (hy : y ≠ 0) : ‖refl y‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
    rw [norm_refl_apply hy, one_mul]

theorem tA_sub_id {y : Space n} (hy : y ≠ 0) (A : Space n → Space n →L[ℝ] Space n) :
    tA A y - ContinuousLinearMap.id ℝ (Space n)
      = refl y ∘L (A (invMap y) - ContinuousLinearMap.id ℝ (Space n)) ∘L refl y := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  simp [tA, refl_refl hy]

theorem norm_tA_le {y : Space n} (hy : y ≠ 0) (A : Space n → Space n →L[ℝ] Space n) :
    ‖tA A y‖ ≤ ‖A (invMap y)‖ := by
  unfold tA
  calc ‖refl y ∘L A (invMap y) ∘L refl y‖ ≤ ‖refl y‖ * (‖A (invMap y)‖ * ‖refl y‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖A (invMap y)‖ * 1) := by
        gcongr
        · exact norm_refl_le hy
        · exact norm_refl_le hy
    _ = _ := by ring

namespace W_PL_tA

/-! ### Helpers for `PL.tA_deriv_bounds`

All derivatives are taken within the open set `punct n = {y ≠ 0}` (`iteratedFDerivWithin`),
where `invMap` and `refl` are smooth.

1. `homog_bound`: if `f` is `C²` on `{y ≠ 0}` and `f (t • y) = t ^ a • f y` for `t > 0`, then
   `‖D^k f y‖ ≤ M ‖y‖ ^ (a - k)` (homogeneity plus compactness of the unit sphere).
2. Applied to `invMap` (degree `-1`) and `refl` (degree `0`).
3. `E y = A (invMap y) - I`: `‖E y‖ ≤ K / ‖y‖` (mean value theorem and `A 0 = I`); the
   derivative bounds come from `norm_iteratedFDerivWithin_comp_le` (Faà di Bruno bound).
4. Leibniz bound (`norm_iteratedFDerivWithin_le_of_bilinear_of_le_one` with `compL`) for
   `G y = refl y ∘L (E y ∘L refl y)`.
5. `tA A = G + I` on `{y ≠ 0}` (`tA_sub_id`), so `tA A` and `G` have the same derivatives.

Status: complete, every proof in this block is closed; `tA_deriv_bounds` uses only `propext`,
`Classical.choice`, `Quot.sound`. -/

/-- The punctured space `{y ≠ 0}`. -/
def punct (n : ℕ) : Set (Space n) := {y | y ≠ 0}

theorem isOpen_punct : IsOpen (punct n) := isOpen_ne

theorem uniqueDiffOn_punct : UniqueDiffOn ℝ (punct n) := isOpen_punct.uniqueDiffOn

/-- Homogeneity bound: a function that is `C²` away from `0` and positively homogeneous of
degree `a` has `k`-th derivative bounded by `M ‖y‖ ^ (a - k)`. -/
theorem homog_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (a : ℤ) (hf : ContDiffOn ℝ 2 f (punct n))
    (hhom : ∀ t : ℝ, 0 < t → ∀ y : Space n, y ≠ 0 → f (t • y) = (t ^ a) • f y)
    {k : ℕ} (hk : k ≤ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Space n, y ≠ 0 →
      ‖iteratedFDerivWithin ℝ k f (punct n) y‖ ≤ M * ‖y‖ ^ (a - k) := by
  have hk' : (k : ℕ∞ω) ≤ 2 := by exact_mod_cast hk
  have hsph : Metric.sphere (0 : Space n) 1 ⊆ punct n := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    intro h
    rw [h, norm_zero] at hz1
    exact zero_ne_one hz1
  have hcont : ContinuousOn (iteratedFDerivWithin ℝ k f (punct n))
      (Metric.sphere (0 : Space n) 1) :=
    (hf.continuousOn_iteratedFDerivWithin hk' uniqueDiffOn_punct).mono hsph
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Space n) 1).exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
  have ht : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set t : ℝ := ‖y‖ with ht_def
  set u : Space n := t⁻¹ • y with hu_def
  have hu1 : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, Real.norm_of_nonneg ht.le, inv_mul_cancel₀ ht.ne']
  have hu0 : u ∈ punct n := by
    intro h
    rw [h, norm_zero] at hu1
    exact zero_ne_one hu1
  set L : Space n →L[ℝ] Space n := t • ContinuousLinearMap.id ℝ (Space n) with hL_def
  have hLz : ∀ z, L z = t • z := fun z => rfl
  have hLu : L u = y := by
    rw [hLz, hu_def, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hpre : L ⁻¹' (punct n) = punct n := by
    ext z
    simp only [Set.mem_preimage, punct, Set.mem_ofPred_eq, hLz]
    exact smul_ne_zero_iff_right ht.ne'
  have h1 := L.iteratedFDerivWithin_comp_right hf uniqueDiffOn_punct
    (by rw [hpre]; exact uniqueDiffOn_punct) (x := u) (by rw [hLu]; exact hy) hk'
  rw [hpre, hLu] at h1
  have h2 : iteratedFDerivWithin ℝ k (f ∘ L) (punct n) u
      = (t ^ a) • iteratedFDerivWithin ℝ k f (punct n) u := by
    rw [iteratedFDerivWithin_congr (f := (t ^ a) • f) (fun z hz => ?_) hu0 k]
    · exact iteratedFDerivWithin_const_smul_apply ((hf u hu0).of_le hk') uniqueDiffOn_punct hu0
    · simp only [Function.comp_apply, Pi.smul_apply, hLz]
      exact hhom t ht z hz
  have h3 : (iteratedFDerivWithin ℝ k f (punct n) y).compContinuousLinearMap (fun _ => L)
      = (t ^ k) • iteratedFDerivWithin ℝ k f (punct n) y := by
    ext m
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hLz,
      smul_apply]
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp [Finset.prod_const]
  rw [h3, h2] at h1
  have hn := congrArg norm h1
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at hn
  have hMu : ‖iteratedFDerivWithin ℝ k f (punct n) u‖ ≤ max M 0 :=
    (hM u (mem_sphere_zero_iff_norm.mpr hu1)).trans (le_max_left _ _)
  have htk : 0 < t ^ k := pow_pos ht k
  have hta : 0 < t ^ a := zpow_pos ht a
  have hy' : ‖iteratedFDerivWithin ℝ k f (punct n) y‖
      = ‖iteratedFDerivWithin ℝ k f (punct n) u‖ * (t ^ a / t ^ k) := by
    field_simp
    linarith
  rw [hy', zpow_sub₀ ht.ne', zpow_natCast]
  exact mul_le_mul_of_nonneg_right hMu (by positivity)

/-- `Φ` is positively homogeneous of degree `-1`. -/
theorem invMap_smul {t : ℝ} (ht : 0 < t) (y : Space n) :
    invMap (t • y) = (t ^ (-1 : ℤ)) • invMap y := by
  have ht0 : t ≠ 0 := ht.ne'
  simp only [invMap, norm_smul, Real.norm_of_nonneg ht.le, smul_smul, zpow_neg, zpow_one]
  congr 1
  have e : ((t * ‖y‖) ^ 2)⁻¹ * t = t⁻¹ * (‖y‖ ^ 2)⁻¹ * (t * t⁻¹) := by
    rw [mul_pow, mul_inv]
    ring
  rw [e, mul_inv_cancel₀ ht0, mul_one]

/-- `ℛ` is positively homogeneous of degree `0`. -/
theorem refl_smul {t : ℝ} (ht : 0 < t) (y : Space n) :
    refl (t • y) = (t ^ (0 : ℤ)) • refl y := by
  have ht0 : t ≠ 0 := ht.ne'
  rw [zpow_zero, one_smul]
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [refl_apply, refl_apply, norm_smul, Real.norm_of_nonneg ht.le, real_inner_smul_left,
    smul_smul]
  congr 2
  have e2 : (t ^ 2)⁻¹ * t * t = 1 := by field_simp
  calc 2 * ((t * ‖y‖) ^ 2)⁻¹ * (t * ⟪y, ξ⟫_ℝ) * t
      = 2 * (‖y‖ ^ 2)⁻¹ * ⟪y, ξ⟫_ℝ * ((t ^ 2)⁻¹ * t * t) := by
        rw [mul_pow, mul_inv]
        ring
    _ = 2 * (‖y‖ ^ 2)⁻¹ * ⟪y, ξ⟫_ℝ := by rw [e2, mul_one]

/-- `ℛ` is `C²` away from `0`. -/
theorem contDiffAt_refl {y : Space n} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (refl : Space n → Space n →L[ℝ] Space n) y := by
  have h2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  have hs : ContDiffAt ℝ 2 (fun x : Space n => 2 * (‖x‖ ^ 2)⁻¹) y :=
    contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.inv h2)
  have hi : ContDiffAt ℝ 2 (fun x : Space n => (innerSL ℝ x).smulRight x) y :=
    ((innerSL ℝ : Space n →L[ℝ] Space n →L[ℝ] ℝ).contDiff.contDiffAt).smulRight contDiffAt_id
  exact contDiffAt_const.sub (hs.smul hi)

theorem contDiffOn_refl : ContDiffOn ℝ 2 (refl : Space n → Space n →L[ℝ] Space n) (punct n) :=
  fun _ hy => (contDiffAt_refl hy).contDiffWithinAt

theorem contDiffOn_invMap : ContDiffOn ℝ 2 (invMap : Space n → Space n) (punct n) :=
  fun _ hy => (contDiffAt_invMap hy).contDiffWithinAt

/-- Derivative bounds for the inversion: `‖DΦ‖ ≤ M ‖y‖⁻²`, `‖D²Φ‖ ≤ M ‖y‖⁻³`. -/
theorem invMap_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Space n, y ≠ 0 →
    ‖iteratedFDerivWithin ℝ 1 invMap (punct n) y‖ ≤ M * ‖y‖⁻¹ ^ 2 ∧
    ‖iteratedFDerivWithin ℝ 2 invMap (punct n) y‖ ≤ M * ‖y‖⁻¹ ^ 3 := by
  have hhom : ∀ t : ℝ, 0 < t → ∀ y : Space n, y ≠ 0 →
      invMap (t • y) = (t ^ (-1 : ℤ)) • invMap y := fun t ht y _ => invMap_smul ht y
  obtain ⟨M1, hM1, h1⟩ := homog_bound invMap (-1) contDiffOn_invMap hhom (k := 1) (by norm_num)
  obtain ⟨M2, hM2, h2⟩ := homog_bound invMap (-1) contDiffOn_invMap hhom (k := 2) le_rfl
  refine ⟨max M1 M2, le_max_of_le_left hM1, fun y hy => ⟨?_, ?_⟩⟩
  · have h := h1 y hy
    have e : ‖y‖ ^ ((-1 : ℤ) - ((1 : ℕ) : ℤ)) = ‖y‖⁻¹ ^ 2 := by
      rw [show (-1 : ℤ) - ((1 : ℕ) : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
        inv_pow]
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have h := h2 y hy
    have e : ‖y‖ ^ ((-1 : ℤ) - ((2 : ℕ) : ℤ)) = ‖y‖⁻¹ ^ 3 := by
      rw [show (-1 : ℤ) - ((2 : ℕ) : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
        inv_pow]
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- Derivative bounds for the reflection: `‖ℛ‖ ≤ 1`, `‖Dℛ‖ ≤ M ‖y‖⁻¹`, `‖D²ℛ‖ ≤ M ‖y‖⁻²`. -/
theorem refl_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Space n, y ≠ 0 →
    ‖iteratedFDerivWithin ℝ 0 refl (punct n) y‖ ≤ 1 ∧
    ‖iteratedFDerivWithin ℝ 1 refl (punct n) y‖ ≤ M * ‖y‖⁻¹ ∧
    ‖iteratedFDerivWithin ℝ 2 refl (punct n) y‖ ≤ M * ‖y‖⁻¹ ^ 2 := by
  have hhom : ∀ t : ℝ, 0 < t → ∀ y : Space n, y ≠ 0 →
      refl (t • y) = (t ^ (0 : ℤ)) • refl y := fun t ht y _ => refl_smul ht y
  obtain ⟨M1, hM1, h1⟩ := homog_bound refl 0 contDiffOn_refl hhom (k := 1) (by norm_num)
  obtain ⟨M2, hM2, h2⟩ := homog_bound refl 0 contDiffOn_refl hhom (k := 2) le_rfl
  refine ⟨max M1 M2, le_max_of_le_left hM1, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · rw [norm_iteratedFDerivWithin_zero]
    exact norm_refl_le hy
  · have h := h1 y hy
    have e : ‖y‖ ^ ((0 : ℤ) - ((1 : ℕ) : ℤ)) = ‖y‖⁻¹ := by
      rw [show (0 : ℤ) - ((1 : ℕ) : ℤ) = -1 by norm_num, zpow_neg_one]
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have h := h2 y hy
    have e : ‖y‖ ^ ((0 : ℤ) - ((2 : ℕ) : ℤ)) = ‖y‖⁻¹ ^ 2 := by
      rw [show (0 : ℤ) - ((2 : ℕ) : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
        inv_pow]
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- The perturbation `E = A ∘ Φ - I`. -/
noncomputable def Ef (S : HalfBallSolution n) (y : Space n) : Space n →L[ℝ] Space n :=
  S.A (invMap y) - ContinuousLinearMap.id ℝ (Space n)

theorem contDiffOn_Ef (S : HalfBallSolution n) : ContDiffOn ℝ 2 (Ef S) (punct n) := by
  exact (S.coeffs.contDiff_A.comp_contDiffOn contDiffOn_invMap).sub contDiffOn_const

/-- Bounds for `E = A ∘ Φ - I` and its first two derivatives, for `‖y‖ ≥ 1`. -/
theorem Ef_bounds (S : HalfBallSolution n) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Space n, 1 ≤ ‖y‖ →
    ‖iteratedFDerivWithin ℝ 0 (Ef S) (punct n) y‖ ≤ M * ‖y‖⁻¹ ∧
    ‖iteratedFDerivWithin ℝ 1 (Ef S) (punct n) y‖ ≤ M * ‖y‖⁻¹ ^ 2 ∧
    ‖iteratedFDerivWithin ℝ 2 (Ef S) (punct n) y‖ ≤ M * ‖y‖⁻¹ ^ 3 := by
  obtain ⟨MΦ, hMΦ, hΦ⟩ := invMap_bounds (n := n)
  have hK : 0 ≤ S.K := (norm_nonneg _).trans (S.coeffs.bound_A 0)
  refine ⟨S.K * MΦ + 2 * S.K * (MΦ + 1) ^ 2 + S.K, by positivity, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    exact absurd hy (by norm_num)
  have hyp : y ∈ punct n := hy0
  have hρ0 : 0 < ‖y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hy0)
  have hρ1 : ‖y‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
  obtain ⟨hΦ1, hΦ2⟩ := hΦ y hy0
  have hAΦ : ContDiffOn ℝ 2 (S.A ∘ invMap) (punct n) :=
    S.coeffs.contDiff_A.comp_contDiffOn contDiffOn_invMap
  -- the derivatives of `E` are those of `A ∘ Φ`
  have hEq : ∀ k : ℕ, k ≠ 0 → k ≤ 2 → iteratedFDerivWithin ℝ k (Ef S) (punct n) y
      = iteratedFDerivWithin ℝ k (S.A ∘ invMap) (punct n) y := by
    intro k hk hk2
    have e : Ef S = (S.A ∘ invMap) - fun _ => ContinuousLinearMap.id ℝ (Space n) := rfl
    rw [e, iteratedFDerivWithin_sub_apply ((hAΦ y hyp).of_le (by exact_mod_cast hk2))
      contDiffWithinAt_const uniqueDiffOn_punct hyp, iteratedFDerivWithin_const_of_ne hk,
      Pi.zero_apply, sub_zero]
  -- the derivatives of `A` are bounded by `K`
  have hA : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDerivWithin ℝ i S.A Set.univ (invMap y)‖ ≤ S.K := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      exact S.coeffs.bound_A _
    · rw [norm_iteratedFDeriv_one]
      exact S.coeffs.bound_dA _
    · exact S.coeffs.bound_d2A _
  refine ⟨?_, ?_, ?_⟩
  · -- `‖E y‖ ≤ K / ‖y‖` by the mean value theorem, since `A 0 = I`
    rw [norm_iteratedFDerivWithin_zero]
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := S.A) (s := Set.univ)
      (x := 0) (y := invMap y)
      (fun x _ => (S.coeffs.contDiff_A.differentiable (by norm_num)) x)
      (fun x _ => S.coeffs.bound_dA x) convex_univ trivial trivial
    rw [S.A_zero, sub_zero, norm_invMap] at h
    calc ‖Ef S y‖ ≤ S.K * ‖y‖⁻¹ := h
      _ ≤ (S.K * MΦ + 2 * S.K * (MΦ + 1) ^ 2 + S.K) * ‖y‖⁻¹ := by
        gcongr
        nlinarith [mul_nonneg hK hMΦ, mul_nonneg hK (sq_nonneg (MΦ + 1))]
  · rw [hEq 1 one_ne_zero (by norm_num)]
    have h := norm_iteratedFDerivWithin_comp_le (g := S.A) (f := invMap) (s := punct n)
      (t := Set.univ) (x := y) (n := 1) (N := 2) S.coeffs.contDiff_A.contDiffOn contDiffOn_invMap
      (by norm_num) uniqueDiffOn_univ uniqueDiffOn_punct (Set.mapsTo_univ _ _) hyp
      (C := S.K) (D := MΦ * ‖y‖⁻¹ ^ 2) (fun i hi => hA i (by omega)) (fun i hi1 hi2 => by
        have : i = 1 := by omega
        subst this
        rw [pow_one]
        exact hΦ1)
    calc _ ≤ _ := h
      _ = S.K * MΦ * ‖y‖⁻¹ ^ 2 := by
        simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
        ring
      _ ≤ (S.K * MΦ + 2 * S.K * (MΦ + 1) ^ 2 + S.K) * ‖y‖⁻¹ ^ 2 := by
        gcongr
        nlinarith [mul_nonneg hK hMΦ, mul_nonneg hK (sq_nonneg (MΦ + 1))]
  · rw [hEq 2 two_ne_zero le_rfl]
    have hsq : Real.sqrt ‖y‖⁻¹ ^ 2 = ‖y‖⁻¹ := Real.sq_sqrt hρ0.le
    have hρs : ‖y‖⁻¹ ≤ Real.sqrt ‖y‖⁻¹ := by
      have h1 : ‖y‖⁻¹ ^ 2 ≤ ‖y‖⁻¹ := by nlinarith
      calc ‖y‖⁻¹ = Real.sqrt (‖y‖⁻¹ ^ 2) := (Real.sqrt_sq hρ0.le).symm
        _ ≤ Real.sqrt ‖y‖⁻¹ := Real.sqrt_le_sqrt h1
    have hs0 : 0 ≤ Real.sqrt ‖y‖⁻¹ := Real.sqrt_nonneg _
    have h := norm_iteratedFDerivWithin_comp_le (g := S.A) (f := invMap) (s := punct n)
      (t := Set.univ) (x := y) (n := 2) (N := 2) S.coeffs.contDiff_A.contDiffOn contDiffOn_invMap
      le_rfl uniqueDiffOn_univ uniqueDiffOn_punct (Set.mapsTo_univ _ _) hyp
      (C := S.K) (D := (MΦ + 1) * ‖y‖⁻¹ * Real.sqrt ‖y‖⁻¹) (fun i hi => hA i hi)
      (fun i hi1 hi2 => by
        interval_cases i
        · rw [pow_one]
          calc ‖iteratedFDerivWithin ℝ 1 invMap (punct n) y‖ ≤ MΦ * ‖y‖⁻¹ ^ 2 := hΦ1
            _ = MΦ * ‖y‖⁻¹ * ‖y‖⁻¹ := by ring
            _ ≤ (MΦ + 1) * ‖y‖⁻¹ * Real.sqrt ‖y‖⁻¹ := by
              gcongr
              linarith
        · calc ‖iteratedFDerivWithin ℝ 2 invMap (punct n) y‖ ≤ MΦ * ‖y‖⁻¹ ^ 3 := hΦ2
            _ ≤ (MΦ + 1) ^ 2 * ‖y‖⁻¹ ^ 3 := by
              gcongr
              nlinarith
            _ = ((MΦ + 1) * ‖y‖⁻¹ * Real.sqrt ‖y‖⁻¹) ^ 2 := by
              rw [mul_pow, mul_pow, hsq]
              ring)
    calc _ ≤ _ := h
      _ = 2 * S.K * (MΦ + 1) ^ 2 * ‖y‖⁻¹ ^ 3 := by
        rw [mul_pow, mul_pow, hsq]
        norm_num
        ring
      _ ≤ (S.K * MΦ + 2 * S.K * (MΦ + 1) ^ 2 + S.K) * ‖y‖⁻¹ ^ 3 := by
        gcongr
        nlinarith [mul_nonneg hK hMΦ, mul_nonneg hK (sq_nonneg (MΦ + 1))]

/-- Leibniz bounds for a composition of operator-valued maps, up to order 2. -/
theorem comp_bounds {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) {x : Space n} (hx : x ∈ s)
    {f g : Space n → (Space n →L[ℝ] Space n)} (hf : ContDiffOn ℝ 2 f s)
    (hg : ContDiffOn ℝ 2 g s) {a0 a1 a2 b0 b1 b2 : ℝ}
    (hf0 : ‖iteratedFDerivWithin ℝ 0 f s x‖ ≤ a0) (hf1 : ‖iteratedFDerivWithin ℝ 1 f s x‖ ≤ a1)
    (hf2 : ‖iteratedFDerivWithin ℝ 2 f s x‖ ≤ a2)
    (hg0 : ‖iteratedFDerivWithin ℝ 0 g s x‖ ≤ b0) (hg1 : ‖iteratedFDerivWithin ℝ 1 g s x‖ ≤ b1)
    (hg2 : ‖iteratedFDerivWithin ℝ 2 g s x‖ ≤ b2) :
    ‖iteratedFDerivWithin ℝ 0 (fun y => f y ∘L g y) s x‖ ≤ a0 * b0 ∧
    ‖iteratedFDerivWithin ℝ 1 (fun y => f y ∘L g y) s x‖ ≤ a0 * b1 + a1 * b0 ∧
    ‖iteratedFDerivWithin ℝ 2 (fun y => f y ∘L g y) s x‖ ≤
      a0 * b2 + 2 * (a1 * b1) + a2 * b0 := by
  have key : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDerivWithin ℝ k (fun y => f y ∘L g y) s x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
        ‖iteratedFDerivWithin ℝ (k - i) g s x‖ := fun k hk =>
    (ContinuousLinearMap.compL ℝ (Space n) (Space n) (Space n)).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      hf hg hs hx (by exact_mod_cast hk) (ContinuousLinearMap.norm_compL_le _ _ _ _)
  have a0n : 0 ≤ a0 := (norm_nonneg _).trans hf0
  have a1n : 0 ≤ a1 := (norm_nonneg _).trans hf1
  have a2n : 0 ≤ a2 := (norm_nonneg _).trans hf2
  have k0 : ‖iteratedFDerivWithin ℝ 0 (fun y => f y ∘L g y) s x‖ ≤
      ‖iteratedFDerivWithin ℝ 0 f s x‖ * ‖iteratedFDerivWithin ℝ 0 g s x‖ := by
    have := key 0 (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
      Nat.cast_one, one_mul] at this
    exact this
  have k1 : ‖iteratedFDerivWithin ℝ 1 (fun y => f y ∘L g y) s x‖ ≤
      ‖iteratedFDerivWithin ℝ 0 f s x‖ * ‖iteratedFDerivWithin ℝ 1 g s x‖ +
      ‖iteratedFDerivWithin ℝ 1 f s x‖ * ‖iteratedFDerivWithin ℝ 0 g s x‖ := by
    have := key 1 (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
      Nat.choose_zero_right, Nat.cast_one, one_mul] at this
    exact this
  have k2 : ‖iteratedFDerivWithin ℝ 2 (fun y => f y ∘L g y) s x‖ ≤
      ‖iteratedFDerivWithin ℝ 0 f s x‖ * ‖iteratedFDerivWithin ℝ 2 g s x‖ +
      2 * ‖iteratedFDerivWithin ℝ 1 f s x‖ * ‖iteratedFDerivWithin ℝ 1 g s x‖ +
      ‖iteratedFDerivWithin ℝ 2 f s x‖ * ‖iteratedFDerivWithin ℝ 0 g s x‖ := by
    have := key 2 le_rfl
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
      Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul,
      Nat.cast_ofNat] at this
    exact this
  have p00 := mul_le_mul hf0 hg0 (norm_nonneg _) a0n
  have p01 := mul_le_mul hf0 hg1 (norm_nonneg _) a0n
  have p02 := mul_le_mul hf0 hg2 (norm_nonneg _) a0n
  have p10 := mul_le_mul hf1 hg0 (norm_nonneg _) a1n
  have p11 := mul_le_mul hf1 hg1 (norm_nonneg _) a1n
  have p20 := mul_le_mul hf2 hg0 (norm_nonneg _) a2n
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `G = ℛ E ℛ`, so that `Ã = G + I` away from `0`. -/
noncomputable def Gf (S : HalfBallSolution n) (y : Space n) : Space n →L[ℝ] Space n :=
  refl y ∘L (Ef S y ∘L refl y)

theorem contDiffOn_Gf (S : HalfBallSolution n) : ContDiffOn ℝ 2 (Gf S) (punct n) :=
  contDiffOn_refl.clm_comp ((contDiffOn_Ef S).clm_comp contDiffOn_refl)

theorem Gf_bounds (S : HalfBallSolution n) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Space n, 1 ≤ ‖y‖ →
    ‖iteratedFDerivWithin ℝ 1 (Gf S) (punct n) y‖ ≤ M * ‖y‖⁻¹ ^ 2 ∧
    ‖iteratedFDerivWithin ℝ 2 (Gf S) (punct n) y‖ ≤ M * ‖y‖⁻¹ ^ 3 := by
  obtain ⟨MR, hMR, hR⟩ := refl_bounds (n := n)
  obtain ⟨ME, hME, hE⟩ := Ef_bounds S
  refine ⟨9 * (MR + ME + 1) ^ 3, by positivity, fun y hy => ?_⟩
  set M : ℝ := MR + ME + 1 with hM_def
  have hM1 : 1 ≤ M := by linarith
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    exact absurd hy (by norm_num)
  have hyp : y ∈ punct n := hy0
  set ρ : ℝ := ‖y‖⁻¹ with hρ_def
  have hρ0 : 0 ≤ ρ := inv_nonneg.mpr (norm_nonneg _)
  obtain ⟨hR0, hR1, hR2⟩ := hR y hy0
  obtain ⟨hE0, hE1, hE2⟩ := hE y hy
  have hR1' : ‖iteratedFDerivWithin ℝ 1 refl (punct n) y‖ ≤ M * ρ :=
    hR1.trans (mul_le_mul_of_nonneg_right (by linarith) hρ0)
  have hR2' : ‖iteratedFDerivWithin ℝ 2 refl (punct n) y‖ ≤ M * ρ ^ 2 :=
    hR2.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hE0' : ‖iteratedFDerivWithin ℝ 0 (Ef S) (punct n) y‖ ≤ M * ρ :=
    hE0.trans (mul_le_mul_of_nonneg_right (by linarith) hρ0)
  have hE1' : ‖iteratedFDerivWithin ℝ 1 (Ef S) (punct n) y‖ ≤ M * ρ ^ 2 :=
    hE1.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hE2' : ‖iteratedFDerivWithin ℝ 2 (Ef S) (punct n) y‖ ≤ M * ρ ^ 3 :=
    hE2.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  -- `H = E ℛ`
  obtain ⟨hH0, hH1, hH2⟩ := comp_bounds uniqueDiffOn_punct hyp (contDiffOn_Ef S) contDiffOn_refl
    hE0' hE1' hE2' hR0 hR1' hR2'
  -- `G = ℛ H`
  obtain ⟨-, hG1, hG2⟩ := comp_bounds uniqueDiffOn_punct hyp contDiffOn_refl
    ((contDiffOn_Ef S).clm_comp contDiffOn_refl) hR0 hR1' hR2' hH0 hH1 hH2
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hMMM : M ^ 2 ≤ M ^ 3 := by nlinarith
  constructor
  · refine hG1.trans ?_
    calc 1 * (M * ρ * (M * ρ) + M * ρ ^ 2 * 1) + M * ρ * (M * ρ * 1)
        = (2 * M ^ 2 + M) * ρ ^ 2 := by ring
      _ ≤ (9 * M ^ 3) * ρ ^ 2 := by
        gcongr
        nlinarith
  · refine hG2.trans ?_
    calc 1 * (M * ρ * (M * ρ ^ 2) + 2 * (M * ρ ^ 2 * (M * ρ)) + M * ρ ^ 3 * 1) +
          2 * (M * ρ * (M * ρ * (M * ρ) + M * ρ ^ 2 * 1)) + M * ρ ^ 2 * (M * ρ * 1)
        = (2 * M ^ 3 + 6 * M ^ 2 + M) * ρ ^ 3 := by ring
      _ ≤ (9 * M ^ 3) * ρ ^ 3 := by
        gcongr
        nlinarith

/-- `Ã = ℛ E ℛ + I` away from `0` (from `tA_sub_id`). -/
theorem tA_eq_Gf (S : HalfBallSolution n) {y : Space n} (hy : y ≠ 0) :
    tA S.A y = Gf S y + ContinuousLinearMap.id ℝ (Space n) := by
  rw [Gf, Ef, ← tA_sub_id hy, sub_add_cancel]

/-- For `k = 1, 2` the `k`-th derivative of `Ã` at `y ≠ 0` has the norm of that of `ℛ E ℛ`. -/
theorem norm_iteratedFDeriv_tA (S : HalfBallSolution n) {k : ℕ} (hk : k ≠ 0) (hk2 : k ≤ 2)
    {y : Space n} (hy : y ≠ 0) :
    ‖iteratedFDeriv ℝ k (tA S.A) y‖ = ‖iteratedFDerivWithin ℝ k (Gf S) (punct n) y‖ := by
  have hy' : y ∈ punct n := hy
  rw [← iteratedFDerivWithin_of_isOpen k isOpen_punct hy',
    iteratedFDerivWithin_congr (f := Gf S + fun _ => ContinuousLinearMap.id ℝ (Space n))
      (fun z hz => tA_eq_Gf S hz) hy' k,
    iteratedFDerivWithin_add_apply ((contDiffOn_Gf S y hy').of_le (by exact_mod_cast hk2))
      contDiffWithinAt_const uniqueDiffOn_punct hy',
    iteratedFDerivWithin_const_of_ne hk, Pi.zero_apply, add_zero]

end W_PL_tA

/-- The derivative bounds `|∇Ã| ≤ K/|y|²`, `|∇²Ã| ≤ K/|y|³` of Lemma inversion. Write
`Ã - I = ℛ E ℛ` with `E = A ∘ Φ - I` (`tA_sub_id`; this uses `ℛ ∘ ℛ = I`) and apply Leibniz:
every term is small because `|ℛ| ≤ 1`, `|E| ≤ K/|y|` (see `coeff_bounds`),
`|DE| ≤ K |DΦ| ≤ K/|y|²`, `|D²E| ≤ K(|DΦ|² + |D²Φ|) ≤ CK/|y|³`, `|Dℛ| ≤ C/|y|`,
`|D²ℛ| ≤ C/|y|²` (`ℛ` is homogeneous of degree `0`, `Φ` of degree `-1`). -/
theorem tA_deriv_bounds (S : HalfBallSolution n) : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ y : Space n, 1 ≤ ‖y‖ →
    ‖fderiv ℝ (tA S.A) y‖ ≤ K₁ / ‖y‖ ^ 2 ∧ ‖iteratedFDeriv ℝ 2 (tA S.A) y‖ ≤ K₁ / ‖y‖ ^ 3 := by
  obtain ⟨M, hM0, hM⟩ := W_PL_tA.Gf_bounds S
  refine ⟨M, hM0, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    exact absurd hy (by norm_num)
  obtain ⟨h1, h2⟩ := hM y hy
  constructor
  · rw [← norm_iteratedFDeriv_one, W_PL_tA.norm_iteratedFDeriv_tA S one_ne_zero (by norm_num) hy0,
      div_eq_mul_inv, ← inv_pow]
    exact h1
  · rw [W_PL_tA.norm_iteratedFDeriv_tA S two_ne_zero le_rfl hy0, div_eq_mul_inv, ← inv_pow]
    exact h2

/-- Regularity and size bounds of the transformed coefficients on `{‖y‖ ≥ 1}` (Lemma inversion). -/
theorem coeff_bounds (S : HalfBallSolution n) : ∃ K' : ℝ, 0 ≤ K' ∧ ∀ y : Space n, 1 ≤ ‖y‖ →
    ‖tA S.A y - ContinuousLinearMap.id ℝ (Space n)‖ ≤ K' / ‖y‖ ∧
    ‖fderiv ℝ (tA S.A) y‖ ≤ K' / ‖y‖ ^ 2 ∧
    ‖iteratedFDeriv ℝ 2 (tA S.A) y‖ ≤ K' / ‖y‖ ^ 3 ∧
    ‖tB S.A S.B y‖ ≤ K' / ‖y‖ ∧
    |tC S.C y| ≤ K' / ‖y‖ ^ 2 := by
  obtain ⟨K₁, hK₁, hd⟩ := tA_deriv_bounds S
  set K := S.K with hKdef
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (S.coeffs.bound_A 0)
  set c : ℝ := |4 - 2 * ((n : ℝ) + 1)| with hc
  have hc0 : 0 ≤ c := abs_nonneg _
  refine ⟨(c + 1) * K + K + K₁, by positivity, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hAd : ∀ x, DifferentiableAt ℝ S.A x := fun x =>
    (S.coeffs.contDiff_A.differentiable (by norm_num)) x
  -- `|A(Φ y) - I| ≤ K / |y|`
  have hAI : ‖S.A (invMap y) - ContinuousLinearMap.id ℝ (Space n)‖ ≤ K / ‖y‖ := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hAd x)
      (fun x _ => S.coeffs.bound_dA x) convex_univ (Set.mem_univ (0 : Space n))
      (Set.mem_univ (invMap y))
    rw [S.A_zero, sub_zero, norm_invMap] at h
    rwa [div_eq_mul_inv]
  have hKy : K / ‖y‖ ≤ ((c + 1) * K + K + K₁) / ‖y‖ := by
    apply div_le_div_of_nonneg_right _ hyp.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [tA_sub_id hy0]
    calc ‖refl y ∘L (S.A (invMap y) - ContinuousLinearMap.id ℝ (Space n)) ∘L refl y‖
        ≤ ‖refl y‖ * (‖S.A (invMap y) - ContinuousLinearMap.id ℝ (Space n)‖ * ‖refl y‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (K / ‖y‖ * 1) := by
          gcongr
          · exact norm_refl_le hy0
          · exact norm_refl_le hy0
      _ = K / ‖y‖ := by ring
      _ ≤ _ := hKy
  · refine (hd y hy).1.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  · refine (hd y hy).2.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  · have h1 : ‖tA S.A y y‖ ≤ K * ‖y‖ :=
      ((tA S.A y).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right ((norm_tA_le hy0 S.A).trans (S.coeffs.bound_A _))
          (norm_nonneg _))
    have h2 : ‖refl y (S.B (invMap y))‖ ≤ K := by
      rw [norm_refl_apply hy0]; exact S.coeffs.bound_B _
    have hy2 : (‖y‖ ^ 2)⁻¹ ≤ ‖y‖⁻¹ := by
      rw [inv_le_inv₀ (by positivity) hyp]; nlinarith
    unfold tB
    calc ‖((4 - 2 * ((n : ℝ) + 1)) * (‖y‖ ^ 2)⁻¹) • tA S.A y y
          + (‖y‖ ^ 2)⁻¹ • refl y (S.B (invMap y))‖
        ≤ ‖((4 - 2 * ((n : ℝ) + 1)) * (‖y‖ ^ 2)⁻¹) • tA S.A y y‖
          + ‖(‖y‖ ^ 2)⁻¹ • refl y (S.B (invMap y))‖ := norm_add_le _ _
      _ = c * (‖y‖ ^ 2)⁻¹ * ‖tA S.A y y‖ + (‖y‖ ^ 2)⁻¹ * ‖refl y (S.B (invMap y))‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
            abs_of_pos (by positivity : (0 : ℝ) < (‖y‖ ^ 2)⁻¹)]
      _ ≤ c * (‖y‖ ^ 2)⁻¹ * (K * ‖y‖) + ‖y‖⁻¹ * K := by
          gcongr
      _ = (c * K + K) / ‖y‖ := by field_simp
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hyp.le
          nlinarith
  · unfold tC
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (‖y‖ ^ 4)⁻¹)]
    have h1 : |S.C (invMap y)| ≤ K := S.coeffs.bound_C _
    have hy4 : (‖y‖ ^ 4)⁻¹ ≤ (‖y‖ ^ 2)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have h2 : 1 ≤ ‖y‖ ^ 2 := one_le_pow₀ hy
      nlinarith [mul_nonneg (sq_nonneg ‖y‖) (sub_nonneg.mpr h2)]
    calc (‖y‖ ^ 4)⁻¹ * |S.C (invMap y)| ≤ (‖y‖ ^ 2)⁻¹ * K :=
          mul_le_mul hy4 h1 (abs_nonneg _) (by positivity)
      _ = K / ‖y‖ ^ 2 := by rw [div_eq_inv_mul]
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith

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

namespace W_PL_carleman

/-! ### Helpers for `carleman_P0` (Proposition carleman of the note)

Notation: `e = ed n`, `s = vcoord y`, `φ = phi C₀ = gw C₀ ∘ vcoord`; `g1, g2, g3` are the first
three derivatives of `gw C₀`. We use the identities of package F2 with the trivial density
`μ = 1`, `B = A`, and the conjugate `w = e^{τφ} v` (`wc`). -/

/-- `g'(s) = 1 - C₀/s`. -/
noncomputable def g1 (C₀ s : ℝ) : ℝ := 1 - C₀ / s

/-- `g''(s) = C₀/s²`. -/
noncomputable def g2 (C₀ s : ℝ) : ℝ := C₀ / s ^ 2

/-- `g'''(s) = -2C₀/s³`. -/
noncomputable def g3 (C₀ s : ℝ) : ℝ := -(2 * C₀) / s ^ 3

/-- The weight `φ(y) = g(y_d)`. -/
noncomputable def phi (C₀ : ℝ) (y : Space n) : ℝ := gw C₀ (vcoord y)

/-- The dimension `d = n + 1` (it bounds the trace: `|tr L| ≤ d ‖L‖`). -/
noncomputable def trN (n : ℕ) : ℝ := (n : ℝ) + 1

theorem trN_nonneg : 0 ≤ trN n := by
  unfold trN
  positivity

/-- The constant `C♯ = 8K + 2‖tr‖ + 2` of the proof. -/
noncomputable def Csh (n : ℕ) (K : ℝ) : ℝ := 8 * K + 2 * trN n + 2

/-- The conjugate `w = e^{τφ} v`. -/
noncomputable def wc (C₀ τ : ℝ) (v : Space n → ℝ) (z : Space n) : ℝ :=
  Real.exp (τ * phi C₀ z) * v z

/-- The field `s⁻² w A ∇w` of Lemma 2.1(3) with `ϱ = s⁻²` and `μ = 1` (the factor `1` is kept so
that the field is syntactically the one of `F2.carleman_gradient_pointwise`). -/
noncomputable def Gf (A : Space n → Space n →L[ℝ] Space n) (w : Space n → ℝ) (z : Space n) :
    Space n :=
  (1 * (vcoord z ^ 2)⁻¹ * w z) • A z (gradient w z)

/-! #### One-variable calculus for the weight -/

theorem hasDerivAt_gw (C₀ : ℝ) {s : ℝ} (hs : 0 < s) : HasDerivAt (gw C₀) (g1 C₀ s) s := by
  have h : HasDerivAt (gw C₀) (1 - C₀ * s⁻¹) s :=
    (hasDerivAt_id' s).sub ((Real.hasDerivAt_log hs.ne').const_mul C₀)
  refine h.congr_deriv ?_
  simp only [g1, div_eq_mul_inv]

theorem hasDerivAt_g1 (C₀ : ℝ) {s : ℝ} (hs : 0 < s) : HasDerivAt (g1 C₀) (g2 C₀ s) s := by
  have h := (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_inv hs.ne').const_mul C₀)
  have e : g1 C₀ = (fun _ => (1 : ℝ)) - fun y => C₀ * y⁻¹ := by
    funext x
    simp [g1, div_eq_mul_inv]
  rw [e]
  refine h.congr_deriv ?_
  simp only [g2]
  field_simp
  ring

theorem hasDerivAt_g2 (C₀ : ℝ) {s : ℝ} (hs : 0 < s) : HasDerivAt (g2 C₀) (g3 C₀ s) s := by
  have h := ((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs.ne')).const_mul C₀
  have e : g2 C₀ = fun y => C₀ * (fun x => x ^ 2)⁻¹ y := by
    funext x
    simp [g2, div_eq_mul_inv]
  rw [e]
  refine h.congr_deriv ?_
  simp only [g3]
  field_simp
  ring

/-! #### The vertical coordinate and the weight -/

theorem vcoord_eq_inner (z : Space n) : vcoord z = ⟪ed n, z⟫_ℝ := by
  rw [real_inner_comm, F1.inner_ed]
  rfl

theorem hasFDerivAt_vcoord (y : Space n) :
    HasFDerivAt (vcoord : Space n → ℝ) (innerSL ℝ (ed n)) y := by
  have h : (vcoord : Space n → ℝ) = fun z => innerSL ℝ (ed n) z := by
    funext z
    rw [innerSL_apply_apply, vcoord_eq_inner]
  rw [h]
  exact (innerSL ℝ (ed n)).hasFDerivAt

theorem hasFDerivAt_comp_vcoord {f : ℝ → ℝ} {f' : ℝ} {y : Space n}
    (hf : HasDerivAt f f' (vcoord y)) :
    HasFDerivAt (fun z => f (vcoord z)) (f' • innerSL ℝ (ed n)) y :=
  hf.comp_hasFDerivAt y (hasFDerivAt_vcoord y)

theorem hasFDerivAt_phi (C₀ : ℝ) {y : Space n} (hy : 0 < vcoord y) :
    HasFDerivAt (phi C₀) (g1 C₀ (vcoord y) • innerSL ℝ (ed n)) y :=
  hasFDerivAt_comp_vcoord (hasDerivAt_gw C₀ hy)

theorem gradient_phi (C₀ : ℝ) {y : Space n} (hy : 0 < vcoord y) :
    gradient (phi C₀) y = g1 C₀ (vcoord y) • ed n := by
  refine ext_inner_right ℝ fun ξ => ?_
  rw [inner_gradient_left, (hasFDerivAt_phi C₀ hy).fderiv, real_inner_smul_left,
    smul_apply, innerSL_apply_apply, smul_eq_mul]

theorem contDiff_vcoord_any {k : WithTop ℕ∞} : ContDiff ℝ k (vcoord : Space n → ℝ) := by
  rw [F1.vcoord_eq_proj]
  exact (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).contDiff

theorem contDiffAt_phi (C₀ : ℝ) {y : Space n} (hy : 0 < vcoord y) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (phi C₀) y := by
  have hv : ContDiffAt ℝ k (vcoord : Space n → ℝ) y := contDiff_vcoord_any.contDiffAt
  have hl : ContDiffAt ℝ k (fun z : Space n => Real.log (vcoord z)) y :=
    (Real.contDiffAt_log.mpr hy.ne').comp y hv
  exact hv.sub (contDiffAt_const.mul hl)

theorem contDiffAt_invsq {y : Space n} (hy : 0 < vcoord y) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (fun z : Space n => (vcoord z ^ 2)⁻¹) y :=
  (contDiff_vcoord_any.contDiffAt.pow 2).inv (pow_ne_zero 2 hy.ne')

theorem contDiffAt_wc (C₀ τ : ℝ) {v : Space n → ℝ} (hv : ContDiff ℝ 2 v) {y : Space n}
    (hy : 0 < vcoord y) : ContDiffAt ℝ 2 (wc C₀ τ v) y :=
  ((contDiffAt_const.mul (contDiffAt_phi C₀ hy)).exp).mul hv.contDiffAt

/-! #### Pointwise hypotheses -/

/-- The hypotheses at a point `y` used by the pointwise estimates. -/
structure PtHyp (A : Space n → Space n →L[ℝ] Space n) (K C₀ : ℝ) (y : Space n) : Prop where
  hK : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hs1 : 1 ≤ vcoord y
  hsC : 4 * C₀ ≤ vcoord y
  hsK : 4 * K ≤ vcoord y
  cd : ContDiffAt ℝ 2 A y
  symm : ∀ ξ η : Space n, ⟪A y ξ, η⟫_ℝ = ⟪ξ, A y η⟫_ℝ
  bA : ‖A y - ContinuousLinearMap.id ℝ (Space n)‖ ≤ K / vcoord y
  bdA : ‖fderiv ℝ A y‖ ≤ K / vcoord y ^ 2
  bd2A : ‖iteratedFDeriv ℝ 2 A y‖ ≤ K / vcoord y ^ 3

namespace PtHyp

variable {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}

theorem spos (h : PtHyp A K C₀ y) : 0 < vcoord y := lt_of_lt_of_le one_pos h.hs1

theorem g1_ge (h : PtHyp A K C₀ y) : 3 / 4 ≤ g1 C₀ (vcoord y) := by
  have hs := h.spos
  have : C₀ / vcoord y ≤ 1 / 4 := by
    rw [div_le_iff₀ hs]
    linarith [h.hsC]
  unfold g1
  linarith

theorem g1_le (h : PtHyp A K C₀ y) : g1 C₀ (vcoord y) ≤ 1 := by
  have := div_nonneg h.hC₀ h.spos.le
  unfold g1
  linarith

theorem g2_nonneg (h : PtHyp A K C₀ y) : 0 ≤ g2 C₀ (vcoord y) :=
  div_nonneg h.hC₀ (by have := h.spos; positivity)

theorem bA' (h : PtHyp A K C₀ y) : ‖A y - ContinuousLinearMap.id ℝ (Space n)‖ ≤ 1 / 4 := by
  refine h.bA.trans ?_
  rw [div_le_iff₀ h.spos]
  linarith [h.hsK]

theorem normA (h : PtHyp A K C₀ y) : ‖A y‖ ≤ 5 / 4 := by
  have h1 : ‖A y‖ ≤ ‖A y - ContinuousLinearMap.id ℝ (Space n)‖
      + ‖ContinuousLinearMap.id ℝ (Space n)‖ := by
    have := norm_add_le (A y - ContinuousLinearMap.id ℝ (Space n))
      (ContinuousLinearMap.id ℝ (Space n))
    rwa [sub_add_cancel] at this
  have h2 : ‖ContinuousLinearMap.id ℝ (Space n)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith [h.bA']

theorem normAv (h : PtHyp A K C₀ y) (ξ : Space n) : ‖A y ξ‖ ≤ 5 / 4 * ‖ξ‖ :=
  ((A y).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right h.normA (norm_nonneg _))

theorem coer (h : PtHyp A K C₀ y) (ξ : Space n) : 3 / 4 * ‖ξ‖ ^ 2 ≤ ⟪A y ξ, ξ⟫_ℝ := by
  have e : ⟪A y ξ, ξ⟫_ℝ = ‖ξ‖ ^ 2 + ⟪(A y - ContinuousLinearMap.id ℝ (Space n)) ξ, ξ⟫_ℝ := by
    rw [sub_apply, inner_sub_left, ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    ring
  have h1 : |⟪(A y - ContinuousLinearMap.id ℝ (Space n)) ξ, ξ⟫_ℝ| ≤ 1 / 4 * ‖ξ‖ ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := ((A y - ContinuousLinearMap.id ℝ (Space n)).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right h.bA' (norm_nonneg ξ))
    nlinarith [norm_nonneg ξ]
  rw [e]
  linarith [(abs_le.mp h1).1]

theorem Add_ge (h : PtHyp A K C₀ y) : 3 / 4 ≤ ⟪ed n, A y (ed n)⟫_ℝ := by
  have := h.coer (ed n)
  rw [norm_ed, real_inner_comm] at this
  linarith

theorem Add_le (h : PtHyp A K C₀ y) : ⟪ed n, A y (ed n)⟫_ℝ ≤ 5 / 4 := by
  have h1 := (real_inner_le_norm (ed n) (A y (ed n))).trans
    (mul_le_mul_of_nonneg_left (h.normAv (ed n)) (norm_nonneg _))
  rw [norm_ed] at h1
  linarith

theorem bd2A' (h : PtHyp A K C₀ y) (u : Space n) :
    ‖fderiv ℝ (fderiv ℝ A) y u‖ ≤ K / vcoord y ^ 3 * ‖u‖ := by
  have hs := h.spos
  have hK := h.hK
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have e := iteratedFDeriv_two_apply (𝕜 := ℝ) A y ![u, v]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
  rw [← e]
  refine ((iteratedFDeriv ℝ 2 A y).le_opNorm ![u, v]).trans ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc ‖iteratedFDeriv ℝ 2 A y‖ * (‖u‖ * ‖v‖) ≤ K / vcoord y ^ 3 * (‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right h.bd2A (by positivity)
    _ = K / vcoord y ^ 3 * ‖u‖ * ‖v‖ := by ring

theorem diffA (h : PtHyp A K C₀ y) : DifferentiableAt ℝ A y :=
  h.cd.differentiableAt (by norm_num)

theorem diffDA (h : PtHyp A K C₀ y) : DifferentiableAt ℝ (fderiv ℝ A) y :=
  (h.cd.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

end PtHyp

/-! #### `V = A ∇φ`, `q = ⟪A∇φ, ∇φ⟫` and their derivatives -/

theorem carlV_phi (A : Space n → Space n →L[ℝ] Space n) (C₀ : ℝ) {z : Space n}
    (hz : 0 < vcoord z) : carlV A (phi C₀) z = g1 C₀ (vcoord z) • A z (ed n) := by
  rw [carlV, gradient_phi C₀ hz, map_smul]

theorem carlV_phi_ev (A : Space n → Space n →L[ℝ] Space n) (C₀ : ℝ) {y : Space n}
    (hy : 0 < vcoord y) :
    carlV A (phi C₀) =ᶠ[𝓝 y] fun z => g1 C₀ (vcoord z) • A z (ed n) := by
  filter_upwards [(isOpen_H (n := n) 0).mem_nhds hy] with z hz
  exact carlV_phi A C₀ hz

theorem carlQ_phi (A : Space n → Space n →L[ℝ] Space n) (C₀ : ℝ) {z : Space n}
    (hz : 0 < vcoord z) :
    carlQ A (phi C₀) z = g1 C₀ (vcoord z) ^ 2 * ⟪ed n, A z (ed n)⟫_ℝ := by
  rw [carlQ, gradient_phi C₀ hz, map_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm]
  ring

theorem carlQ_phi_ev (A : Space n → Space n →L[ℝ] Space n) (C₀ : ℝ) {y : Space n}
    (hy : 0 < vcoord y) :
    carlQ A (phi C₀) =ᶠ[𝓝 y] fun z => g1 C₀ (vcoord z) ^ 2 * ⟪ed n, A z (ed n)⟫_ℝ := by
  filter_upwards [(isOpen_H (n := n) 0).mem_nhds hy] with z hz
  exact carlQ_phi A C₀ hz

theorem hasFDerivAt_apply_const {A : Space n → Space n →L[ℝ] Space n} {y : Space n}
    (hA : DifferentiableAt ℝ A y) (e : Space n) :
    HasFDerivAt (fun z => A z e) ((fderiv ℝ A y).flip e) y := by
  have := hA.hasFDerivAt.clm_apply (hasFDerivAt_const e y)
  simpa using this

theorem fderiv_carlV_apply {A : Space n → Space n →L[ℝ] Space n} (C₀ : ℝ) {y : Space n}
    (hy : 0 < vcoord y) (hA : DifferentiableAt ℝ A y) (u : Space n) :
    fderiv ℝ (carlV A (phi C₀)) y u
      = g1 C₀ (vcoord y) • fderiv ℝ A y u (ed n)
        + (g2 C₀ (vcoord y) * ⟪ed n, u⟫_ℝ) • A y (ed n) := by
  have hh := hasFDerivAt_comp_vcoord (hasDerivAt_g1 C₀ hy)
  have hV : HasFDerivAt (fun z => g1 C₀ (vcoord z) • A z (ed n)) _ y :=
    hh.smul (hasFDerivAt_apply_const hA (ed n))
  rw [(carlV_phi_ev A C₀ hy).fderiv_eq, hV.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_eq_mul]

theorem fderiv_carlQ_apply {A : Space n → Space n →L[ℝ] Space n} (C₀ : ℝ) {y : Space n}
    (hy : 0 < vcoord y) (hA : DifferentiableAt ℝ A y) (u : Space n) :
    fderiv ℝ (carlQ A (phi C₀)) y u
      = 2 * g1 C₀ (vcoord y) * (g2 C₀ (vcoord y) * ⟪ed n, u⟫_ℝ) * ⟪ed n, A y (ed n)⟫_ℝ
        + g1 C₀ (vcoord y) ^ 2 * ⟪ed n, fderiv ℝ A y u (ed n)⟫_ℝ := by
  have hh := hasFDerivAt_comp_vcoord (hasDerivAt_g1 C₀ hy)
  have hI : HasFDerivAt (fun z => ⟪ed n, A z (ed n)⟫_ℝ)
      ((innerSL ℝ (ed n)).comp ((fderiv ℝ A y).flip (ed n))) y :=
    (innerSL ℝ (ed n)).hasFDerivAt.comp y (hasFDerivAt_apply_const hA (ed n))
  have hq : HasFDerivAt (fun z => g1 C₀ (vcoord z) ^ 2 * ⟪ed n, A z (ed n)⟫_ℝ) _ y :=
    (hh.pow 2).mul hI
  rw [(carlQ_phi_ev A C₀ hy).fderiv_eq, hq.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem norm_dA_apply_le {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) (u v : Space n) :
    ‖fderiv ℝ A y u v‖ ≤ K * (vcoord y ^ 2)⁻¹ * ‖u‖ * ‖v‖ := by
  calc ‖fderiv ℝ A y u v‖ ≤ ‖fderiv ℝ A y u‖ * ‖v‖ := (fderiv ℝ A y u).le_opNorm v
    _ ≤ ‖fderiv ℝ A y‖ * ‖u‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ A y).le_opNorm u) (norm_nonneg _)
    _ ≤ K * (vcoord y ^ 2)⁻¹ * ‖u‖ * ‖v‖ := by
        gcongr
        rw [← div_eq_mul_inv]
        exact h.bdA

/-- The trace in the standard basis `b i = EuclideanSpace.single i 1`. -/
theorem trace_eq_sum (L : Space n →L[ℝ] Space n) :
    F2.traceCLM L = ∑ i, ⟪(EuclideanSpace.single i (1 : ℝ) : Space n),
      L (EuclideanSpace.single i (1 : ℝ))⟫_ℝ := by
  rw [F2.traceCLM_apply, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
  simp [EuclideanSpace.basisFun_apply]

/-- `tr(DA(x)(·) e) = Σᵢ ⟪bᵢ, DA(x) bᵢ e⟫`. -/
noncomputable def trDA (A : Space n → Space n →L[ℝ] Space n) (x : Space n) : ℝ :=
  ∑ i, ⟪(EuclideanSpace.single i (1 : ℝ) : Space n),
    fderiv ℝ A x (EuclideanSpace.single i (1 : ℝ)) (ed n)⟫_ℝ

theorem abs_sum_single_le (f : Space n →L[ℝ] Space n →L[ℝ] Space n) :
    |∑ i, ⟪(EuclideanSpace.single i (1 : ℝ) : Space n),
      f (EuclideanSpace.single i (1 : ℝ)) (ed n)⟫_ℝ| ≤ trN n * ‖f‖ := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ i : Fin (n + 1), ‖(EuclideanSpace.single i (1 : ℝ) : Space n)‖ = 1 := fun i => by
    simp
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
      |⟪(EuclideanSpace.single i (1 : ℝ) : Space n),
        f (EuclideanSpace.single i (1 : ℝ)) (ed n)⟫_ℝ| ≤ ‖f‖ := by
    intro i _
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hb, one_mul]
    calc ‖f (EuclideanSpace.single i (1 : ℝ)) (ed n)‖
        ≤ ‖f (EuclideanSpace.single i (1 : ℝ))‖ * ‖ed n‖ := (f _).le_opNorm _
      _ ≤ ‖f‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Space n)‖ * ‖ed n‖ :=
          mul_le_mul_of_nonneg_right (f.le_opNorm _) (norm_nonneg _)
      _ = ‖f‖ := by rw [hb, norm_ed, mul_one, mul_one]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, trN]
  push_cast
  rfl

/-- `div V = g'(s) tr(DA(·) e) + g''(s) ⟪e, A e⟫`. -/
theorem divV_eq {A : Space n → Space n →L[ℝ] Space n} (C₀ : ℝ) {x : Space n}
    (hx : 0 < vcoord x) (hA : DifferentiableAt ℝ A x) :
    divergence (carlV A (phi C₀)) x
      = g1 C₀ (vcoord x) * trDA A x + g2 C₀ (vcoord x) * ⟪ed n, A x (ed n)⟫_ℝ := by
  have hh := hasFDerivAt_comp_vcoord (hasDerivAt_g1 C₀ hx)
  have hV : HasFDerivAt (fun z => g1 C₀ (vcoord z) • A z (ed n)) _ x :=
    hh.smul (hasFDerivAt_apply_const hA (ed n))
  rw [F2.divergence_eq_traceCLM, (carlV_phi_ev A C₀ hx).fderiv_eq, hV.fderiv, map_add, map_smul,
    traceCLM_smulRight, smul_eq_mul, smul_apply,
    innerSL_apply_apply, smul_eq_mul, trace_eq_sum, trDA]
  simp only [ContinuousLinearMap.flip_apply]

theorem hasFDerivAt_trDA {A : Space n → Space n →L[ℝ] Space n} {y : Space n}
    (hDA : DifferentiableAt ℝ (fderiv ℝ A) y) :
    HasFDerivAt (trDA A) (∑ i, (innerSL ℝ (EuclideanSpace.single i (1 : ℝ) : Space n)).comp
      (((fderiv ℝ (fderiv ℝ A) y).flip (EuclideanSpace.single i (1 : ℝ))).flip (ed n))) y := by
  have key : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
      HasFDerivAt (fun x => ⟪(EuclideanSpace.single i (1 : ℝ) : Space n),
        fderiv ℝ A x (EuclideanSpace.single i (1 : ℝ)) (ed n)⟫_ℝ)
      ((innerSL ℝ (EuclideanSpace.single i (1 : ℝ) : Space n)).comp
      (((fderiv ℝ (fderiv ℝ A) y).flip (EuclideanSpace.single i (1 : ℝ))).flip (ed n))) y := by
    intro i _
    have hc1 : HasFDerivAt (fun x => fderiv ℝ A x (EuclideanSpace.single i (1 : ℝ)))
        ((fderiv ℝ (fderiv ℝ A) y).flip (EuclideanSpace.single i (1 : ℝ))) y := by
      have := hDA.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) y)
      simpa using this
    have hc2 : HasFDerivAt (fun x => fderiv ℝ A x (EuclideanSpace.single i (1 : ℝ)) (ed n))
        (((fderiv ℝ (fderiv ℝ A) y).flip (EuclideanSpace.single i (1 : ℝ))).flip (ed n)) y := by
      have := hc1.clm_apply (hasFDerivAt_const (ed n) y)
      simpa using this
    exact (innerSL ℝ (EuclideanSpace.single i (1 : ℝ) : Space n)).hasFDerivAt.comp y hc2
  have := HasFDerivAt.sum key
  convert this using 1
  funext x
  simp [trDA]

/-- Pure algebra for `norm_gradient_divV_le`. -/
theorem alg_divV {a t2 t1 r q eu W κ c0 T U C₀ K : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht2 : |t2| ≤ T * (κ * W * U)) (ht1 : |t1| ≤ T * (K * W)) (hr : |r| ≤ K * W * U)
    (hq : |q| ≤ 5 / 4) (heu : |eu| ≤ U) (hKC : K * W * (C₀ * W) = κ * c0 * W)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 4) (hc00 : 0 ≤ c0) (hc01 : c0 ≤ 1 / 4) (hW0 : 0 < W)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hC : 0 ≤ C₀) (hK : 0 ≤ K) :
    |a * t2 + t1 * (C₀ * W * eu) + (C₀ * W * r + q * (-(2 * c0 * W) * eu))|
      ≤ (T + 1) * W * U := by
  have hCW : 0 ≤ C₀ * W := by positivity
  have b1 : |a * t2| ≤ T * (κ * W * U) := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc a * |t2| ≤ 1 * |t2| := mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
      _ ≤ T * (κ * W * U) := by rw [one_mul]; exact ht2
  have b2 : |t1 * (C₀ * W * eu)| ≤ T * (κ * c0 * W) * U := by
    rw [abs_mul, abs_mul, abs_of_nonneg hCW]
    calc |t1| * (C₀ * W * |eu|) ≤ T * (K * W) * (C₀ * W * U) := by gcongr
      _ = T * (K * W * (C₀ * W)) * U := by ring
      _ = T * (κ * c0 * W) * U := by rw [hKC]
  have b3 : |C₀ * W * r| ≤ κ * c0 * W * U := by
    rw [abs_mul, abs_of_nonneg hCW]
    calc C₀ * W * |r| ≤ C₀ * W * (K * W * U) := by gcongr
      _ = K * W * (C₀ * W) * U := by ring
      _ = κ * c0 * W * U := by rw [hKC]
  have b4 : |q * (-(2 * c0 * W) * eu)| ≤ 5 / 2 * c0 * W * U := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c0 * W)]
    calc |q| * (2 * c0 * W * |eu|) ≤ 5 / 4 * (2 * c0 * W * U) := by gcongr
      _ = 5 / 2 * c0 * W * U := by ring
  have htri : |a * t2 + t1 * (C₀ * W * eu) + (C₀ * W * r + q * (-(2 * c0 * W) * eu))|
      ≤ |a * t2| + |t1 * (C₀ * W * eu)| + (|C₀ * W * r| + |q * (-(2 * c0 * W) * eu)|) := by
    calc _ ≤ |a * t2 + t1 * (C₀ * W * eu)| + |C₀ * W * r + q * (-(2 * c0 * W) * eu)| :=
          abs_add_le _ _
      _ ≤ _ := add_le_add (abs_add_le _ _) (abs_add_le _ _)
  have hκc : κ * c0 ≤ 1 / 16 := by nlinarith
  have hWU : 0 ≤ W * U := by positivity
  have f1 : T * (κ * W * U) ≤ T * (1 / 4 * (W * U)) := by
    have : κ * W * U ≤ 1 / 4 * (W * U) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hκ1 hWU
    exact mul_le_mul_of_nonneg_left this hT
  have f2 : T * (κ * c0 * W) * U ≤ T * (1 / 16 * (W * U)) := by
    have : κ * c0 * W * U ≤ 1 / 16 * (W * U) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hκc hWU
    calc T * (κ * c0 * W) * U = T * (κ * c0 * W * U) := by ring
      _ ≤ T * (1 / 16 * (W * U)) := mul_le_mul_of_nonneg_left this hT
  have f3 : κ * c0 * W * U ≤ 1 / 16 * (W * U) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hκc hWU
  have f4 : 5 / 2 * c0 * W * U ≤ 5 / 8 * (W * U) := by
    have : 5 / 2 * c0 ≤ 5 / 8 := by linarith
    calc 5 / 2 * c0 * W * U = 5 / 2 * c0 * (W * U) := by ring
      _ ≤ 5 / 8 * (W * U) := mul_le_mul_of_nonneg_right this hWU
  have hTWU : 0 ≤ T * (W * U) := by positivity
  have hfin : (T + 1) * W * U = T * (W * U) + W * U := by ring
  rw [hfin]
  linarith

/-- **The bound `|∇ div V| ≤ (d + 1) / s²`** (uses `|D²A| ≤ K/s³` and `g3 = -2C₀/s³`). -/
theorem norm_gradient_divV_le {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) :
    ‖gradient (divMu (fun _ => (1 : ℝ)) (carlV A (phi C₀))) y‖
      ≤ (trN n + 1) / vcoord y ^ 2 := by
  have hs := h.spos
  have hT := trN_nonneg (n := n)
  have hK := h.hK
  have hC := h.hC₀
  have hfun : divMu (fun _ => (1 : ℝ)) (carlV A (phi C₀))
      = fun x => divergence (carlV A (phi C₀)) x := by
    funext x
    exact F2.divMu_one _ x
  rw [hfun]
  have hnorm : ‖gradient (fun x => divergence (carlV A (phi C₀)) x) y‖
      = ‖fderiv ℝ (fun x => divergence (carlV A (phi C₀)) x) y‖ := by
    simp [gradient]
  rw [hnorm]
  have hev : (fun x => divergence (carlV A (phi C₀)) x) =ᶠ[𝓝 y]
      fun x => g1 C₀ (vcoord x) * trDA A x + g2 C₀ (vcoord x) * ⟪ed n, A x (ed n)⟫_ℝ := by
    filter_upwards [(isOpen_H (n := n) 0).mem_nhds hs, h.cd.eventually (by simp)] with x hx hAx
    exact divV_eq C₀ hx (hAx.differentiableAt (by norm_num))
  have h1 := hasFDerivAt_comp_vcoord (hasDerivAt_g1 C₀ hs)
  have h2 := hasFDerivAt_comp_vcoord (hasDerivAt_g2 C₀ hs)
  have hτA := hasFDerivAt_trDA h.diffDA
  have hq0 : HasFDerivAt (fun x => ⟪ed n, A x (ed n)⟫_ℝ)
      ((innerSL ℝ (ed n)).comp ((fderiv ℝ A y).flip (ed n))) y :=
    (innerSL ℝ (ed n)).hasFDerivAt.comp y (hasFDerivAt_apply_const h.diffA (ed n))
  have hD : HasFDerivAt (fun x => g1 C₀ (vcoord x) * trDA A x
      + g2 C₀ (vcoord x) * ⟪ed n, A x (ed n)⟫_ℝ) _ y := (h1.mul hτA).add (h2.mul hq0)
  rw [hev.fderiv_eq, hD.fderiv]
  set W := (vcoord y ^ 2)⁻¹ with hW
  have hW0 : 0 < W := by positivity
  have hdivW : (trN n + 1) / vcoord y ^ 2 = (trN n + 1) * W := by rw [hW, div_eq_mul_inv]
  rw [hdivW]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply,
    smul_eq_mul, Real.norm_eq_abs, FunLike.coe_sum, Finset.sum_apply]
  -- the elementary bounds
  have hκ0 : 0 ≤ K * (vcoord y)⁻¹ := by positivity
  have hc00 : 0 ≤ C₀ * (vcoord y)⁻¹ := by positivity
  have hκ1 : K * (vcoord y)⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hs]
    linarith [h.hsK]
  have hc01 : C₀ * (vcoord y)⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hs]
    linarith [h.hsC]
  have hK3 : K / vcoord y ^ 3 = K * (vcoord y)⁻¹ * W := by rw [hW]; field_simp
  have hg2 : g2 C₀ (vcoord y) = C₀ * W := by rw [g2, hW, div_eq_mul_inv]
  have hg3 : g3 C₀ (vcoord y) = -(2 * (C₀ * (vcoord y)⁻¹) * W) := by rw [g3, hW]; field_simp
  have hKC : K * W * (C₀ * W) = K * (vcoord y)⁻¹ * (C₀ * (vcoord y)⁻¹) * W := by
    rw [hW]; field_simp
  have heu : |⟪ed n, u⟫_ℝ| ≤ ‖u‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_ed, one_mul]
  have ha0 : 0 ≤ g1 C₀ (vcoord y) := by linarith [h.g1_ge]
  have hq : |⟪ed n, A y (ed n)⟫_ℝ| ≤ 5 / 4 := by
    rw [abs_le]; constructor <;> linarith [h.Add_ge, h.Add_le]
  have ht2 := (abs_sum_single_le (fderiv ℝ (fderiv ℝ A) y u)).trans
    (mul_le_mul_of_nonneg_left (h.bd2A' u) hT)
  rw [hK3] at ht2
  have ht1 := (abs_sum_single_le (fderiv ℝ A y)).trans (mul_le_mul_of_nonneg_left h.bdA hT)
  rw [div_eq_mul_inv, ← hW] at ht1
  have hr : |⟪ed n, fderiv ℝ A y u (ed n)⟫_ℝ| ≤ K * W * ‖u‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := norm_dA_apply_le h u (ed n)
    rw [norm_ed, mul_one] at this
    rw [norm_ed, one_mul]
    exact this
  rw [hg2, hg3]
  exact alg_divV ha0 h.g1_le ht2 ht1 hr hq heu hKC hκ0 hκ1 hc00 hc01 hW0 hT (norm_nonneg u) hC hK

/-! #### The bulk term `J` -/

theorem norm_carlV_le {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) : ‖carlV A (phi C₀) y‖ ≤ 5 / 4 := by
  rw [carlV_phi A C₀ h.spos, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [h.g1_ge] : (0 : ℝ) ≤ g1 C₀ (vcoord y))]
  have h1 := h.normAv (ed n)
  rw [norm_ed, mul_one] at h1
  calc g1 C₀ (vcoord y) * ‖A y (ed n)‖ ≤ 1 * (5 / 4) :=
        mul_le_mul h.g1_le h1 (norm_nonneg _) zero_le_one
    _ = 5 / 4 := by ring

theorem inner_V_gradQ_ge {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) :
    (C₀ / 2 - 5 / 4 * K) * (vcoord y ^ 2)⁻¹
      ≤ ⟪carlV A (phi C₀) y, gradient (carlQ A (phi C₀)) y⟫_ℝ := by
  have hs := h.spos
  rw [real_inner_comm, inner_gradient_left, fderiv_carlQ_apply C₀ hs h.diffA,
    carlV_phi A C₀ hs, map_smul, smul_apply, real_inner_smul_right,
    real_inner_smul_right]
  have hX : |⟪ed n, fderiv ℝ A y (A y (ed n)) (ed n)⟫_ℝ| ≤ 5 / 4 * K * (vcoord y ^ 2)⁻¹ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_ed, one_mul]
    have h1 := norm_dA_apply_le h (A y (ed n)) (ed n)
    have h2 := h.normAv (ed n)
    rw [norm_ed] at h1 h2
    have hKW : 0 ≤ K * (vcoord y ^ 2)⁻¹ := by have := h.hK; positivity
    calc ‖fderiv ℝ A y (A y (ed n)) (ed n)‖ ≤ K * (vcoord y ^ 2)⁻¹ * (5 / 4 * 1) * 1 :=
          h1.trans (by gcongr)
      _ = 5 / 4 * K * (vcoord y ^ 2)⁻¹ := by ring
  have hg := h.g1_ge
  have hg' := h.g1_le
  have ha := h.Add_ge
  have hb : g2 C₀ (vcoord y) = C₀ * (vcoord y ^ 2)⁻¹ := by rw [g2, div_eq_mul_inv]
  have hCW : 0 ≤ C₀ * (vcoord y ^ 2)⁻¹ := by have := h.hC₀; positivity
  set g := g1 C₀ (vcoord y) with hgdef
  set a := ⟪ed n, A y (ed n)⟫_ℝ with hadef
  set X := ⟪ed n, fderiv ℝ A y (A y (ed n)) (ed n)⟫_ℝ with hXdef
  have hg3 : 0 ≤ g ^ 3 := by positivity
  have hg31 : g ^ 3 ≤ 1 := pow_le_one₀ (by linarith) hg'
  have hXl : -(5 / 4 * K * (vcoord y ^ 2)⁻¹) ≤ g ^ 2 * (g * X) := by
    have e1 : |g ^ 2 * (g * X)| ≤ |X| := by
      rw [show g ^ 2 * (g * X) = g ^ 3 * X by ring, abs_mul, abs_of_nonneg hg3]
      exact mul_le_of_le_one_left (abs_nonneg _) hg31
    linarith [neg_abs_le (g ^ 2 * (g * X))]
  have hga : 9 / 16 ≤ g * a := by nlinarith
  have hmain : C₀ * (vcoord y ^ 2)⁻¹ / 2
      ≤ 2 * g * (g2 C₀ (vcoord y) * (g * a)) * a := by
    rw [hb, show 2 * g * (C₀ * (vcoord y ^ 2)⁻¹ * (g * a)) * a
      = 2 * (g * a) ^ 2 * (C₀ * (vcoord y ^ 2)⁻¹) by ring]
    have : (9 / 16) ^ 2 ≤ (g * a) ^ 2 := pow_le_pow_left₀ (by norm_num) hga 2
    nlinarith
  linarith

theorem inner_dV_ge {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) (ξ : Space n) :
    -(5 / 4 * K * (vcoord y ^ 2)⁻¹ * ‖ξ‖ ^ 2)
      ≤ ⟪fderiv ℝ (carlV A (phi C₀)) y (A y ξ), ξ⟫_ℝ := by
  have hs := h.spos
  rw [fderiv_carlV_apply C₀ hs h.diffA, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, h.symm (ed n) ξ]
  have hY : |⟪fderiv ℝ A y (A y ξ) (ed n), ξ⟫_ℝ| ≤ 5 / 4 * K * (vcoord y ^ 2)⁻¹ * ‖ξ‖ ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h1 := norm_dA_apply_le h (A y ξ) (ed n)
    have h2 := h.normAv ξ
    rw [norm_ed, mul_one] at h1
    have hKW : 0 ≤ K * (vcoord y ^ 2)⁻¹ := by have := h.hK; positivity
    calc ‖fderiv ℝ A y (A y ξ) (ed n)‖ * ‖ξ‖ ≤ K * (vcoord y ^ 2)⁻¹ * (5 / 4 * ‖ξ‖) * ‖ξ‖ := by
          gcongr
          exact h1.trans (by gcongr)
      _ = 5 / 4 * K * (vcoord y ^ 2)⁻¹ * ‖ξ‖ ^ 2 := by ring
  have hg0 : 0 ≤ g1 C₀ (vcoord y) := by linarith [h.g1_ge]
  have hgY : -(5 / 4 * K * (vcoord y ^ 2)⁻¹ * ‖ξ‖ ^ 2)
      ≤ g1 C₀ (vcoord y) * ⟪fderiv ℝ A y (A y ξ) (ed n), ξ⟫_ℝ := by
    have e1 : |g1 C₀ (vcoord y) * ⟪fderiv ℝ A y (A y ξ) (ed n), ξ⟫_ℝ|
        ≤ |⟪fderiv ℝ A y (A y ξ) (ed n), ξ⟫_ℝ| := by
      rw [abs_mul, abs_of_nonneg hg0]
      exact mul_le_of_le_one_left (abs_nonneg _) h.g1_le
    linarith [neg_abs_le (g1 C₀ (vcoord y) * ⟪fderiv ℝ A y (A y ξ) (ed n), ξ⟫_ℝ)]
  have hpos : 0 ≤ g2 C₀ (vcoord y) * ⟪ed n, A y ξ⟫_ℝ * ⟪ed n, A y ξ⟫_ℝ := by
    have := h.g2_nonneg
    rw [mul_assoc]
    exact mul_nonneg this (mul_self_nonneg _)
  linarith

theorem abs_inner_dA_le {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) (ξ : Space n) :
    |⟪fderiv ℝ A y (carlV A (phi C₀) y) ξ, ξ⟫_ℝ| ≤ 5 / 4 * K * (vcoord y ^ 2)⁻¹ * ‖ξ‖ ^ 2 := by
  have hs := h.spos
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h1 := norm_dA_apply_le h (carlV A (phi C₀) y) ξ
  have hV := norm_carlV_le h
  have hKW : 0 ≤ K * (vcoord y ^ 2)⁻¹ := by have := h.hK; positivity
  calc ‖fderiv ℝ A y (carlV A (phi C₀) y) ξ‖ * ‖ξ‖
      ≤ K * (vcoord y ^ 2)⁻¹ * ‖carlV A (phi C₀) y‖ * ‖ξ‖ * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ K * (vcoord y ^ 2)⁻¹ * (5 / 4) * ‖ξ‖ * ‖ξ‖ := by gcongr
    _ = 5 / 4 * K * (vcoord y ^ 2)⁻¹ * ‖ξ‖ ^ 2 := by ring

/-- **Lower bound for `J`** (part (a) of the proof of Proposition carleman). -/
theorem carlJ_ge {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) {τ : ℝ} (hτ : 0 ≤ τ) (w : Space n → ℝ) :
    (C₀ - 3 * K) * τ ^ 3 * ((vcoord y ^ 2)⁻¹ * w y ^ 2)
      - Csh n K * τ * ((vcoord y ^ 2)⁻¹ * w y ^ 2)
      - Csh n K * τ * ((vcoord y ^ 2)⁻¹ * ‖gradient w y‖ ^ 2)
      ≤ carlJ (fun _ => (1 : ℝ)) A (phi C₀) τ w y := by
  have hs := h.spos
  have hW0 : 0 ≤ (vcoord y ^ 2)⁻¹ := by positivity
  have hK := h.hK
  have hT := trN_nonneg (n := n)
  have t1 := inner_V_gradQ_ge h
  have t2 := inner_dV_ge h (gradient w y)
  have t3 := abs_inner_dA_le h (gradient w y)
  have t4 : |⟪A y (gradient w y), gradient (divMu (fun _ => (1 : ℝ)) (carlV A (phi C₀))) y⟫_ℝ|
      ≤ 5 / 4 * ‖gradient w y‖ * ((trN n + 1) * (vcoord y ^ 2)⁻¹) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hdv := norm_gradient_divV_le h
    rw [div_eq_mul_inv] at hdv
    exact mul_le_mul (h.normAv _) hdv (norm_nonneg _) (by positivity)
  have e1 := mul_le_mul_of_nonneg_left t1 (by positivity : (0 : ℝ) ≤ 2 * τ ^ 3 * w y ^ 2)
  have e2 := mul_le_mul_of_nonneg_left t2 (by positivity : (0 : ℝ) ≤ 4 * τ)
  have e3 : 2 * τ * ⟪fderiv ℝ A y (carlV A (phi C₀) y) (gradient w y), gradient w y⟫_ℝ
      ≤ 2 * τ * (5 / 4 * K * (vcoord y ^ 2)⁻¹ * ‖gradient w y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans t3) (by positivity)
  have e4a : -(|w y| * (5 / 4 * ‖gradient w y‖ * ((trN n + 1) * (vcoord y ^ 2)⁻¹)))
      ≤ w y * ⟪A y (gradient w y), gradient (divMu (fun _ => (1 : ℝ)) (carlV A (phi C₀))) y⟫_ℝ := by
    have h4 : |w y * ⟪A y (gradient w y),
        gradient (divMu (fun _ => (1 : ℝ)) (carlV A (phi C₀))) y⟫_ℝ|
        ≤ |w y| * (5 / 4 * ‖gradient w y‖ * ((trN n + 1) * (vcoord y ^ 2)⁻¹)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left t4 (abs_nonneg _)
    linarith [neg_abs_le (w y * ⟪A y (gradient w y),
      gradient (divMu (fun _ => (1 : ℝ)) (carlV A (phi C₀))) y⟫_ℝ)]
  have e4 := mul_le_mul_of_nonneg_left e4a (by positivity : (0 : ℝ) ≤ 2 * τ)
  have e5 : 2 * |w y| * ‖gradient w y‖ ≤ w y ^ 2 + ‖gradient w y‖ ^ 2 := by
    nlinarith [sq_nonneg (|w y| - ‖gradient w y‖), sq_abs (w y)]
  have e5' := mul_le_mul_of_nonneg_left e5
    (by positivity : (0 : ℝ) ≤ 5 / 8 * τ * (trN n + 1) * (vcoord y ^ 2)⁻¹)
  have p1 : 0 ≤ K * τ ^ 3 * (vcoord y ^ 2)⁻¹ * w y ^ 2 := by positivity
  have p2 : 0 ≤ (8 * K + 3 / 4 * trN n + 3 / 4) * τ * (vcoord y ^ 2)⁻¹ * w y ^ 2 := by positivity
  have p3 : 0 ≤ (1 / 2 * K + 3 / 4 * trN n + 3 / 4) * τ * (vcoord y ^ 2)⁻¹
      * ‖gradient w y‖ ^ 2 := by
    positivity
  simp only [carlJ, Csh]
  nlinarith

/-! #### Gradient control (part (b)) -/

/-- **Gradient control**, pointwise: Lemma 2.1(3) with `ϱ = s⁻²`. -/
theorem grad_ptwise {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) {τ : ℝ} (hτ : 5 ≤ τ) {w : Space n → ℝ} (hw : ContDiffAt ℝ 2 w y) :
    (vcoord y ^ 2)⁻¹ * ‖gradient w y‖ ^ 2
      ≤ 2 * |carlS (fun _ => (1 : ℝ)) A (phi C₀) τ w y| * ((vcoord y ^ 2)⁻¹ * |w y|)
        + 3 * τ ^ 2 * ((vcoord y ^ 2)⁻¹ * w y ^ 2) + 2 * divergence (Gf A w) y := by
  have hs := h.spos
  have key : (vcoord y ^ 2)⁻¹ * 1 * ⟪A y (gradient w y), gradient w y⟫_ℝ
      = -(carlS (fun _ => (1 : ℝ)) A (phi C₀) τ w y * (vcoord y ^ 2)⁻¹ * w y * 1)
        + τ ^ 2 * carlQ A (phi C₀) y * (vcoord y ^ 2)⁻¹ * w y ^ 2 * 1
        - 1 * w y * ⟪A y (gradient w y), gradient (fun z : Space n => (vcoord z ^ 2)⁻¹) y⟫_ℝ
        + divergence (Gf A w) y :=
    carleman_gradient_pointwise (fun _ => (1 : ℝ)) A (phi C₀) τ w
      (fun z => (vcoord z ^ 2)⁻¹) y contDiffAt_const one_ne_zero (h.cd.of_le (by norm_num)) hw
      (contDiffAt_invsq hs)
  -- the gradient of `s⁻²`
  have hd : HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹) (-(2 * vcoord y) / (vcoord y ^ 2) ^ 2)
      (vcoord y) := by
    have h0 := (hasDerivAt_pow 2 (vcoord y)).inv (pow_ne_zero 2 hs.ne')
    refine h0.congr_deriv ?_
    norm_num
  have hF : HasFDerivAt (fun z : Space n => (vcoord z ^ 2)⁻¹)
      ((-(2 * vcoord y) / (vcoord y ^ 2) ^ 2) • innerSL ℝ (ed n)) y :=
    hasFDerivAt_comp_vcoord hd
  have hgr : gradient (fun z : Space n => (vcoord z ^ 2)⁻¹) y
      = (-(2 * vcoord y) / (vcoord y ^ 2) ^ 2) • ed n := by
    refine ext_inner_right ℝ fun ξ => ?_
    rw [inner_gradient_left, hF.fderiv, real_inner_smul_left, smul_apply,
      innerSL_apply_apply, smul_eq_mul]
  set W := (vcoord y ^ 2)⁻¹ with hW
  have hW0 : 0 < W := by positivity
  have hsW : vcoord y ^ 2 * W = 1 := by rw [hW]; field_simp
  have hW1 : W ≤ 1 := by
    rw [hW]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h.hs1)
  have hc : -(2 * vcoord y) / (vcoord y ^ 2) ^ 2 = -(2 * vcoord y * W ^ 2) := by
    rw [hW]; field_simp
  -- the three error terms
  have c1 : 3 / 4 * (W * ‖gradient w y‖ ^ 2) ≤ W * ⟪A y (gradient w y), gradient w y⟫_ℝ := by
    have := mul_le_mul_of_nonneg_left (h.coer (gradient w y)) hW0.le
    linarith
  have hq : carlQ A (phi C₀) y ≤ 5 / 4 := by
    rw [carlQ_phi A C₀ hs]
    have hg := h.g1_ge
    have hg' := h.g1_le
    have ha := h.Add_ge
    have ha' := h.Add_le
    have hg2 : g1 C₀ (vcoord y) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) hg'
    nlinarith
  have c3 : τ ^ 2 * carlQ A (phi C₀) y * W * w y ^ 2 ≤ 5 / 4 * τ ^ 2 * (W * w y ^ 2) := by
    have : 0 ≤ τ ^ 2 * (W * w y ^ 2) := by positivity
    nlinarith
  have c4 : |w y * ⟪A y (gradient w y), gradient (fun z : Space n => (vcoord z ^ 2)⁻¹) y⟫_ℝ|
      ≤ 5 / 2 * vcoord y * W ^ 2 * (|w y| * ‖gradient w y‖) := by
    rw [hgr, hc, real_inner_smul_right, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * vcoord y * W ^ 2)]
    have h1 : |⟪A y (gradient w y), ed n⟫_ℝ| ≤ 5 / 4 * ‖gradient w y‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_ed, mul_one]
      exact h.normAv _
    have h2 : 0 ≤ 2 * vcoord y * W ^ 2 := by positivity
    calc |w y| * (2 * vcoord y * W ^ 2 * |⟪A y (gradient w y), ed n⟫_ℝ|)
        ≤ |w y| * (2 * vcoord y * W ^ 2 * (5 / 4 * ‖gradient w y‖)) := by gcongr
      _ = 5 / 2 * vcoord y * W ^ 2 * (|w y| * ‖gradient w y‖) := by ring
  have c5 : 5 / 2 * vcoord y * W ^ 2 * (|w y| * ‖gradient w y‖)
      ≤ 1 / 4 * (W * ‖gradient w y‖ ^ 2) + 25 / 4 * (W * w y ^ 2) := by
    have hsq := mul_nonneg hW0.le
      (sq_nonneg (1 / 2 * ‖gradient w y‖ - 5 / 2 * vcoord y * W * |w y|))
    have ex : W * (1 / 2 * ‖gradient w y‖ - 5 / 2 * vcoord y * W * |w y|) ^ 2
        = 1 / 4 * (W * ‖gradient w y‖ ^ 2)
          - 5 / 2 * vcoord y * W ^ 2 * (|w y| * ‖gradient w y‖)
          + 25 / 4 * (W * (vcoord y * W) ^ 2 * |w y| ^ 2) := by ring
    rw [sq_abs] at ex
    have e : W * (vcoord y * W) ^ 2 * w y ^ 2 = W * w y ^ 2 * (W * (vcoord y ^ 2 * W)) := by ring
    have hWW : W * (vcoord y ^ 2 * W) ≤ 1 := by rw [hsW, mul_one]; exact hW1
    have h3 : W * (vcoord y * W) ^ 2 * w y ^ 2 ≤ W * w y ^ 2 := by
      rw [e]
      exact mul_le_of_le_one_right (by positivity) hWW
    linarith
  have c6 : 25 / 4 * (W * w y ^ 2) ≤ 1 / 4 * τ ^ 2 * (W * w y ^ 2) := by
    have : (25 : ℝ) ≤ τ ^ 2 := by nlinarith
    have : 0 ≤ W * w y ^ 2 := by positivity
    nlinarith
  have c2 : -(carlS (fun _ => (1 : ℝ)) A (phi C₀) τ w y * W * w y)
      ≤ |carlS (fun _ => (1 : ℝ)) A (phi C₀) τ w y| * (W * |w y|) := by
    have := neg_abs_le (carlS (fun _ => (1 : ℝ)) A (phi C₀) τ w y * W * w y)
    rw [abs_mul, abs_mul, abs_of_pos hW0] at this
    linarith
  have c4' := neg_abs_le (w y * ⟪A y (gradient w y),
    gradient (fun z : Space n => (vcoord z ^ 2)⁻¹) y⟫_ℝ)
  have c4'' := le_abs_self (w y * ⟪A y (gradient w y),
    gradient (fun z : Space n => (vcoord z ^ 2)⁻¹) y⟫_ℝ)
  nlinarith

/-! #### Conjugation and the flux identity -/

theorem conj_pt {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) (τ : ℝ) {v : Space n → ℝ} (hv : ContDiff ℝ 2 v) :
    Real.exp (τ * phi C₀ y) * divergence (fun z => A z (gradient v z)) y
      = carlS (fun _ => (1 : ℝ)) A (phi C₀) τ (wc C₀ τ v) y
        + carlT (fun _ => (1 : ℝ)) A (phi C₀) τ (wc C₀ τ v) y := by
  have key := F2.carleman_conj_of_symm' (fun _ => (1 : ℝ)) A (phi C₀) τ v y contDiffAt_const
    one_ne_zero (h.cd.of_le (by norm_num)) h.symm (contDiffAt_phi C₀ h.spos) hv.contDiffAt
  rw [F2.divMu_one] at key
  exact key

/-- `F2.carleman_pointwise` with the symmetry of `B` assumed only at the point `x`.
Adapted (verbatim proof) from this project, `MazyaRefinedCauchy/Pkg/F2.lean`,
`carleman_pointwise`, whose proof only uses the symmetry at `x`. -/
theorem carleman_pointwise_loc (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 2 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 2 B x)
    (hsx : ∀ ξ η, ⟪B x ξ, η⟫_ℝ = ⟪ξ, B x η⟫_ℝ)
    (hφ : ContDiffAt ℝ 3 φ x) (hw : ContDiffAt ℝ 2 w x) :
    2 * carlS μ B φ τ w x * carlT μ B φ τ w x * μ x
      = carlJ μ B φ τ w x + divergence (carlFlux μ B φ τ w) x := by
  -- regularity at `x`
  have hμd : DifferentiableAt ℝ μ x := hμ.differentiableAt (by simp)
  have hBd : DifferentiableAt ℝ B x := hB.differentiableAt (by simp)
  have hwd : DifferentiableAt ℝ w x := hw.differentiableAt (by simp)
  have hgw : DifferentiableAt ℝ (gradient w) x := F2.differentiableAt_gradient hw
  have hgφ2 : ContDiffAt ℝ 2 (gradient φ) x := F2.contDiffAt_gradient hφ (by norm_num)
  have hgφ : DifferentiableAt ℝ (gradient φ) x := hgφ2.differentiableAt (by simp)
  have hV2 : ContDiffAt ℝ 2 (carlV B φ) x := hB.clm_apply hgφ2
  have hVd : DifferentiableAt ℝ (carlV B φ) x := hV2.differentiableAt (by simp)
  have hWd : DifferentiableAt ℝ (fun y => B y (gradient w y)) x := hBd.clm_apply hgw
  have hμWd : DifferentiableAt ℝ (fun y => μ y • B y (gradient w y)) x := hμd.smul hWd
  have hμVd : DifferentiableAt ℝ (fun y => μ y • carlV B φ y) x := hμd.smul hVd
  have had : DifferentiableAt ℝ (fun y => ⟪carlV B φ y, gradient w y⟫_ℝ) x := hVd.inner ℝ hgw
  have hbd : DifferentiableAt ℝ (fun y => ⟪B y (gradient w y), gradient w y⟫_ℝ) x :=
    hWd.inner ℝ hgw
  have hqd : DifferentiableAt ℝ (carlQ B φ) x := (hBd.clm_apply hgφ).inner ℝ hgφ
  have hδd : DifferentiableAt ℝ (divMu μ (carlV B φ)) x := by
    have h2 : ContDiffAt ℝ 2 (fun y => μ y • carlV B φ y) x := hμ.smul hV2
    exact (hμd.inv hμ0).mul (F2.differentiableAt_divergence h2)
  have hfWd : DifferentiableAt ℝ (fun y => -4 * τ * ⟪carlV B φ y, gradient w y⟫_ℝ
      - 2 * τ * divMu μ (carlV B φ) y * w y) x :=
    (had.const_mul _).sub ((hδd.const_mul _).mul hwd)
  have hfVd : DifferentiableAt ℝ (fun y => 2 * τ * ⟪B y (gradient w y), gradient w y⟫_ℝ
      - 2 * τ ^ 3 * carlQ B φ y * w y ^ 2) x :=
    (hbd.const_mul _).sub ((hqd.const_mul _).mul (hwd.pow 2))
  have h1d : DifferentiableAt ℝ (fun y => (-4 * τ * ⟪carlV B φ y, gradient w y⟫_ℝ
      - 2 * τ * divMu μ (carlV B φ) y * w y) • (μ y • B y (gradient w y))) x := hfWd.smul hμWd
  have h2d : DifferentiableAt ℝ (fun y => (2 * τ * ⟪B y (gradient w y), gradient w y⟫_ℝ
      - 2 * τ ^ 3 * carlQ B φ y * w y ^ 2) • (μ y • carlV B φ y)) x := hfVd.smul hμVd
  -- symmetry facts
  have hH : ∀ u v, ⟪fderiv ℝ (gradient w) x u, v⟫_ℝ = ⟪fderiv ℝ (gradient w) x v, u⟫_ℝ :=
    F2.inner_fderiv_gradient_comm hw
  -- derivatives of the coefficients of the flux
  have hW_fd : ∀ u, fderiv ℝ (fun y => B y (gradient w y)) x u
      = B x (fderiv ℝ (gradient w) x u) + fderiv ℝ B x u (gradient w x) := by
    intro u
    rw [fderiv_clm_apply hBd hgw]
    simp
  have ha_fd : ∀ u, fderiv ℝ (fun y => ⟪carlV B φ y, gradient w y⟫_ℝ) x u
      = ⟪carlV B φ x, fderiv ℝ (gradient w) x u⟫_ℝ
        + ⟪fderiv ℝ (carlV B φ) x u, gradient w x⟫_ℝ :=
    fun u => fderiv_inner_apply ℝ hVd hgw u
  have hb_fd : ∀ u, fderiv ℝ (fun y => ⟪B y (gradient w y), gradient w y⟫_ℝ) x u
      = ⟪B x (gradient w x), fderiv ℝ (gradient w) x u⟫_ℝ
        + ⟪B x (fderiv ℝ (gradient w) x u) + fderiv ℝ B x u (gradient w x), gradient w x⟫_ℝ := by
    intro u
    rw [fderiv_inner_apply ℝ hWd hgw u, hW_fd]
  have hfW_fd : ∀ u, fderiv ℝ (fun y => -4 * τ * ⟪carlV B φ y, gradient w y⟫_ℝ
      - 2 * τ * divMu μ (carlV B φ) y * w y) x u
      = -4 * τ * fderiv ℝ (fun y => ⟪carlV B φ y, gradient w y⟫_ℝ) x u
        - 2 * τ * (divMu μ (carlV B φ) x * fderiv ℝ w x u
          + w x * fderiv ℝ (divMu μ (carlV B φ)) x u) := by
    intro u
    have h : HasFDerivAt (fun y => -4 * τ * ⟪carlV B φ y, gradient w y⟫_ℝ
        - 2 * τ * divMu μ (carlV B φ) y * w y) _ x :=
      (had.hasFDerivAt.const_mul (-4 * τ)).sub
        ((hδd.hasFDerivAt.const_mul (2 * τ)).mul hwd.hasFDerivAt)
    rw [h.fderiv]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  have hfV_fd : ∀ u, fderiv ℝ (fun y => 2 * τ * ⟪B y (gradient w y), gradient w y⟫_ℝ
      - 2 * τ ^ 3 * carlQ B φ y * w y ^ 2) x u
      = 2 * τ * fderiv ℝ (fun y => ⟪B y (gradient w y), gradient w y⟫_ℝ) x u
        - 2 * τ ^ 3 * (carlQ B φ x * (2 * w x * fderiv ℝ w x u)
          + w x ^ 2 * fderiv ℝ (carlQ B φ) x u) := by
    intro u
    have h : HasFDerivAt (fun y => 2 * τ * ⟪B y (gradient w y), gradient w y⟫_ℝ
        - 2 * τ ^ 3 * carlQ B φ y * w y ^ 2) _ x :=
      (hbd.hasFDerivAt.const_mul (2 * τ)).sub
        ((hqd.hasFDerivAt.const_mul (2 * τ ^ 3)).mul (hwd.hasFDerivAt.pow 2))
    rw [h.fderiv]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  -- the divergence of the flux
  rw [F2.carlFlux_eq, F2.divergence_add h1d h2d, F2.divergence_smul hfWd hμWd,
    F2.divergence_smul hfVd hμVd, hfW_fd, hfV_fd, ← F2.mul_divMu hμ0, ← F2.mul_divMu hμ0]
  simp only [map_smul, smul_eq_mul]
  rw [ha_fd, hb_fd]
  simp only [carlS, carlT, carlJ]
  -- identify the remaining atoms
  have e1 : ⟪carlV B φ x, gradient (carlQ B φ) x⟫_ℝ = fderiv ℝ (carlQ B φ) x (carlV B φ x) := by
    rw [real_inner_comm, inner_gradient_left]
  have e2 : ⟪B x (gradient w x), gradient (divMu μ (carlV B φ)) x⟫_ℝ
      = fderiv ℝ (divMu μ (carlV B φ)) x (B x (gradient w x)) := by
    rw [real_inner_comm, inner_gradient_left]
  have e3 : fderiv ℝ w x (B x (gradient w x)) = ⟪B x (gradient w x), gradient w x⟫_ℝ := by
    rw [← inner_gradient_left, real_inner_comm]
  have e4 : fderiv ℝ w x (carlV B φ x) = ⟪carlV B φ x, gradient w x⟫_ℝ := by
    rw [← inner_gradient_left, real_inner_comm]
  have e5 : ⟪carlV B φ x, fderiv ℝ (gradient w) x (B x (gradient w x))⟫_ℝ
      = ⟪fderiv ℝ (gradient w) x (carlV B φ x), B x (gradient w x)⟫_ℝ := by
    rw [real_inner_comm, hH]
  have e6 : ⟪B x (gradient w x), fderiv ℝ (gradient w) x (carlV B φ x)⟫_ℝ
      = ⟪fderiv ℝ (gradient w) x (carlV B φ x), B x (gradient w x)⟫_ℝ := by
    rw [real_inner_comm]
  have e7 : ⟪B x (fderiv ℝ (gradient w) x (carlV B φ x))
        + fderiv ℝ B x (carlV B φ x) (gradient w x), gradient w x⟫_ℝ
      = ⟪fderiv ℝ (gradient w) x (carlV B φ x), B x (gradient w x)⟫_ℝ
        + ⟪fderiv ℝ B x (carlV B φ x) (gradient w x), gradient w x⟫_ℝ := by
    rw [inner_add_left, hsx]
  rw [e1, e2, e3, e4, e5, e6, e7]
  ring

/-! #### From `w` back to `v` -/

theorem gradient_wc {C₀ τ : ℝ} {v : Space n → ℝ} {y : Space n} (hy : 0 < vcoord y)
    (hv : DifferentiableAt ℝ v y) :
    gradient (wc C₀ τ v) y
      = Real.exp (τ * phi C₀ y) • gradient v y
        + (τ * g1 C₀ (vcoord y) * wc C₀ τ v y) • ed n := by
  have hE : HasFDerivAt (fun z => Real.exp (τ * phi C₀ z)) _ y :=
    ((hasFDerivAt_phi C₀ hy).const_mul τ).exp
  have hW : HasFDerivAt (wc C₀ τ v) _ y := hE.mul hv.hasFDerivAt
  refine ext_inner_right ℝ fun ξ => ?_
  rw [inner_gradient_left, hW.fderiv, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradient_left]
  simp only [add_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul, wc]
  ring

theorem exp_sq_eq (C₀ τ : ℝ) (y : Space n) :
    Real.exp (2 * τ * gw C₀ (vcoord y)) = Real.exp (τ * phi C₀ y) ^ 2 := by
  rw [sq, ← Real.exp_add]
  congr 1
  simp only [phi]
  ring

theorem exp_norm_grad_le {C₀ τ : ℝ} {v : Space n → ℝ} {y : Space n} (hy : 0 < vcoord y)
    (hg0 : 0 ≤ g1 C₀ (vcoord y)) (hg1 : g1 C₀ (vcoord y) ≤ 1) (hv : DifferentiableAt ℝ v y) :
    Real.exp (2 * τ * gw C₀ (vcoord y)) * ‖gradient v y‖ ^ 2
      ≤ 2 * ‖gradient (wc C₀ τ v) y‖ ^ 2 + 2 * τ ^ 2 * wc C₀ τ v y ^ 2 := by
  have hg := gradient_wc (C₀ := C₀) (τ := τ) hy hv
  have h1 : Real.exp (τ * phi C₀ y) • gradient v y
      = gradient (wc C₀ τ v) y - (τ * g1 C₀ (vcoord y) * wc C₀ τ v y) • ed n := by
    rw [hg]
    abel
  have h2 : ‖Real.exp (τ * phi C₀ y) • gradient v y‖
      ≤ ‖gradient (wc C₀ τ v) y‖ + |τ * g1 C₀ (vcoord y) * wc C₀ τ v y| := by
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_ed, mul_one, Real.norm_eq_abs]
  have h3 : ‖Real.exp (τ * phi C₀ y) • gradient v y‖
      = Real.exp (τ * phi C₀ y) * ‖gradient v y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h4 : |τ * g1 C₀ (vcoord y) * wc C₀ τ v y| ≤ |τ| * |wc C₀ τ v y| := by
    rw [abs_mul, abs_mul]
    have hga : |g1 C₀ (vcoord y)| ≤ 1 := abs_le.mpr ⟨by linarith, hg1⟩
    calc |τ| * |g1 C₀ (vcoord y)| * |wc C₀ τ v y| ≤ |τ| * 1 * |wc C₀ τ v y| := by gcongr
      _ = |τ| * |wc C₀ τ v y| := by ring
  rw [exp_sq_eq]
  have h5 : Real.exp (τ * phi C₀ y) * ‖gradient v y‖
      ≤ ‖gradient (wc C₀ τ v) y‖ + |τ| * |wc C₀ τ v y| := by linarith
  have h6 : 0 ≤ Real.exp (τ * phi C₀ y) * ‖gradient v y‖ := by positivity
  calc Real.exp (τ * phi C₀ y) ^ 2 * ‖gradient v y‖ ^ 2
      = (Real.exp (τ * phi C₀ y) * ‖gradient v y‖) ^ 2 := by ring
    _ ≤ (‖gradient (wc C₀ τ v) y‖ + |τ| * |wc C₀ τ v y|) ^ 2 := pow_le_pow_left₀ h6 h5 2
    _ ≤ 2 * ‖gradient (wc C₀ τ v) y‖ ^ 2 + 2 * τ ^ 2 * wc C₀ τ v y ^ 2 := by
        nlinarith [sq_nonneg (‖gradient (wc C₀ τ v) y‖ - |τ| * |wc C₀ τ v y|), sq_abs τ,
          sq_abs (wc C₀ τ v y)]

/-! #### The main pointwise inequality -/

/-- Pure algebra of part (c): `2|S|W|w| C♯τ ≤ S²/2 + 2C♯²τ² W w²`. -/
theorem alg_s6 {S ww W Cs τ : ℝ} (hW0 : 0 < W) (hW1 : W ≤ 1) (_hCs0 : 0 ≤ Cs) (_hτ0 : 0 ≤ τ) :
    2 * Cs * τ * (|S| * (W * |ww|)) ≤ 1 / 2 * S ^ 2 + 2 * Cs ^ 2 * τ ^ 2 * (W * ww ^ 2) := by
  have hW2 : W ^ 2 * ww ^ 2 ≤ W * ww ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
  have h1 := sq_nonneg (|S| - 2 * Cs * τ * W * |ww|)
  have ex : (|S| - 2 * Cs * τ * W * |ww|) ^ 2
      = |S| ^ 2 - 4 * (Cs * τ * (|S| * (W * |ww|)))
        + 4 * (Cs ^ 2 * τ ^ 2) * (W ^ 2 * |ww| ^ 2) := by ring
  rw [sq_abs, sq_abs] at ex
  have h2 := mul_le_mul_of_nonneg_left hW2 (by positivity : (0 : ℝ) ≤ 4 * (Cs ^ 2 * τ ^ 2))
  linarith

/-- Pure algebra of part (c): `2τ|S|W|w| ≤ S² + τ³ W w²`. -/
theorem alg_s11 {S ww W τ : ℝ} (hW0 : 0 < W) (hW1 : W ≤ 1) (hτ1 : 1 ≤ τ) :
    2 * τ * (|S| * (W * |ww|)) ≤ S ^ 2 + τ ^ 3 * (W * ww ^ 2) := by
  have hτ0 : 0 ≤ τ := by linarith
  have hW2 : W ^ 2 * ww ^ 2 ≤ W * ww ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
  have hX : 0 ≤ W * ww ^ 2 := by positivity
  have h1 := sq_nonneg (|S| - τ * W * |ww|)
  have ex : (|S| - τ * W * |ww|) ^ 2
      = |S| ^ 2 - 2 * τ * (|S| * (W * |ww|)) + τ ^ 2 * (W ^ 2 * |ww| ^ 2) := by ring
  rw [sq_abs, sq_abs] at ex
  have h2 := mul_le_mul_of_nonneg_left hW2 (by positivity : (0 : ℝ) ≤ τ ^ 2)
  have h3 : τ ^ 2 * (W * ww ^ 2) ≤ τ ^ 3 * (W * ww ^ 2) := by
    have : τ ^ 2 ≤ τ ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hX
  linarith

/-- Pure algebra of part (c): combination of all pointwise facts. -/
theorem alg_main {S T J dF dG P E gw gv ww a W Cs τ vv : ℝ}
    (hτ5 : 5 ≤ τ) (hτC : 2 * Cs ^ 2 + Cs ≤ τ) (hCs0 : 0 ≤ Cs) (hW0 : 0 < W) (hW1 : W ≤ 1)
    (hconj : a * P = S + T) (hflux : 2 * S * T * 1 = J + dF)
    (hJ : (3 * Cs + 2) * τ ^ 3 * (W * ww ^ 2) - Cs * τ * (W * ww ^ 2) - Cs * τ * (W * gw ^ 2) ≤ J)
    (hG : W * gw ^ 2 ≤ 2 * |S| * (W * |ww|) + 3 * τ ^ 2 * (W * ww ^ 2) + 2 * dG)
    (hgv : E * gv ^ 2 ≤ 2 * gw ^ 2 + 2 * τ ^ 2 * ww ^ 2)
    (hE : E = a ^ 2) (hwv : ww = a * vv) :
    τ ^ 3 * (W * E * vv ^ 2) + τ * (W * E * gv ^ 2)
      ≤ 11 * (E * P ^ 2) - 11 * dF + (22 * Cs + 4) * τ * dG := by
  have hτ0 : 0 ≤ τ := by linarith
  have hτ1 : 1 ≤ τ := by linarith
  have hX : 0 ≤ W * ww ^ 2 := by positivity
  have s1 : E * P ^ 2 = (S + T) ^ 2 := by rw [hE, ← hconj]; ring
  have s2 : S ^ 2 + J + dF ≤ (S + T) ^ 2 := by nlinarith [sq_nonneg T]
  have s3 : W * E * vv ^ 2 = W * ww ^ 2 := by rw [hwv, hE]; ring
  have s3' : τ ^ 3 * (W * E * vv ^ 2) = τ ^ 3 * (W * ww ^ 2) := by rw [s3]
  have s4 := mul_le_mul_of_nonneg_left hgv (mul_nonneg hτ0 hW0.le)
  have s5 := mul_le_mul_of_nonneg_left hG (mul_nonneg hCs0 hτ0)
  have s10 := mul_le_mul_of_nonneg_left hG hτ0
  have s6 := alg_s6 (S := S) (ww := ww) hW0 hW1 hCs0 hτ0
  have s11 := alg_s11 (S := S) (ww := ww) hW0 hW1 hτ1
  have hτ3 : 2 * Cs ^ 2 * τ ^ 2 + Cs * τ ≤ τ ^ 3 := by
    have a1 : 0 ≤ τ ^ 2 * (τ - 2 * Cs ^ 2 - Cs) := mul_nonneg (sq_nonneg τ) (by linarith)
    have a2 : 0 ≤ Cs * τ * (τ - 1) := mul_nonneg (mul_nonneg hCs0 hτ0) (by linarith)
    nlinarith
  have s8 := mul_le_mul_of_nonneg_right hτ3 hX
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have s4' : τ * (W * E * gv ^ 2) ≤ τ * W * (2 * gw ^ 2 + 2 * τ ^ 2 * ww ^ 2) := by
    have : τ * (W * E * gv ^ 2) = τ * W * (E * gv ^ 2) := by ring
    rw [this]
    exact s4
  linarith

theorem main_ptwise {A : Space n → Space n →L[ℝ] Space n} {K C₀ : ℝ} {y : Space n}
    (h : PtHyp A K C₀ y) (hC₀ : C₀ = 3 * K + 3 * Csh n K + 2)
    {τ : ℝ} (hτ5 : 5 ≤ τ) (hτC : 2 * Csh n K ^ 2 + Csh n K ≤ τ)
    {v : Space n → ℝ} (hv : ContDiff ℝ 2 v) :
    τ ^ 3 * ((vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y)) * v y ^ 2)
      + τ * ((vcoord y ^ 2)⁻¹ * Real.exp (2 * τ * gw C₀ (vcoord y)) * ‖gradient v y‖ ^ 2)
      ≤ 11 * (Real.exp (2 * τ * gw C₀ (vcoord y))
            * divergence (fun z => A z (gradient v z)) y ^ 2)
        - 11 * divergence (carlFlux (fun _ => (1 : ℝ)) A (phi C₀) τ (wc C₀ τ v)) y
        + (22 * Csh n K + 4) * τ * divergence (Gf A (wc C₀ τ v)) y := by
  have hs := h.spos
  have hτ0 : 0 ≤ τ := by linarith
  have hT := trN_nonneg (n := n)
  have hK := h.hK
  have hCs0 : 0 ≤ Csh n K := by unfold Csh; linarith
  have hw2 : ContDiffAt ℝ 2 (wc C₀ τ v) y := contDiffAt_wc C₀ τ hv hs
  have hconj := conj_pt h τ hv
  have hflux := carleman_pointwise_loc (fun _ => (1 : ℝ)) A (phi C₀) τ (wc C₀ τ v) y
    contDiffAt_const one_ne_zero h.cd h.symm (contDiffAt_phi C₀ hs) hw2
  have hJ := carlJ_ge h hτ0 (wc C₀ τ v)
  have hG := grad_ptwise h hτ5 hw2
  have hgv := exp_norm_grad_le (C₀ := C₀) (τ := τ) hs (by linarith [h.g1_ge]) h.g1_le
    ((hv.differentiable (by norm_num)) y)
  have hE := exp_sq_eq C₀ τ y
  have hwv : wc C₀ τ v y = Real.exp (τ * phi C₀ y) * v y := rfl
  have hW0 : 0 < (vcoord y ^ 2)⁻¹ := by positivity
  have hW1 : (vcoord y ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h.hs1)
  have hCK : C₀ - 3 * K = 3 * Csh n K + 2 := by rw [hC₀]; ring
  rw [hCK] at hJ
  exact alg_main hτ5 hτC hCs0 hW0 hW1 hconj hflux hJ hG hgv hE hwv

/-! #### Support and regularity of the fields -/

theorem wc_eq_zero {C₀ τ : ℝ} {v : Space n → ℝ} {z : Space n} (hz : z ∉ tsupport v) :
    wc C₀ τ v z = 0 := by
  simp [wc, image_eq_zero_of_notMem_tsupport hz]

theorem gradient_wc_eq_zero {C₀ τ : ℝ} {v : Space n → ℝ} {z : Space n} (hz : z ∉ tsupport v) :
    gradient (wc C₀ τ v) z = 0 := by
  have h0 : wc C₀ τ v =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_eq_zero_of_not_mem_tsupport hz] with x hx
    exact wc_eq_zero hx
  rw [h0.gradient_eq, gradient_fun_const]

theorem flux_eq_zero {A : Space n → Space n →L[ℝ] Space n} {C₀ τ : ℝ} {v : Space n → ℝ}
    {z : Space n} (hz : z ∉ tsupport v) :
    carlFlux (fun _ => (1 : ℝ)) A (phi C₀) τ (wc C₀ τ v) z = 0 := by
  simp [carlFlux, wc_eq_zero hz, gradient_wc_eq_zero hz]

theorem Gf_eq_zero {A : Space n → Space n →L[ℝ] Space n} {C₀ τ : ℝ} {v : Space n → ℝ}
    {z : Space n} (hz : z ∉ tsupport v) : Gf A (wc C₀ τ v) z = 0 := by
  simp [Gf, wc_eq_zero hz]

theorem divergence_eq_zero_of {F : Space n → Space n} {v : Space n → ℝ}
    (hF : ∀ z, z ∉ tsupport v → F z = 0) {y : Space n} (hy : y ∉ tsupport v) :
    divergence F y = 0 := by
  have h : F =ᶠ[𝓝 y] fun _ => (0 : Space n) := by
    filter_upwards [eventually_eq_zero_of_not_mem_tsupport hy] with z hz
    exact hF z hz
  rw [F2.divergence_congr h]
  simp [divergence]

theorem contDiff_of_local {F : Space n → Space n} {v : Space n → ℝ} {l : ℝ}
    (hF : ∀ z, z ∉ tsupport v → F z = 0) (hvs : tsupport v ⊆ H n l)
    (hFH : ∀ y ∈ H n l, ContDiffAt ℝ 1 F y) : ContDiff ℝ 1 F := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ H n l
  · exact hFH y hy
  · have hy' : y ∉ tsupport v := fun h => hy (hvs h)
    have h : F =ᶠ[𝓝 y] fun _ => (0 : Space n) := by
      filter_upwards [eventually_eq_zero_of_not_mem_tsupport hy'] with z hz
      exact hF z hz
    exact contDiffAt_const.congr_of_eventuallyEq h

theorem hasCompactSupport_of {F : Space n → Space n} {v : Space n → ℝ}
    (hvc : HasCompactSupport v) (hF : ∀ z, z ∉ tsupport v → F z = 0) : HasCompactSupport F :=
  HasCompactSupport.intro hvc fun z hz => hF z hz

theorem integrable_divergence {F : Space n → Space n} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) : Integrable (fun y => divergence F y) := by
  have hc : Continuous (fun y => divergence F y) :=
    (F2.traceCLM (n := n)).continuous.comp (hF.continuous_fderiv one_ne_zero)
  have hs : HasCompactSupport (fun y => divergence F y) :=
    (hFc.fderiv ℝ).comp_left (g := F2.traceCLM (n := n)) (map_zero _)
  exact hc.integrable_of_hasCompactSupport hs

theorem contDiffAt_flux {A : Space n → Space n →L[ℝ] Space n} {C₀ τ : ℝ} {v : Space n → ℝ}
    {y : Space n} (hy : 0 < vcoord y) (hA : ContDiffAt ℝ 2 A y) (hv : ContDiff ℝ 2 v) :
    ContDiffAt ℝ 1 (carlFlux (fun _ => (1 : ℝ)) A (phi C₀) τ (wc C₀ τ v)) y := by
  have hw2 := contDiffAt_wc C₀ τ hv hy
  have hw : ContDiffAt ℝ 1 (wc C₀ τ v) y := hw2.of_le (by norm_num)
  have hgw : ContDiffAt ℝ 1 (gradient (wc C₀ τ v)) y := F2.contDiffAt_gradient hw2 (by norm_num)
  have hA1 : ContDiffAt ℝ 1 A y := hA.of_le (by norm_num)
  have hgφ : ContDiffAt ℝ 2 (gradient (phi C₀)) y :=
    F2.contDiffAt_gradient (contDiffAt_phi C₀ hy (k := 3)) (by norm_num)
  have hV2 : ContDiffAt ℝ 2 (carlV A (phi C₀)) y := hA.clm_apply hgφ
  have hV : ContDiffAt ℝ 1 (carlV A (phi C₀)) y := hV2.of_le (by norm_num)
  have hq : ContDiffAt ℝ 1 (carlQ A (phi C₀)) y :=
    (hA1.clm_apply (hgφ.of_le (by norm_num))).inner ℝ (hgφ.of_le (by norm_num))
  have hV2' : ContDiffAt ℝ 2 (fun z => (fun _ => (1 : ℝ)) z • carlV A (phi C₀) z) y :=
    (contDiffAt_const (c := (1 : ℝ))).smul hV2
  have hdv : ContDiffAt ℝ 1
      (fun x => divergence (fun z => (fun _ => (1 : ℝ)) z • carlV A (phi C₀) z) x) y :=
    (F2.traceCLM (n := n)).contDiff.contDiffAt.comp y (hV2'.fderiv_right (m := 1) (by norm_num))
  have hdiv : ContDiffAt ℝ 1 (divMu (fun _ => (1 : ℝ)) (carlV A (phi C₀))) y :=
    contDiffAt_const.mul hdv
  have h1 : ContDiffAt ℝ 1 (fun x => ⟪carlV A (phi C₀) x, gradient (wc C₀ τ v) x⟫_ℝ) y :=
    hV.inner ℝ hgw
  have hAg : ContDiffAt ℝ 1 (fun x => A x (gradient (wc C₀ τ v) x)) y := hA1.clm_apply hgw
  have h2 : ContDiffAt ℝ 1
      (fun x => ⟪A x (gradient (wc C₀ τ v) x), gradient (wc C₀ τ v) x⟫_ℝ) y := hAg.inner ℝ hgw
  exact (contDiffAt_const (c := (1 : ℝ))).smul (((((contDiffAt_const.mul h1).smul hAg).add
    ((contDiffAt_const.mul h2).smul hV)).sub
    (((contDiffAt_const.mul hdiv).mul hw).smul hAg)).sub
    (((contDiffAt_const.mul hq).mul (hw.pow 2)).smul hV))

theorem contDiffAt_Gf {A : Space n → Space n →L[ℝ] Space n} {C₀ τ : ℝ} {v : Space n → ℝ}
    {y : Space n} (hy : 0 < vcoord y) (hA : ContDiffAt ℝ 2 A y) (hv : ContDiff ℝ 2 v) :
    ContDiffAt ℝ 1 (Gf A (wc C₀ τ v)) y := by
  have hw2 := contDiffAt_wc C₀ τ hv hy
  have hgw : ContDiffAt ℝ 1 (gradient (wc C₀ τ v)) y := F2.contDiffAt_gradient hw2 (by norm_num)
  have hA1 : ContDiffAt ℝ 1 A y := hA.of_le (by norm_num)
  exact ((contDiffAt_const.mul (contDiffAt_invsq hy)).mul (hw2.of_le (by norm_num))).smul
    (hA1.clm_apply hgw)

end W_PL_carleman

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
  -- Proof (Proposition carleman of the note, with `μ = 1`, `B = A`, `φ = gw C₀ ∘ vcoord`,
  -- `w = e^{τφ} v`): `C♯ = 8K + 2d + 2` with `d = n + 1` (`W_PL_carleman.Csh`),
  -- `C₀ = 3K + 3C♯ + 2`, `l₁ = max (4C₀) (max (4K) 1)`, `τ₁ = max 5 (2C♯² + C♯)`.
  -- The pointwise inequality `W_PL_carleman.main_ptwise`
  --   `τ³ s⁻² e^{2τφ} v² + τ s⁻² e^{2τφ} |∇v|² ≤ 11 e^{2τφ} (P₀v)² - 11 div F + c τ div G`
  -- (`F = carlFlux`, `G = s⁻² w A∇w`) holds on `tsupport v ⊆ H n l`; off `tsupport v` all its
  -- terms vanish. `F` and `G` are `C¹` with compact support, so their divergences integrate to
  -- `0` (`integral_divergence_eq_zero`); integrating gives the estimate with `11 ≤ 15`.
  set Cs := W_PL_carleman.Csh n K with hCs
  have hCs0 : 0 ≤ Cs := by
    have := W_PL_carleman.trN_nonneg (n := n)
    simp only [hCs, W_PL_carleman.Csh]
    linarith
  refine ⟨3 * K + 3 * Cs + 2, max (4 * (3 * K + 3 * Cs + 2)) (max (4 * K) 1),
    max 5 (2 * Cs ^ 2 + Cs), by positivity, le_max_of_le_right (le_max_right _ _),
    le_max_left _ _, le_max_of_le_left (by norm_num), ?_⟩
  intro l hl A β γ hc τ hτ v hv hvc hvs
  set C₀ := 3 * K + 3 * Cs + 2 with hC₀def
  have hl4C : 4 * C₀ ≤ l := le_trans (le_max_left _ _) hl
  have hl4K : 4 * K ≤ l := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hl
  have hl1 : 1 ≤ l := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hl
  have hτ5 : 5 ≤ τ := le_trans (le_max_left _ _) hτ
  have hτC : 2 * Cs ^ 2 + Cs ≤ τ := le_trans (le_max_right _ _) hτ
  have hl0 : 0 ≤ l := by linarith
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hPt : ∀ y ∈ H n l, W_PL_carleman.PtHyp A K C₀ y := fun y hy =>
    { hK := hK
      hC₀ := hC₀0
      hs1 := by have : l < vcoord y := hy; linarith
      hsC := by have : l < vcoord y := hy; linarith
      hsK := by have : l < vcoord y := hy; linarith
      cd := hc.contDiffAt y hy
      symm := hc.symm y hy
      bA := hc.bound_A y hy
      bdA := hc.bound_dA y hy
      bd2A := hc.bound_d2A y hy }
  have hposH : ∀ y ∈ H n l, 0 < vcoord y := fun y hy => lt_of_le_of_lt hl0 hy
  set w := W_PL_carleman.wc C₀ τ v with hw
  set F := carlFlux (fun _ => (1 : ℝ)) A (W_PL_carleman.phi C₀) τ w with hF
  set G := W_PL_carleman.Gf A w with hG
  set E : Space n → ℝ := fun y => Real.exp (2 * τ * gw C₀ (vcoord y)) with hE
  set Wt : Space n → ℝ := fun y => (vcoord y ^ 2)⁻¹ with hWt
  set P : Space n → ℝ := fun y => divergence (fun z => A z (gradient v z)) y with hP
  -- the fields `F` and `G` are `C¹` with compact support
  have hF0 : ∀ z, z ∉ tsupport v → F z = 0 := fun z hz => W_PL_carleman.flux_eq_zero hz
  have hG0 : ∀ z, z ∉ tsupport v → G z = 0 := fun z hz => W_PL_carleman.Gf_eq_zero hz
  have hF1 : ContDiff ℝ 1 F := W_PL_carleman.contDiff_of_local hF0 hvs fun y hy =>
    W_PL_carleman.contDiffAt_flux (hposH y hy) (hc.contDiffAt y hy) hv
  have hG1 : ContDiff ℝ 1 G := W_PL_carleman.contDiff_of_local hG0 hvs fun y hy =>
    W_PL_carleman.contDiffAt_Gf (hposH y hy) (hc.contDiffAt y hy) hv
  have hFc : HasCompactSupport F := W_PL_carleman.hasCompactSupport_of hvc hF0
  have hGc : HasCompactSupport G := W_PL_carleman.hasCompactSupport_of hvc hG0
  have hdF0 : ∫ y, divergence F y = 0 := integral_divergence_eq_zero F hF1 hFc
  have hdG0 : ∫ y, divergence G y = 0 := integral_divergence_eq_zero G hG1 hGc
  have hdFi : Integrable (fun y => divergence F y) := W_PL_carleman.integrable_divergence hF1 hFc
  have hdGi : Integrable (fun y => divergence G y) := W_PL_carleman.integrable_divergence hG1 hGc
  -- integrability of the other terms (as in `carleman`)
  have hEc : ContinuousOn E (H n l) := continuousOn_weight C₀ τ hl0
  have hWc : ContinuousOn Wt (H n l) := continuousOn_inv_sq hl0
  have hgc : Continuous (gradient v) := continuous_gradient_of_contDiff hv
  have hPc : ContinuousOn P (H n l) := by
    intro y hy
    have hFy : ContDiffAt ℝ 1 (fun z => A z (gradient v z)) y :=
      ((hc.contDiffAt y hy).of_le (by norm_num)).clm_apply
        (F2.contDiffAt_gradient hv.contDiffAt (m := 1) (by norm_num))
    exact (continuousAt_divergence hFy).continuousWithinAt
  have hv0 : ∀ y, y ∉ tsupport v → v y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hg0 : ∀ y, y ∉ tsupport v → gradient v y = 0 :=
    fun y hy => (eventually_gradient_eq_zero hy).self_of_nhds
  have hP0' : ∀ y, y ∉ tsupport v → P y = 0 :=
    fun y hy => divergence_eq_zero_of_not_mem_tsupport A hy
  have hi1 : Integrable (fun y => Wt y * E y * v y ^ 2) :=
    integrable_of_tsupport (isOpen_H l) hvc hvs
      ((hWc.mul hEc).mul (hv.continuous.continuousOn.pow 2))
      (fun y hy => by simp [hv0 y hy])
  have hi2 : Integrable (fun y => Wt y * E y * ‖gradient v y‖ ^ 2) :=
    integrable_of_tsupport (isOpen_H l) hvc hvs
      ((hWc.mul hEc).mul ((hgc.norm.pow 2).continuousOn))
      (fun y hy => by simp [hg0 y hy])
  have hi3 : Integrable (fun y => E y * P y ^ 2) :=
    integrable_of_tsupport (isOpen_H l) hvc hvs (hEc.mul (hPc.pow 2))
      (fun y hy => by simp [hP0' y hy])
  -- the pointwise inequality
  have hpt : ∀ y, τ ^ 3 * (Wt y * E y * v y ^ 2) + τ * (Wt y * E y * ‖gradient v y‖ ^ 2)
      ≤ 11 * (E y * P y ^ 2) - 11 * divergence F y + (22 * Cs + 4) * τ * divergence G y := by
    intro y
    by_cases hy : y ∈ tsupport v
    · exact W_PL_carleman.main_ptwise (hPt y (hvs hy)) rfl hτ5 hτC hv
    · rw [hv0 y hy, hg0 y hy, hP0' y hy, W_PL_carleman.divergence_eq_zero_of hF0 hy,
        W_PL_carleman.divergence_eq_zero_of hG0 hy]
      simp
  -- integrate
  have hL : Integrable (fun y => τ ^ 3 * (Wt y * E y * v y ^ 2)
      + τ * (Wt y * E y * ‖gradient v y‖ ^ 2)) := (hi1.const_mul _).add (hi2.const_mul _)
  have hR1 : Integrable (fun y => 11 * (E y * P y ^ 2) - 11 * divergence F y) :=
    (hi3.const_mul _).sub (hdFi.const_mul _)
  have hR2 : Integrable (fun y => (22 * Cs + 4) * τ * divergence G y) := hdGi.const_mul _
  have hR : Integrable (fun y => 11 * (E y * P y ^ 2) - 11 * divergence F y
      + (22 * Cs + 4) * τ * divergence G y) := hR1.add hR2
  have hm := integral_mono hL hR hpt
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
    integral_add hR1 hR2, integral_sub (hi3.const_mul _) (hdFi.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, hdF0, hdG0] at hm
  have hI3 : 0 ≤ ∫ y, E y * P y ^ 2 :=
    integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  simp only [hE, hWt, hP] at hm hI3
  linarith

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

theorem abs_det_refl {x : Space n} (hx : x ≠ 0) :
    |LinearMap.det (refl x : Space n →ₗ[ℝ] Space n)| = 1 := by
  have h : (refl x : Space n →ₗ[ℝ] Space n) ∘ₗ (refl x : Space n →ₗ[ℝ] Space n)
      = LinearMap.id := by
    refine LinearMap.ext fun ξ => ?_
    simp [refl_refl hx]
  have hd : LinearMap.det (refl x : Space n →ₗ[ℝ] Space n)
      * LinearMap.det (refl x : Space n →ₗ[ℝ] Space n) = 1 := by
    rw [← LinearMap.det_comp, h, LinearMap.det_id]
  have h0 := abs_nonneg (LinearMap.det (refl x : Space n →ₗ[ℝ] Space n))
  have h2 : |LinearMap.det (refl x : Space n →ₗ[ℝ] Space n)|
      * |LinearMap.det (refl x : Space n →ₗ[ℝ] Space n)| = 1 := by
    rw [← abs_mul, hd, abs_one]
  nlinarith [sq_nonneg (|LinearMap.det (refl x : Space n →ₗ[ℝ] Space n)| - 1)]

theorem abs_det_fderiv_invMap {x : Space n} (hx : x ≠ 0) :
    abs (((‖x‖ ^ 2)⁻¹ • refl x).det) = ((‖x‖ ^ 2)⁻¹) ^ (n + 1) := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_smul, LinearMap.det_smul, abs_mul,
    abs_det_refl hx, mul_one, finrank_euclideanSpace_fin, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (‖x‖ ^ 2)⁻¹)]

theorem measurable_invMap : Measurable (invMap : Space n → Space n) :=
  ((continuous_norm.measurable.pow_const 2).inv).smul measurable_id

theorem invMap_surjective : Function.Surjective (invMap : Space n → Space n) :=
  fun y => ⟨invMap y, invMap_invMap y⟩

theorem invMap_injective : Function.Injective (invMap : Space n → Space n) :=
  Function.LeftInverse.injective invMap_invMap

theorem invMap_zero : invMap (0 : Space n) = 0 := by simp [invMap]

/-- Integrability of `v² + |Dv|²` on `halfBall n r` for `r < R`. -/
theorem integrableOn_halfBall_energy (S : HalfBallSolution n) {r : ℝ} (hr : r < S.R) :
    IntegrableOn (fun x => S.v x ^ 2 + ‖S.Dv x‖ ^ 2) (halfBall n r) := by
  set K : Set (Space n) := {x | ‖x‖ ≤ r ∧ 0 ≤ vcoord x} with hK
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const F1.continuous_vcoord)
    · refine (Metric.isBounded_closedBall (x := (0 : Space n)) (r := r)).subset fun x hx => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.1
  have hKs : K ⊆ closedHalfBall n S.R := fun x hx => ⟨lt_of_le_of_lt hx.1 hr, hx.2⟩
  have hcont : ContinuousOn (fun x => S.v x ^ 2 + ‖S.Dv x‖ ^ 2) K :=
    ((S.v_continuousOn.mono hKs).pow 2).add ((S.Dv_continuousOn.mono hKs).norm.pow 2)
  exact (hcont.integrableOn_compact hKc).mono_set fun x hx => ⟨hx.1.le, hx.2.le⟩

/-- **Decay on shells** for `U = v ∘ Φ`: the change of variables `x = Φ(y)` in the decay
hypothesis. -/
theorem shell_decay (S : HalfBallSolution n)
    (hdecay : ∀ N : ℝ, ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 S.R,
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cn * Real.exp (-N / r))
    {l : ℝ} (hl : 1 ≤ l) (hlR : 1 / l < S.R) :
    ∀ N : ℝ, ∃ CN M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
      ∫ y in shell n l M, ((S.v ∘ invMap) y ^ 2 + ‖gradient (S.v ∘ invMap) y‖ ^ 2)
        ≤ CN * Real.exp (-N * M) := by
  intro N
  have hl0 : 0 < l := by linarith
  have hR := S.R_pos
  obtain ⟨C', hC'⟩ := hdecay (2 * N + 4)
  set k : ℕ := 2 * (n + 1) with hk
  refine ⟨max C' 0 * (k.factorial : ℝ), max 1 (2 / S.R + 1), fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
  have hMR : 2 / S.R + 1 ≤ M := le_trans (le_max_right _ _) hM
  have hM0 : 0 < M := by linarith
  have h2M : 2 / M < S.R := by
    rw [div_lt_iff₀ hM0]
    have : 2 / S.R < M := by linarith
    rw [div_lt_iff₀ hR] at this
    linarith
  set G : Space n → ℝ := fun y => (S.v ∘ invMap) y ^ 2 + ‖gradient (S.v ∘ invMap) y‖ ^ 2 with hG
  set T : Set (Space n) := invMap ⁻¹' shell n l M with hT
  have hTm : MeasurableSet T := (isClosed_shell l M).measurableSet.preimage measurable_invMap
  have hTimg : invMap '' T = shell n l M := Set.image_preimage_eq _ invMap_surjective
  have hT0 : ∀ x ∈ T, x ≠ 0 := by
    intro x hx h
    have : invMap x ∈ shell n l M := hx
    rw [h, invMap_zero] at this
    have h1 := this.1
    simp [vcoord] at h1
    linarith
  -- change of variables
  have hcov : ∫ y in shell n l M, G y
      = ∫ x in T, abs (((‖x‖ ^ 2)⁻¹ • refl x).det) • G (invMap x) := by
    rw [← hTimg]
    exact integral_image_eq_integral_abs_det_fderiv_smul volume hTm
      (fun x hx => (hasFDerivAt_invMap (hT0 x hx)).hasFDerivWithinAt)
      invMap_injective.injOn G
  -- points of `T`
  have hr : (0 : ℝ) < 1 / (2 * l) := by positivity
  have hTmem : ∀ x ∈ T, x ∈ halfBall n S.R ∧ x ∈ halfBall n (2 / M)
      ∧ 1 / (2 * M) ≤ ‖x‖ ∧ ‖x‖ ≤ 1 / M := by
    intro x hx
    have hsh : invMap x ∈ shell n l M := hx
    have hHl : invMap x ∈ H n (1 / (2 * (1 / (2 * l)))) := by
      have : 1 / (2 * (1 / (2 * l))) = l := by field_simp
      rw [this]
      show l < vcoord (invMap x)
      linarith [hsh.1]
    have hball := invMap_mem_ball hr hHl
    rw [invMap_invMap] at hball
    have hhb := ball_subset_halfBall hr hball
    have h2l : 2 * (1 / (2 * l)) = 1 / l := by field_simp
    rw [h2l] at hhb
    have hx0 := hT0 x hx
    have hN : ‖invMap x‖ = ‖x‖⁻¹ := norm_invMap x
    have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hn1 : M ≤ ‖x‖⁻¹ := hN ▸ hsh.2.1
    have hn2 : ‖x‖⁻¹ ≤ 2 * M := hN ▸ hsh.2.2
    have hb1 : 1 / (2 * M) ≤ ‖x‖ := by
      rw [div_le_iff₀ (by positivity)]
      calc 1 = ‖x‖⁻¹ * ‖x‖ := (inv_mul_cancel₀ hxp.ne').symm
        _ ≤ (2 * M) * ‖x‖ := mul_le_mul_of_nonneg_right hn2 hxp.le
        _ = ‖x‖ * (2 * M) := by ring
    have hb2 : ‖x‖ ≤ 1 / M := by
      rw [le_div_iff₀ hM0]
      calc ‖x‖ * M ≤ ‖x‖ * ‖x‖⁻¹ := mul_le_mul_of_nonneg_left hn1 hxp.le
        _ = 1 := mul_inv_cancel₀ hxp.ne'
    refine ⟨halfBall_mono hlR.le hhb, ⟨?_, hhb.2⟩, hb1, hb2⟩
    calc ‖x‖ ≤ 1 / M := hb2
      _ < 2 / M := by gcongr; norm_num
  -- pointwise bound on `T`
  have hpt : ∀ x ∈ T, abs (((‖x‖ ^ 2)⁻¹ • refl x).det) • G (invMap x)
      ≤ (2 * M) ^ k * (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) := by
    intro x hx
    obtain ⟨hxR, -, hb1, hb2⟩ := hTmem x hx
    have hx0 := hT0 x hx
    have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hvx : ContDiffAt ℝ 2 S.v x :=
      S.v_contDiffOn.contDiffAt ((isOpen_halfBall S.R).mem_nhds hxR)
    have hgrad : gradient (S.v ∘ invMap) (invMap x)
        = (‖invMap x‖ ^ 2)⁻¹ • refl (invMap x) (gradient S.v x) := by
      have := gradient_comp_invMap S.v (invMap_ne_zero hx0)
        (by rw [invMap_invMap]; exact hvx.differentiableAt (by simp))
      rw [invMap_invMap] at this
      exact this
    have hnorm : ‖gradient (S.v ∘ invMap) (invMap x)‖ = ‖x‖ ^ 2 * ‖S.Dv x‖ := by
      rw [hgrad, norm_smul, norm_refl_apply (invMap_ne_zero hx0), norm_invMap,
        S.gradient_eq x hxR, Real.norm_eq_abs, abs_of_pos (by positivity), inv_pow, inv_inv]
    have hGx : G (invMap x) = S.v x ^ 2 + (‖x‖ ^ 2 * ‖S.Dv x‖) ^ 2 := by
      simp only [hG, Function.comp_apply, invMap_invMap, hnorm]
    rw [abs_det_fderiv_invMap hx0, hGx, smul_eq_mul]
    have hxinv : (‖x‖ ^ 2)⁻¹ ≤ (2 * M) ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      have : 1 ≤ (2 * M) * ‖x‖ := by
        rw [div_le_iff₀ (by positivity)] at hb1
        linarith
      nlinarith
    have hpow : ((‖x‖ ^ 2)⁻¹) ^ (n + 1) ≤ (2 * M) ^ k := by
      rw [hk, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hxinv _
    have hx4 : (‖x‖ ^ 2 * ‖S.Dv x‖) ^ 2 ≤ ‖S.Dv x‖ ^ 2 := by
      have hx1 : ‖x‖ ≤ 1 := hb2.trans (by rw [div_le_one hM0]; exact hM1)
      have : ‖x‖ ^ 2 ≤ 1 := by nlinarith
      have h0 : 0 ≤ ‖x‖ ^ 2 := by positivity
      calc (‖x‖ ^ 2 * ‖S.Dv x‖) ^ 2 = (‖x‖ ^ 2) ^ 2 * ‖S.Dv x‖ ^ 2 := by ring
        _ ≤ 1 * ‖S.Dv x‖ ^ 2 := by gcongr; nlinarith
        _ = _ := one_mul _
    exact mul_le_mul hpow (by linarith) (by positivity) (by positivity)
  -- comparison with the half-ball integral
  have hint := integrableOn_halfBall_energy S h2M
  have hTsub : T ⊆ halfBall n (2 / M) := fun x hx => (hTmem x hx).2.1
  have hbound : ∫ x in T, abs (((‖x‖ ^ 2)⁻¹ • refl x).det) • G (invMap x)
      ≤ (2 * M) ^ k * ∫ x in halfBall n (2 / M), (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) := by
    rw [← integral_const_mul]
    calc ∫ x in T, abs (((‖x‖ ^ 2)⁻¹ • refl x).det) • G (invMap x)
        ≤ ∫ x in T, (2 * M) ^ k * (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall fun x => by positivity
          · exact ((hint.mono_set hTsub).const_mul _)
          · exact (ae_restrict_iff' hTm).mpr (Eventually.of_forall hpt)
      _ ≤ ∫ x in halfBall n (2 / M), (2 * M) ^ k * (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) :=
          setIntegral_mono_set (hint.const_mul _)
            (Eventually.of_forall fun x => by positivity)
            (Filter.eventuallySubset_iff.2 (Eventually.of_forall fun x hx => hTsub hx))
  have hdec' : ∫ x in halfBall n (2 / M), (S.v x ^ 2 + ‖S.Dv x‖ ^ 2)
      ≤ max C' 0 * Real.exp (-(N + 2) * M) := by
    have h1 := hC' (2 / M) (show 2 / M ∈ Set.Ioo 0 S.R from ⟨by positivity, h2M⟩)
    have hexp : -(2 * N + 4) / (2 / M) = -(N + 2) * M := by
      field_simp
      ring
    rw [hexp] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  -- absorb the polynomial factor
  have hfac : (2 * M) ^ k ≤ (k.factorial : ℝ) * Real.exp (2 * M) := by
    have := Real.pow_div_factorial_le_exp (2 * M) (by positivity) k
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hI0 : 0 ≤ ∫ x in halfBall n (2 / M), (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) :=
    setIntegral_nonneg (isOpen_halfBall _).measurableSet (fun x _ => by positivity)
  rw [hcov]
  calc _ ≤ (2 * M) ^ k * ∫ x in halfBall n (2 / M), (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) := hbound
    _ ≤ ((k.factorial : ℝ) * Real.exp (2 * M)) * (max C' 0 * Real.exp (-(N + 2) * M)) :=
        mul_le_mul hfac hdec' hI0 (by positivity)
    _ = max C' 0 * (k.factorial : ℝ) * Real.exp (-N * M) := by
        rw [show -N * M = 2 * M + -(N + 2) * M by ring, Real.exp_add]
        ring

/-- The proof of Proposition PL (the contract theorem `HalfBallSolution.vanish_of_superexp`). -/
theorem vanish_of_superexp_aux (S : HalfBallSolution n)
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

end PL

/-- **Proposition PL.** Interior decay faster than every `e^{-N/r}` forces the solution to vanish
on a ball tangent to the flat boundary at `0`. -/
theorem HalfBallSolution.vanish_of_superexp (S : HalfBallSolution n)
    (hdecay : ∀ N : ℝ, ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 S.R,
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cn * Real.exp (-N / r)) :
    ∃ r' > 0, ∀ x ∈ Metric.ball (r' • ed n) r', S.v x = 0 :=
  PL.vanish_of_superexp_aux S hdecay

end MazyaRefinedCauchy
