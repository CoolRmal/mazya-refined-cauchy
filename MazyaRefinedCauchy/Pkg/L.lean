module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F4
public import MazyaRefinedCauchy.Pkg.F6

@[expose] public section

/-!
# Work package L

The theorems stated in this file are the frozen contract of package L (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory
open scoped FourierTransform

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package L: the Laplacian, quasianalyticity (Lemma DC) -/

/-- The inner unit normal of the graph of `Γ` at `0`. -/
noncomputable def innerNormalZero (Γ : (Fin n → ℝ) → ℝ) : Space n :=
  -outerNormal Γ 0

namespace LPkg

/-! ### Tangent balls -/

/-- The horizontal coordinates `x ↦ (x (castSucc i))ᵢ`, as a continuous linear map. -/
noncomputable def hproj (n : ℕ) : Space n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i))

theorem hproj_apply (x : Space n) : hproj n x = fun i => x (Fin.castSucc i) := rfl

theorem norm_hproj_le (x : Space n) : ‖hproj n x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa [hproj_apply] using PiLp.norm_apply_le x (Fin.castSucc i)

theorem graphFn_eq (Γ : (Fin n → ℝ) → ℝ) :
    graphFn Γ = fun x => Γ (hproj n x) - EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n) x := rfl

theorem hasFDerivAt_graphFn {Γ : (Fin n → ℝ) → ℝ} {x : Space n}
    (hΓ : DifferentiableAt ℝ Γ (hproj n x)) :
    HasFDerivAt (graphFn Γ)
      ((fderiv ℝ Γ (hproj n x)).comp (hproj n) - EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)) x := by
  rw [graphFn_eq]
  exact (hΓ.hasFDerivAt.comp x (hproj n).hasFDerivAt).sub
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).hasFDerivAt

theorem inner_gradient_graphFn {Γ : (Fin n → ℝ) → ℝ} {x : Space n}
    (hΓ : DifferentiableAt ℝ Γ (hproj n x)) (v : Space n) :
    ⟪gradient (graphFn Γ) x, v⟫_ℝ = fderiv ℝ Γ (hproj n x) (hproj n v) - v (Fin.last n) := by
  rw [gradient, toDual_symm_apply, (hasFDerivAt_graphFn hΓ).fderiv]
  rfl

theorem hproj_ed : hproj n (ed n) = 0 := by
  funext i
  simp [hproj_apply, ed, Fin.castSucc_ne_last]

/-- Second order Taylor bound at `0` for a smooth function. -/
theorem taylor_two {m : ℕ} {Γ : (Fin m → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ) :
    ∃ δ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Fin m → ℝ, ‖z‖ < δ →
      |Γ z - Γ 0 - fderiv ℝ Γ 0 z| ≤ K * ‖z‖ ^ 2 := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ Γ) := hΓ.fderiv_right (by simp)
  have h1' : ContDiffAt ℝ 1 (fderiv ℝ Γ) 0 := (h1.of_le (by simp)).contDiffAt
  obtain ⟨K, t, ht, hK⟩ := h1'.exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  have hdΓ : Differentiable ℝ Γ := hΓ.differentiable (by simp)
  refine ⟨δ, hδ, K, K.2, fun z hz => ?_⟩
  have hdiff : ∀ w, DifferentiableAt ℝ (fun w => Γ w - fderiv ℝ Γ 0 w) w := fun w =>
    (hdΓ w).sub (fderiv ℝ Γ 0).differentiableAt
  have hfd : ∀ w, fderiv ℝ (fun w => Γ w - fderiv ℝ Γ 0 w) w = fderiv ℝ Γ w - fderiv ℝ Γ 0 := by
    intro w
    rw [fderiv_fun_sub (hdΓ w) (fderiv ℝ Γ 0).differentiableAt, ContinuousLinearMap.fderiv]
  have hsub : Metric.closedBall (0 : Fin m → ℝ) ‖z‖ ⊆ t := fun w hw => hball (by
    simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at hw ⊢; linarith)
  have hz0 : z ∈ Metric.closedBall (0 : Fin m → ℝ) ‖z‖ := by simp
  have h00 : (0 : Fin m → ℝ) ∈ Metric.closedBall (0 : Fin m → ℝ) ‖z‖ := by simp
  have key := (convex_closedBall (0 : Fin m → ℝ) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
    (f := fun w => Γ w - fderiv ℝ Γ 0 w) (C := K * ‖z‖) (fun w _ => hdiff w) (fun w hw => ?_)
    h00 hz0
  · simp only [map_zero, sub_zero] at key
    rw [Real.norm_eq_abs] at key
    calc |Γ z - Γ 0 - fderiv ℝ Γ 0 z| = |Γ z - fderiv ℝ Γ 0 z - Γ 0| := by ring_nf
      _ ≤ K * ‖z‖ * ‖z‖ := key
      _ = K * ‖z‖ ^ 2 := by ring
  · rw [hfd]
    have hl := hK.dist_le_mul w (hsub hw) 0 (hsub h00)
    rw [dist_eq_norm, dist_zero_right] at hl
    calc ‖fderiv ℝ Γ w - fderiv ℝ Γ 0‖ ≤ K * ‖w‖ := hl
      _ ≤ K * ‖z‖ := mul_le_mul_of_nonneg_left (by simpa using hw) K.2

end LPkg

open LPkg in
/-- Balls tangent to the boundary at `0` from inside lie in the domain. -/
theorem tangent_ball_subset_domain (hn : 0 < n) (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ)
    (hΓ0 : Γ 0 = 0) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R₀ > 0, ∀ R ∈ Set.Ioc 0 R₀, Metric.ball (R • innerNormalZero Γ) R ⊆ domain Γ ρ := by
  obtain ⟨δ, hδ, K, hK, htay⟩ := taylor_two hΓ
  set G := gradient (graphFn Γ) 0 with hG
  have hdΓ : ∀ x : Space n, DifferentiableAt ℝ Γ (hproj n x) := fun x =>
    hΓ.differentiable (by simp) _
  have hG_inner : ∀ v : Space n, ⟪G, v⟫_ℝ = fderiv ℝ Γ 0 (hproj n v) - v (Fin.last n) := by
    intro v
    have := inner_gradient_graphFn (hdΓ 0) v
    simp only [map_zero] at this
    rw [hG]
    exact this
  have hGed : ⟪G, ed n⟫_ℝ = -1 := by
    rw [hG_inner, hproj_ed]
    simp [ed]
  have hG1 : 1 ≤ ‖G‖ := by
    have h := abs_real_inner_le_norm G (ed n)
    rw [hGed] at h
    have hed : ‖ed n‖ = 1 := by simp [ed]
    rw [hed] at h
    simpa using h
  have hGpos : 0 < ‖G‖ := lt_of_lt_of_le one_pos hG1
  have hν : innerNormalZero Γ = -(‖G‖⁻¹ • G) := rfl
  have hνnorm : ‖innerNormalZero Γ‖ = 1 := by
    rw [hν, norm_neg, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hGpos.ne']
  refine ⟨min (ρ / 2) (min (δ / 2) (1 / (2 * K + 2))), ?_, ?_⟩
  · refine lt_min (by linarith) (lt_min (by linarith) ?_)
    have : 0 < 2 * K + 2 := by linarith
    positivity
  rintro R ⟨hR0, hR⟩ x hx
  have hRρ : R ≤ ρ / 2 := le_trans hR (min_le_left _ _)
  have hRδ : R ≤ δ / 2 := le_trans hR (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRK : R ≤ 1 / (2 * K + 2) := le_trans hR (le_trans (min_le_right _ _) (min_le_right _ _))
  rw [Metric.mem_ball, dist_eq_norm] at hx
  set ν := innerNormalZero Γ with hνdef
  have hxnorm : ‖x‖ < 2 * R := by
    calc ‖x‖ = ‖(x - R • ν) + R • ν‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - R • ν‖ + ‖R • ν‖ := norm_add_le _ _
      _ < R + R := by
        rw [norm_smul, hνnorm, Real.norm_eq_abs, abs_of_pos hR0, mul_one]; linarith
      _ = 2 * R := by ring
  -- the defining inequality of the ball
  have hsq : ‖x‖ ^ 2 < 2 * R * ⟪x, ν⟫_ℝ := by
    have h1 : ‖x - R • ν‖ ^ 2 < R ^ 2 := by
      have := norm_nonneg (x - R • ν)
      nlinarith
    rw [@norm_sub_sq_real, norm_smul, hνnorm, Real.norm_eq_abs, abs_of_pos hR0,
      inner_smul_right] at h1
    nlinarith
  have hxν : ⟪x, ν⟫_ℝ = -(‖G‖⁻¹ * ⟪G, x⟫_ℝ) := by
    rw [hν, inner_neg_right, inner_smul_right, real_inner_comm]
  have hGx : ⟪G, x⟫_ℝ < -(‖x‖ ^ 2 / (2 * R)) := by
    rw [hxν] at hsq
    have h2 : ‖G‖ * ‖x‖ ^ 2 < -(2 * R) * ⟪G, x⟫_ℝ := by
      have := mul_lt_mul_of_pos_left hsq hGpos
      have e : ‖G‖ * (2 * R * -(‖G‖⁻¹ * ⟪G, x⟫_ℝ)) = -(2 * R) * ⟪G, x⟫_ℝ := by
        field_simp
      linarith
    have h3 : ‖x‖ ^ 2 ≤ ‖G‖ * ‖x‖ ^ 2 := by
      have := sq_nonneg ‖x‖
      nlinarith
    have h4 : ‖x‖ ^ 2 < -(2 * R) * ⟪G, x⟫_ℝ := lt_of_le_of_lt h3 h2
    have e2 : -(‖x‖ ^ 2 / (2 * R)) = -‖x‖ ^ 2 / (2 * R) := by ring
    rw [e2, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * R)]
    linarith
  refine ⟨by linarith, ?_⟩
  -- the graph inequality
  have hz : ‖hproj n x‖ < δ := lt_of_le_of_lt (norm_hproj_le x) (by linarith)
  have hT := htay (hproj n x) hz
  rw [hΓ0] at hT
  have hT' : Γ (hproj n x) ≤ fderiv ℝ Γ 0 (hproj n x) + K * ‖x‖ ^ 2 := by
    have h1 := (abs_le.1 hT).2
    have h2 : ‖hproj n x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have := norm_hproj_le x
      have := norm_nonneg (hproj n x)
      nlinarith
    nlinarith
  have hKR : K * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 / (2 * R) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * R)]
    have h5 : K * (2 * R) ≤ 1 := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * K + 2)] at hRK
      nlinarith
    have := sq_nonneg ‖x‖
    nlinarith
  have hGx' := hG_inner x
  show Γ (fun i => x (Fin.castSucc i)) - x (Fin.last n) < 0
  have : Γ (fun i => x (Fin.castSucc i)) = Γ (hproj n x) := rfl
  rw [this]
  linarith

namespace LPkg

open Laplacian

/-! ### The Kelvin transform -/

/-- The orthonormal basis used for all trace computations. -/
noncomputable abbrev bE (n : ℕ) : OrthonormalBasis (Fin (n + 1)) ℝ (Space n) :=
  EuclideanSpace.basisFun (Fin (n + 1)) ℝ

theorem sum_inner_smul_bE (y : Space n) : ∑ i, ⟪y, bE n i⟫_ℝ • bE n i = y := by
  conv_rhs => rw [← (bE n).sum_repr' y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm]

theorem sum_inner_sq_bE (y : Space n) : ∑ i, ⟪y, bE n i⟫_ℝ ^ 2 = ‖y‖ ^ 2 :=
  OrthonormalBasis.sum_sq_inner_left (bE n) y

theorem sum_norm_sq_bE : ∑ i : Fin (n + 1), ‖bE n i‖ ^ 2 = (n + 1 : ℝ) := by
  simp

/-- The Laplacian as a sum of iterated directional derivatives.
Adapted from TauCeti, `TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`. -/
theorem laplacian_eq_sum_dir {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    Δ f x = ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (bE n i)) x (bE n i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (bE n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hf (differentiableAt_const _)]
  simp

theorem laplacian_eq_sum_fderiv2 (f : Space n → ℝ) (x : Space n) :
    Δ f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (bE n i) (bE n i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (bE n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  rfl

/-- **The Leibniz rule for the Laplacian.**
Adapted from TauCeti, `TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`. -/
theorem laplacian_mul' {f g : Space n → ℝ} {x : Space n} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y ↦ f y * g y) x = f x * Δ g x +
      2 * ∑ i, fderiv ℝ f x (bE n i) * fderiv ℝ g x (bE n i) + g x * Δ f x := by
  have hfd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hfg : fderiv ℝ (fun y ↦ f y * g y) =ᶠ[𝓝 x]
      fun y ↦ f y • fderiv ℝ g y + g y • fderiv ℝ f y := by
    filter_upwards [hfd, hgd] with y hfy hgy
    exact fderiv_mul hfy hgy
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hterm : ∀ v, iteratedFDeriv ℝ 2 (fun y ↦ f y * g y) x ![v, v] =
      f x * iteratedFDeriv ℝ 2 g x ![v, v] + 2 * (fderiv ℝ f x v * fderiv ℝ g x v) +
        g x * iteratedFDeriv ℝ 2 f x ![v, v] := by
    intro v
    have h1 : DifferentiableAt ℝ (fun y ↦ f y • fderiv ℝ g y) x := hfd.self_of_nhds.smul hg'
    have h2 : DifferentiableAt ℝ (fun y ↦ g y • fderiv ℝ f y) x := hgd.self_of_nhds.smul hf'
    rw [iteratedFDeriv_two_apply, hfg.fderiv_eq, fderiv_fun_add h1 h2,
      fderiv_fun_smul hfd.self_of_nhds hg', fderiv_fun_smul hgd.self_of_nhds hf',
      iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ (bE n)) x,
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f (bE n)) x,
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis g (bE n)) x]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]

end LPkg

namespace LPkg

open Laplacian

/-- `z ↦ (‖z‖²)⁻¹`. -/
theorem hasFDerivAt_sinv {z : Space n} (hz : z ≠ 0) :
    HasFDerivAt (fun z : Space n => (‖z‖ ^ 2)⁻¹)
      ((-((‖z‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ z)) z :=
  (hasDerivAt_inv (pow_ne_zero 2 (norm_ne_zero_iff.2 hz))).comp_hasFDerivAt z
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt

theorem sinvD_apply (z v : Space n) :
    ((-((‖z‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ z)) v = -(2 * ((‖z‖ ^ 2)⁻¹) ^ 2 * ⟪z, v⟫_ℝ) := by
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, inv_pow,
    two_smul, ContinuousLinearMap.add_apply]
  ring

/-- The inversion `z ↦ z/‖z‖²`. -/
noncomputable def invMap (z : Space n) : Space n := (‖z‖ ^ 2)⁻¹ • z

theorem invMap_eq (z : Space n) : invMap z = ‖z‖⁻¹ ^ 2 • z := by rw [invMap, inv_pow]

/-- The derivative of the inversion. -/
noncomputable def invMapD (z : Space n) : Space n →L[ℝ] Space n :=
  (‖z‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ (Space n) -
    (2 * ((‖z‖ ^ 2)⁻¹) ^ 2) • (innerSL ℝ z).smulRight z

theorem invMapD_apply (z v : Space n) :
    invMapD z v = (‖z‖ ^ 2)⁻¹ • v - (2 * ((‖z‖ ^ 2)⁻¹) ^ 2 * ⟪z, v⟫_ℝ) • z := by
  simp [invMapD, smul_smul]

theorem hasFDerivAt_invMap {z : Space n} (hz : z ≠ 0) : HasFDerivAt invMap (invMapD z) z := by
  have h := (hasFDerivAt_sinv hz).smul (hasFDerivAt_id z)
  convert h using 1
  · funext v; rfl
  · ext1 v
    rw [invMapD_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      sinvD_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, id]
    module

theorem invMapD_apply_self (z : Space n) (hz : z ≠ 0) : invMapD z z = -((‖z‖ ^ 2)⁻¹ • z) := by
  rw [invMapD_apply, real_inner_self_eq_norm_sq]
  have h : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hz)
  have e : 2 * ((‖z‖ ^ 2)⁻¹) ^ 2 * ‖z‖ ^ 2 = 2 * (‖z‖ ^ 2)⁻¹ := by field_simp
  rw [e]
  module

/-- The second directional derivative of the inversion. -/
theorem hasFDerivAt_invMapD_apply {y : Space n} (hy : y ≠ 0) (v : Space n) :
    ∃ G : Space n →L[ℝ] Space n, HasFDerivAt (fun z => invMapD z v) G y ∧
      G v = (-(4 * ((‖y‖ ^ 2)⁻¹) ^ 2 * ⟪y, v⟫_ℝ)) • v +
        (8 * ((‖y‖ ^ 2)⁻¹) ^ 3 * ⟪y, v⟫_ℝ ^ 2 - 2 * ((‖y‖ ^ 2)⁻¹) ^ 2 * ‖v‖ ^ 2) • y := by
  have hs := hasFDerivAt_sinv hy
  have hs2 := hs.pow 2
  have hin : HasFDerivAt (fun z : Space n => ⟪z, v⟫_ℝ) (innerSL ℝ v) y := by
    have := (innerSL ℝ v).hasFDerivAt (x := y)
    convert this using 1
    funext z
    simp [real_inner_comm]
  have h3 := ((hs2.const_mul (2 : ℝ)).mul hin).smul (hasFDerivAt_id y)
  have key := (hs.smul_const v).sub h3
  have key2 := key.congr_of_eventuallyEq (f₁ := fun z => invMapD z v)
    (Filter.Eventually.of_forall fun z => by
      show invMapD z v = _
      rw [invMapD_apply]; rfl)
  refine ⟨_, key2, ?_⟩
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, id, smul_eq_mul,
      Pi.mul_apply]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, real_inner_self_eq_norm_sq, real_inner_comm v y]
    module

end LPkg

namespace LPkg

open Laplacian

theorem contDiffAt_invMap {y : Space n} (hy : y ≠ 0) {m : WithTop ℕ∞} :
    ContDiffAt ℝ m invMap y := by
  have h1 : ContDiffAt ℝ m (fun z : Space n => ‖z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt
  have h2 : ContDiffAt ℝ m (fun z : Space n => (‖z‖ ^ 2)⁻¹) y :=
    h1.inv (pow_ne_zero 2 (norm_ne_zero_iff.2 hy))
  exact h2.smul contDiffAt_id

theorem invMapD_apply' (z v : Space n) :
    invMapD z v = (‖z‖ ^ 2)⁻¹ • v + ((-(2 * ((‖z‖ ^ 2)⁻¹) ^ 2)) * ⟪z, v⟫_ℝ) • z := by
  rw [invMapD_apply]
  module

/-- Trace of a bilinear form conjugated by `b ↦ a b + c ⟪y, b⟫ y`. -/
theorem sum_bilin_conj (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) (y : Space n) (a c : ℝ) :
    ∑ i, H (a • bE n i + (c * ⟪y, bE n i⟫_ℝ) • y) (a • bE n i + (c * ⟪y, bE n i⟫_ℝ) • y) =
      a ^ 2 * ∑ i, H (bE n i) (bE n i) + (2 * a * c + c ^ 2 * ‖y‖ ^ 2) * H y y := by
  have h1 : ∑ i, ⟪y, bE n i⟫_ℝ * H (bE n i) y = H y y := by
    have := congrArg (fun w => H w y) (sum_inner_smul_bE y)
    simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at this
    exact this
  have h2 : ∑ i, ⟪y, bE n i⟫_ℝ * H y (bE n i) = H y y := by
    have := congrArg (fun w => H y w) (sum_inner_smul_bE y)
    simp only [map_sum, map_smul, smul_eq_mul] at this
    exact this
  have h3 := sum_inner_sq_bE y
  have hexp : ∀ i, H (a • bE n i + (c * ⟪y, bE n i⟫_ℝ) • y)
      (a • bE n i + (c * ⟪y, bE n i⟫_ℝ) • y) =
      a ^ 2 * H (bE n i) (bE n i) + (a * c) * (⟪y, bE n i⟫_ℝ * H (bE n i) y) +
      (a * c) * (⟪y, bE n i⟫_ℝ * H y (bE n i)) + (c ^ 2 * H y y) * ⟪y, bE n i⟫_ℝ ^ 2 := by
    intro i
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2, h3]
  ring

/-- **Laplacian of `u ∘ invMap`.** -/
theorem laplacian_comp_invMap {u : Space n → ℝ} {y : Space n} (hy : y ≠ 0)
    (hu : ContDiffAt ℝ 2 u (invMap y)) :
    Δ (fun z => u (invMap z)) y = ((‖y‖ ^ 2)⁻¹) ^ 2 * Δ u (invMap y) +
      (2 - 2 * n) * ((‖y‖ ^ 2)⁻¹) ^ 2 * fderiv ℝ u (invMap y) y := by
  set s := (‖y‖ ^ 2)⁻¹ with hs_def
  have hy2 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have hsy : s * ‖y‖ ^ 2 = 1 := inv_mul_cancel₀ hy2
  have hΦ : ContDiffAt ℝ 2 invMap y := contDiffAt_invMap hy
  have hw : ContDiffAt ℝ 2 (fun z => u (invMap z)) y := hu.comp y hΦ
  have hw' : DifferentiableAt ℝ (fderiv ℝ (fun z => u (invMap z))) y :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : ∀ᶠ z in 𝓝 y, z ≠ 0 ∧ DifferentiableAt ℝ u (invMap z) := by
    have h1 : ∀ᶠ z in 𝓝 y, z ≠ 0 := isOpen_ne.mem_nhds hy
    have h2 : ∀ᶠ x in 𝓝 (invMap y), DifferentiableAt ℝ u x :=
      (hu.eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)
    exact h1.and (hΦ.continuousAt.eventually h2)
  have hfd : ∀ v, (fun z => fderiv ℝ (fun z => u (invMap z)) z v) =ᶠ[𝓝 y]
      fun z => fderiv ℝ u (invMap z) (invMapD z v) := by
    intro v
    filter_upwards [hev] with z hz
    show fderiv ℝ (u ∘ invMap) z v = _
    rw [(hz.2.hasFDerivAt.comp z (hasFDerivAt_invMap hz.1)).fderiv]
    rfl
  have hu2 : DifferentiableAt ℝ (fderiv ℝ u) (invMap y) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun z => fderiv ℝ u (invMap z))
      ((fderiv ℝ (fderiv ℝ u) (invMap y)).comp (invMapD y)) y :=
    hu2.hasFDerivAt.comp y (hasFDerivAt_invMap hy)
  have hterm : ∀ v, fderiv ℝ (fun z => fderiv ℝ (fun z => u (invMap z)) z v) y v =
      fderiv ℝ u (invMap y) ((-(4 * s ^ 2 * ⟪y, v⟫_ℝ)) • v +
        (8 * s ^ 3 * ⟪y, v⟫_ℝ ^ 2 - 2 * s ^ 2 * ‖v‖ ^ 2) • y) +
      fderiv ℝ (fderiv ℝ u) (invMap y) (invMapD y v) (invMapD y v) := by
    intro v
    obtain ⟨G, hG, hGv⟩ := hasFDerivAt_invMapD_apply hy v
    rw [(hfd v).fderiv_eq, (hc.clm_apply hG).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.flip_apply]
    rw [hGv]
  rw [laplacian_eq_sum_dir hw']
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← map_sum]
  have hsum1 : ∑ i, ((-(4 * s ^ 2 * ⟪y, bE n i⟫_ℝ)) • bE n i +
      (8 * s ^ 3 * ⟪y, bE n i⟫_ℝ ^ 2 - 2 * s ^ 2 * ‖bE n i‖ ^ 2) • y) =
      ((2 - 2 * n) * s ^ 2) • y := by
    rw [Finset.sum_add_distrib, ← Finset.sum_smul]
    have e1 : ∑ i, (-(4 * s ^ 2 * ⟪y, bE n i⟫_ℝ)) • bE n i =
        (-(4 * s ^ 2)) • ∑ i, ⟪y, bE n i⟫_ℝ • bE n i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      ring_nf
    have e2 : ∑ i, (8 * s ^ 3 * ⟪y, bE n i⟫_ℝ ^ 2 - 2 * s ^ 2 * ‖bE n i‖ ^ 2) =
        8 * s ^ 3 * ‖y‖ ^ 2 - 2 * s ^ 2 * (n + 1) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_inner_sq_bE,
        sum_norm_sq_bE]
    rw [e1, e2, sum_inner_smul_bE]
    have e3 : 8 * s ^ 3 * ‖y‖ ^ 2 = 8 * s ^ 2 := by
      have : s ^ 3 * ‖y‖ ^ 2 = s ^ 2 * (s * ‖y‖ ^ 2) := by ring
      rw [mul_assoc, this, hsy, mul_one]
    rw [e3, ← add_smul]
    congr 1
    ring
  have hsum2 : ∑ i, fderiv ℝ (fderiv ℝ u) (invMap y) (invMapD y (bE n i)) (invMapD y (bE n i)) =
      s ^ 2 * Δ u (invMap y) := by
    simp_rw [invMapD_apply']
    rw [sum_bilin_conj, laplacian_eq_sum_fderiv2 u (invMap y)]
    have : 2 * s * -(2 * s ^ 2) + (-(2 * s ^ 2)) ^ 2 * ‖y‖ ^ 2 = 0 := by
      have : (-(2 * s ^ 2)) ^ 2 * ‖y‖ ^ 2 = 4 * s ^ 3 * (s * ‖y‖ ^ 2) := by ring
      rw [this, hsy]
      ring
    rw [this, zero_mul, add_zero]
  rw [hsum1, hsum2, map_smul, smul_eq_mul]
  ring

end LPkg

namespace LPkg

open Laplacian

theorem hasFDerivAt_kfac {y : Space n} (hy : y ≠ 0) (a : ℝ) :
    HasFDerivAt (fun z : Space n => (‖z‖ ^ 2) ^ a)
      ((a * (‖y‖ ^ 2) ^ (a - 1)) • (2 • innerSL ℝ y)) y :=
  (hasStrictFDerivAt_norm_sq y).hasFDerivAt.rpow_const
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.2 hy)))

theorem kfacD_apply (y v : Space n) (a : ℝ) :
    ((a * (‖y‖ ^ 2) ^ (a - 1)) • (2 • innerSL ℝ y)) v =
      2 * a * (‖y‖ ^ 2) ^ (a - 1) * ⟪y, v⟫_ℝ := by
  simp only [ContinuousLinearMap.smul_apply, two_smul, ContinuousLinearMap.add_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

theorem contDiffAt_kfac {y : Space n} (hy : y ≠ 0) (a : ℝ) {m : WithTop ℕ∞} :
    ContDiffAt ℝ m (fun z : Space n => (‖z‖ ^ 2) ^ a) y :=
  (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne (pow_ne_zero 2 (norm_ne_zero_iff.2 hy))

theorem hasFDerivAt_inner_right (v y : Space n) :
    HasFDerivAt (fun z : Space n => ⟪z, v⟫_ℝ) (innerSL ℝ v) y := by
  have := (innerSL ℝ v).hasFDerivAt (x := y)
  convert this using 1
  funext z
  simp [real_inner_comm]

/-- The Kelvin factor `|y|^{1-n} = (|y|²)^{(1-n)/2}` is harmonic away from `0`. -/
theorem laplacian_kfac {y : Space n} (hy : y ≠ 0) :
    Δ (fun z : Space n => (‖z‖ ^ 2) ^ ((1 - (n : ℝ)) / 2)) y = 0 := by
  set a := (1 - (n : ℝ)) / 2 with ha
  have hy2 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have hk : ContDiffAt ℝ 2 (fun z : Space n => (‖z‖ ^ 2) ^ a) y := contDiffAt_kfac hy a
  have hk' : DifferentiableAt ℝ (fderiv ℝ (fun z : Space n => (‖z‖ ^ 2) ^ a)) y :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfd : ∀ v, (fun z => fderiv ℝ (fun z : Space n => (‖z‖ ^ 2) ^ a) z v) =ᶠ[𝓝 y]
      fun z => 2 * a * (‖z‖ ^ 2) ^ (a - 1) * ⟪z, v⟫_ℝ := by
    intro v
    filter_upwards [isOpen_ne.mem_nhds hy] with z hz
    rw [(hasFDerivAt_kfac hz a).fderiv, kfacD_apply]
  have hterm : ∀ v, fderiv ℝ (fun z => fderiv ℝ (fun z : Space n => (‖z‖ ^ 2) ^ a) z v) y v =
      2 * a * ((a - 1) * (‖y‖ ^ 2) ^ (a - 1 - 1) * 2 * ⟪y, v⟫_ℝ ^ 2 +
        (‖y‖ ^ 2) ^ (a - 1) * ‖v‖ ^ 2) := by
    intro v
    have h := ((hasFDerivAt_kfac hy (a - 1)).const_mul (2 * a)).mul (hasFDerivAt_inner_right v y)
    have h' : HasFDerivAt (fun z : Space n => 2 * a * (‖z‖ ^ 2) ^ (a - 1) * ⟪z, v⟫_ℝ) _ y := h
    rw [(hfd v).fderiv_eq, h'.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, kfacD_apply,
      innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
    ring
  rw [laplacian_eq_sum_dir hk']
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have e1 : ∑ i, (a - 1) * (‖y‖ ^ 2) ^ (a - 1 - 1) * 2 * ⟪y, bE n i⟫_ℝ ^ 2 =
      (a - 1) * (‖y‖ ^ 2) ^ (a - 1 - 1) * 2 * ‖y‖ ^ 2 := by
    rw [← Finset.mul_sum, sum_inner_sq_bE]
  have e2 : ∑ i, (‖y‖ ^ 2) ^ (a - 1) * ‖bE n i‖ ^ 2 = (‖y‖ ^ 2) ^ (a - 1) * (n + 1) := by
    rw [← Finset.mul_sum, sum_norm_sq_bE]
  rw [e1, e2]
  have e3 : (‖y‖ ^ 2) ^ (a - 1 - 1) * ‖y‖ ^ 2 = (‖y‖ ^ 2) ^ (a - 1) := by
    rw [Real.rpow_sub_one hy2 (a - 1), div_mul_cancel₀ _ hy2]
  have : (a - 1) * (‖y‖ ^ 2) ^ (a - 1 - 1) * 2 * ‖y‖ ^ 2 =
      (a - 1) * 2 * ((‖y‖ ^ 2) ^ (a - 1 - 1) * ‖y‖ ^ 2) := by ring
  rw [this, e3, ha]
  ring

/-- **Laplacian of the Kelvin transform.** -/
theorem laplacian_kelvin {u : Space n → ℝ} {y : Space n} (hy : y ≠ 0)
    (hu : ContDiffAt ℝ 2 u (invMap y)) :
    Δ (fun z => (‖z‖ ^ 2) ^ ((1 - (n : ℝ)) / 2) * u (invMap z)) y =
      (‖y‖ ^ 2) ^ ((1 - (n : ℝ)) / 2) * ((‖y‖ ^ 2)⁻¹) ^ 2 * Δ u (invMap y) := by
  have hy2 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have hk := contDiffAt_kfac hy ((1 - (n : ℝ)) / 2) (m := 2)
  have hw : ContDiffAt ℝ 2 (fun z => u (invMap z)) y := hu.comp y (contDiffAt_invMap hy)
  rw [laplacian_mul' hk hw, laplacian_kfac hy, laplacian_comp_invMap hy hu]
  have hDk : ∀ v, fderiv ℝ (fun z : Space n => (‖z‖ ^ 2) ^ ((1 - (n : ℝ)) / 2)) y v =
      2 * ((1 - (n : ℝ)) / 2) * (‖y‖ ^ 2) ^ ((1 - (n : ℝ)) / 2 - 1) * ⟪y, v⟫_ℝ := fun v => by
    rw [(hasFDerivAt_kfac hy _).fderiv, kfacD_apply]
  have hud : DifferentiableAt ℝ u (invMap y) := hu.differentiableAt (by norm_num)
  have hDw : ∀ v, fderiv ℝ (fun z => u (invMap z)) y v =
      fderiv ℝ u (invMap y) (invMapD y v) := by
    intro v
    show fderiv ℝ (u ∘ invMap) y v = _
    rw [(hud.hasFDerivAt.comp y (hasFDerivAt_invMap hy)).fderiv]
    rfl
  simp_rw [hDk, hDw]
  have hcross : ∑ i, 2 * ((1 - (n : ℝ)) / 2) * (‖y‖ ^ 2) ^ ((1 - (n : ℝ)) / 2 - 1) *
      ⟪y, bE n i⟫_ℝ * fderiv ℝ u (invMap y) (invMapD y (bE n i)) =
      2 * ((1 - (n : ℝ)) / 2) * (‖y‖ ^ 2) ^ ((1 - (n : ℝ)) / 2 - 1) *
        fderiv ℝ u (invMap y) (invMapD y y) := by
    have := congrArg (fun w => fderiv ℝ u (invMap y) (invMapD y w)) (sum_inner_smul_bE y)
    simp only [map_sum, map_smul, smul_eq_mul] at this
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hcross, invMapD_apply_self y hy, map_neg, map_smul, smul_eq_mul]
  have ht : (‖y‖ ^ 2) ^ ((1 - (n : ℝ)) / 2 - 1) =
      (‖y‖ ^ 2) ^ ((1 - (n : ℝ)) / 2) * (‖y‖ ^ 2)⁻¹ := by
    rw [Real.rpow_sub_one hy2, div_eq_mul_inv]
  rw [ht]
  ring

end LPkg

/-- **Kelvin transform.** If `u` is harmonic on an open set `W` not containing `0`, then
`|y|^{1-n} u(y/|y|²)` is harmonic on the image of `W` under inversion. -/
theorem kelvin_harmonicOnNhd {W : Set (Space n)} (hW : IsOpen W) (h0 : (0 : Space n) ∉ W)
    (u : Space n → ℝ) (hu : HarmonicOnNhd u W) :
    HarmonicOnNhd (fun y => ‖y‖ ^ (1 - (n : ℝ)) * u (‖y‖⁻¹ ^ 2 • y))
      {y | y ≠ 0 ∧ ‖y‖⁻¹ ^ 2 • y ∈ W} := by
  have hfun : (fun y : Space n => ‖y‖ ^ (1 - (n : ℝ)) * u (‖y‖⁻¹ ^ 2 • y)) =
      fun y => (‖y‖ ^ 2) ^ ((1 - (n : ℝ)) / 2) * u (LPkg.invMap y) := by
    funext y
    rw [LPkg.invMap_eq]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
    congr 1
    push_cast
    ring
  have hS : {y : Space n | y ≠ 0 ∧ ‖y‖⁻¹ ^ 2 • y ∈ W} = {y | y ≠ 0} ∩ LPkg.invMap ⁻¹' W := by
    ext y
    simp [LPkg.invMap_eq]
  rw [hfun, hS]
  have hcont : ContinuousOn LPkg.invMap {y : Space n | y ≠ 0} := fun y hy =>
    (LPkg.contDiffAt_invMap hy (m := 0)).continuousAt.continuousWithinAt
  have hSopen : IsOpen ({y : Space n | y ≠ 0} ∩ LPkg.invMap ⁻¹' W) :=
    hcont.isOpen_inter_preimage isOpen_ne hW
  intro y hy
  refine ⟨?_, ?_⟩
  · exact (LPkg.contDiffAt_kfac hy.1 _).mul ((hu _ hy.2).1.comp y (LPkg.contDiffAt_invMap hy.1))
  · filter_upwards [hSopen.mem_nhds hy] with z hz
    rw [LPkg.laplacian_kelvin hz.1 (hu _ hz.2).1]
    have := (hu _ hz.2).2.self_of_nhds
    simp only [Pi.zero_apply] at this
    rw [this, mul_zero]
    rfl

namespace LPkg

open Laplacian

/-! ### Lemma DC: invariance under rotations -/

/-- A unit vector is the image of `e_d` under a linear isometry (a reflection). -/
theorem exists_linearIsometryEquiv_ed (ν : Space n) (hν : ‖ν‖ = 1) :
    ∃ T : Space n ≃ₗᵢ[ℝ] Space n, T (ed n) = ν := by
  refine ⟨Submodule.reflection (ℝ ∙ (ed n - ν))ᗮ, Submodule.reflection_sub ?_⟩
  rw [hν]
  simp [ed]

/-- The Laplacian after a linear change of variables (no differentiability needed).
Adapted from TauCeti, `TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`. -/
theorem laplacian_comp_continuousLinearEquiv_right_apply {ι : Type*} [Fintype ι]
    (e : Space n ≃L[ℝ] Space n) (b : OrthonormalBasis ι ℝ (Space n)) (f : Space n → ℝ)
    (x : Space n) :
    Δ (f ∘ e) x = ∑ i, iteratedFDeriv ℝ 2 f (e x) ![e (b i), e (b i)] := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ e) b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x) (Set.mem_univ _) 2
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- **Invariance of the Laplacian under isometries.**
Adapted from TauCeti, `TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`. -/
theorem laplacian_comp_linearIsometryEquiv (l : Space n ≃ₗᵢ[ℝ] Space n) (f : Space n → ℝ) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  rw [Function.comp_apply, ← LinearIsometryEquiv.coe_toContinuousLinearEquiv l,
    laplacian_comp_continuousLinearEquiv_right_apply _ (stdOrthonormalBasis ℝ (Space n)),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ (Space n)).map l)]
  simp [OrthonormalBasis.map_apply]

theorem harmonicAt_comp_linearIsometryEquiv (l : Space n ≃ₗᵢ[ℝ] Space n) {f : Space n → ℝ}
    {x : Space n} (h : HarmonicAt f (l x)) : HarmonicAt (f ∘ l) x := by
  refine ⟨h.1.comp x l.toContinuousLinearEquiv.contDiff.contDiffAt, ?_⟩
  rw [laplacian_comp_linearIsometryEquiv]
  have h2 : Tendsto l (𝓝 x) (𝓝 (l x)) := l.continuous.tendsto x
  have := h2.eventually h.2
  filter_upwards [this] with y hy
  simpa using hy

/-! ### Lemma DC: the flat case -/

/-- The radial majorant `ψ (max s 1)`, monotone on all of `ℝ`. -/
noncomputable def psiBar (ψ : ℝ → ℝ) (s : ℝ) : ℝ := ψ (max s 1)

theorem psiBar_mono (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1)) : Monotone (psiBar ψ) := by
  intro s t hst
  exact hψ_mono (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_Ici.2 (le_max_right _ _))
    (max_le_max hst le_rfl)

theorem le_psiBar (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1)) (s : ℝ) :
    ψ 1 ≤ psiBar ψ s :=
  hψ_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (le_max_right _ _)) (le_max_right _ _)

theorem exists_mul_log_le (ψ : ℝ → ℝ) (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (A : ℝ) : ∃ S ≥ 2, ∀ s ≥ S, A * Real.log s ≤ ψ s := by
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.1 (hψ_log.eventually_ge_atTop A)
  refine ⟨max S 2, le_max_right _ _, fun s hs => ?_⟩
  have h1 := hS s (le_trans (le_max_left _ _) hs)
  have hlog : 0 < Real.log s := Real.log_pos (by linarith [le_max_right S 2])
  rwa [le_div_iff₀ hlog] at h1

theorem measurable_psiBar_norm (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1)) :
    Measurable (fun y' : EuclideanSpace ℝ (Fin n) => psiBar ψ ‖y'‖) :=
  (psiBar_mono ψ hψ_mono).measurable.comp continuous_norm.measurable

/-- Polynomial moments of `e^{-ψ̄(|y'|)}` are finite. -/
theorem integrable_pow_mul_exp_neg_psiBar (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop) (k : ℕ) :
    Integrable (fun y' : EuclideanSpace ℝ (Fin n) => ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖)) := by
  obtain ⟨S, hS2, hS⟩ := exists_mul_log_le ψ hψ_log ((k + n + 1 : ℕ) : ℝ)
  have hS0 : 0 ≤ S := by linarith
  have hmeas : AEStronglyMeasurable
      (fun y' : EuclideanSpace ℝ (Fin n) => ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖)) volume :=
    ((continuous_norm.pow k).measurable.mul
      (Real.measurable_exp.comp (measurable_psiBar_norm ψ hψ_mono).neg)).aestronglyMeasurable
  have hint : Integrable (fun y' : EuclideanSpace ℝ (Fin n) => (1 + ‖y'‖) ^ (-((n : ℝ) + 1))) :=
    integrable_one_add_norm (by simp)
  set K : ℝ := 2 ^ (n + 1) + S ^ k * Real.exp (-ψ 1) * (1 + S) ^ (n + 1) with hK
  have hKa : 0 ≤ S ^ k * Real.exp (-ψ 1) * (1 + S) ^ (n + 1) := by
    have := pow_nonneg hS0 k
    positivity
  have hK1 : (2 : ℝ) ^ (n + 1) ≤ K := by linarith
  have hK2 : S ^ k * Real.exp (-ψ 1) * (1 + S) ^ (n + 1) ≤ K := by
    have : (0 : ℝ) ≤ 2 ^ (n + 1) := by positivity
    linarith
  refine (hint.const_mul K).mono' hmeas (Filter.Eventually.of_forall fun y' => ?_)
  set r := ‖y'‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hpos : 0 < 1 + r := by linarith
  have hrpow : (1 + r) ^ (-((n : ℝ) + 1)) = ((1 + r) ^ (n + 1))⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    congr 1
    exact_mod_cast Real.rpow_natCast (1 + r) (n + 1)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hrpow]
  by_cases hrS : S ≤ r
  · have hr1 : (1 : ℝ) ≤ r := by linarith
    have hrpos : 0 < r := by linarith
    have hψr : psiBar ψ r = ψ r := by simp [psiBar, max_eq_left hr1]
    have h1 : Real.exp (-psiBar ψ r) ≤ (r ^ (k + n + 1))⁻¹ := by
      rw [hψr]
      have := hS r hrS
      calc Real.exp (-ψ r) ≤ Real.exp (-(((k + n + 1 : ℕ) : ℝ) * Real.log r)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = (r ^ (k + n + 1))⁻¹ := by
          rw [← Real.log_pow, Real.exp_neg, Real.exp_log (pow_pos hrpos _)]
    have h2 : r ^ k * (r ^ (k + n + 1))⁻¹ = (r ^ (n + 1))⁻¹ := by
      rw [show k + n + 1 = k + (n + 1) by ring, pow_add]
      field_simp
    have h3 : (r ^ (n + 1))⁻¹ ≤ 2 ^ (n + 1) * ((1 + r) ^ (n + 1))⁻¹ := by
      have h4 : (1 + r) ^ (n + 1) ≤ (2 * r) ^ (n + 1) :=
        pow_le_pow_left₀ hpos.le (by linarith) _
      rw [mul_pow] at h4
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc (r ^ (n + 1))⁻¹ * (1 + r) ^ (n + 1) ≤ (r ^ (n + 1))⁻¹ * (2 ^ (n + 1) * r ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 2 ^ (n + 1) := by field_simp
    calc r ^ k * Real.exp (-psiBar ψ r) ≤ r ^ k * (r ^ (k + n + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (r ^ (n + 1))⁻¹ := h2
      _ ≤ 2 ^ (n + 1) * ((1 + r) ^ (n + 1))⁻¹ := h3
      _ ≤ K * ((1 + r) ^ (n + 1))⁻¹ := mul_le_mul_of_nonneg_right hK1 (by positivity)
  · push Not at hrS
    have h1 : Real.exp (-psiBar ψ r) ≤ Real.exp (-ψ 1) :=
      Real.exp_le_exp.2 (neg_le_neg (le_psiBar ψ hψ_mono r))
    have h2 : r ^ k ≤ S ^ k := pow_le_pow_left₀ hr0 hrS.le _
    have h3 : 1 ≤ (1 + S) ^ (n + 1) * ((1 + r) ^ (n + 1))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hpos.le (by linarith) _
    have hSk : 0 ≤ S ^ k := pow_nonneg hS0 k
    calc r ^ k * Real.exp (-psiBar ψ r) ≤ S ^ k * Real.exp (-ψ 1) :=
          mul_le_mul h2 h1 (by positivity) hSk
      _ ≤ S ^ k * Real.exp (-ψ 1) * ((1 + S) ^ (n + 1) * ((1 + r) ^ (n + 1))⁻¹) :=
          le_mul_of_one_le_right (by positivity) h3
      _ = (S ^ k * Real.exp (-ψ 1) * (1 + S) ^ (n + 1)) * ((1 + r) ^ (n + 1))⁻¹ := by ring
      _ ≤ K * ((1 + r) ^ (n + 1))⁻¹ := mul_le_mul_of_nonneg_right hK2 (by positivity)

/-- `Cu ≥ 0` (the half-space is nonempty). -/
theorem cu_nonneg (lam : ℝ) (U : Space n → ℝ) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖)) : 0 ≤ Cu := by
  have h1 := hdecay (lift 0 (lam + 1)) (by rw [vcoord_lift]; linarith)
  have h2 := abs_nonneg (U (lift 0 (lam + 1)))
  have h3 := Real.exp_pos (-ψ ‖lift (0 : EuclideanSpace ℝ (Fin n)) (lam + 1)‖)
  by_contra hneg
  push Not at hneg
  nlinarith

/-- Horizontal slices are bounded by `Cu e^{-ψ̄(|y'|)}`. -/
theorem slice_bound (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1)) (t : ℝ) (ht : lam < t) (y' : EuclideanSpace ℝ (Fin n)) :
    |U (lift y' t)| ≤ Cu * Real.exp (-psiBar ψ ‖y'‖) := by
  have hCu := cu_nonneg lam U ψ Cu hdecay
  refine (hdecay _ (by rw [vcoord_lift]; exact ht)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) hCu
  have h1 : max ‖y'‖ 1 ≤ ‖lift y' t‖ := by
    refine max_le (F1.norm_le_norm_lift y' t) ?_
    have := norm_lift_sq y' t
    have h4 : (1 : ℝ) ≤ t ^ 2 := by nlinarith
    nlinarith [norm_nonneg (lift y' t), sq_nonneg ‖y'‖]
  exact hψ_mono (Set.mem_Ici.2 (le_max_right _ _))
    (Set.mem_Ici.2 ((le_max_right _ _).trans h1)) h1

theorem slice_continuous (lam : ℝ) (U : Space n → ℝ) (hU : HarmonicOnNhd U {y | lam < vcoord y})
    (t : ℝ) (ht : lam < t) : Continuous (fun y' : EuclideanSpace ℝ (Fin n) => U (lift y' t)) := by
  have hU' : ContinuousOn U {y | lam < vcoord y} := hU.continuousOn
  refine hU'.comp_continuous (F1.continuous_lift_left t) fun y' => ?_
  show lam < vcoord (lift y' t)
  rw [vcoord_lift]; exact ht

/-- The horizontal moments `m_k(t) = ∫ ⟪y', e⟫ᵏ U(y', t) dy'`. -/
noncomputable def hmoment (U : Space n → ℝ) (e : EuclideanSpace ℝ (Fin n)) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ y' : EuclideanSpace ℝ (Fin n), ⟪y', e⟫_ℝ ^ k * U (lift y' t)

theorem hmoment_bound (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (k : ℕ) (t : ℝ) (ht : lam < t) :
    |hmoment U e k t| ≤ ‖e‖ ^ k * Cu *
      ∫ y' : EuclideanSpace ℝ (Fin n), ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖) := by
  have hCu := cu_nonneg lam U ψ Cu hdecay
  rw [hmoment, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le
    ((integrable_pow_mul_exp_neg_psiBar ψ hψ_mono hψ_log k).const_mul _)
    (Filter.Eventually.of_forall fun y' => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : |⟪y', e⟫_ℝ| ^ k ≤ (‖e‖ * ‖y'‖) ^ k := by
    gcongr
    rw [mul_comm]
    exact abs_real_inner_le_norm y' e
  have h2 := slice_bound lam hlam U ψ Cu hdecay hψ_mono t ht y'
  calc |⟪y', e⟫_ℝ| ^ k * |U (lift y' t)| ≤ (‖e‖ * ‖y'‖) ^ k * (Cu * Real.exp (-psiBar ψ ‖y'‖)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = ‖e‖ ^ k * Cu * (‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖)) := by ring

theorem hmoment_tendsto_zero (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Tendsto (hmoment U e k) atTop (𝓝 0) := by
  have hCu := cu_nonneg lam U ψ Cu hdecay
  have h0 : (0 : ℝ) = ∫ y' : EuclideanSpace ℝ (Fin n), (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y' => ‖e‖ ^ k * Cu * (‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖))) ?_ ?_
    ((integrable_pow_mul_exp_neg_psiBar ψ hψ_mono hψ_log k).const_mul _) ?_
  · filter_upwards [eventually_gt_atTop lam] with t ht
    exact (((continuous_id.inner continuous_const).pow k).mul
      (slice_continuous lam U hU t ht)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop lam] with t ht
    refine Filter.Eventually.of_forall fun y' => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |⟪y', e⟫_ℝ| ^ k ≤ (‖e‖ * ‖y'‖) ^ k := by
      gcongr
      rw [mul_comm]
      exact abs_real_inner_le_norm y' e
    have h2 := slice_bound lam hlam U ψ Cu hdecay hψ_mono t ht y'
    calc |⟪y', e⟫_ℝ| ^ k * |U (lift y' t)| ≤ (‖e‖ * ‖y'‖) ^ k * (Cu * Real.exp (-psiBar ψ ‖y'‖)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = ‖e‖ ^ k * Cu * (‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖)) := by ring
  · refine Filter.Eventually.of_forall fun y' => ?_
    -- `|U (lift y' t)| ≤ Cu e^{-ψ(t)} → 0`
    have hψtop : Tendsto ψ atTop atTop := by
      obtain ⟨S, hS2, hS⟩ := exists_mul_log_le ψ hψ_log 1
      refine tendsto_atTop_mono' atTop ?_ (Real.tendsto_log_atTop)
      filter_upwards [eventually_ge_atTop S] with s hs
      simpa using hS s hs
    have hU0 : Tendsto (fun t => U (lift y' t)) atTop (𝓝 0) := by
      have hexp : Tendsto (fun t => Cu * Real.exp (-ψ t)) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hψtop).const_mul Cu
        simpa using this
      refine squeeze_zero_norm' ?_ hexp
      filter_upwards [eventually_gt_atTop lam] with t ht
      rw [Real.norm_eq_abs]
      refine (hdecay _ (by rw [vcoord_lift]; exact ht)).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) hCu
      have ht1 : 1 ≤ t := by linarith
      have h1 : t ≤ ‖lift y' t‖ := by
        have := norm_lift_sq y' t
        nlinarith [norm_nonneg (lift y' t), sq_nonneg ‖y'‖]
      exact hψ_mono (Set.mem_Ici.2 ht1) (Set.mem_Ici.2 (ht1.trans h1)) h1
    have := hU0.const_mul (⟪y', e⟫_ℝ ^ k)
    simpa using this

/-- A function with `m' = D`, `D' = 0` on `(a, ∞)` is affine there. -/
theorem affine_of_hasDerivAt (m D : ℝ → ℝ) (a : ℝ)
    (hm : ∀ t, a < t → HasDerivAt m (D t) t) (hD : ∀ t, a < t → HasDerivAt D 0 t) :
    ∃ α β : ℝ, ∀ t, a < t → m t = α * t + β := by
  have key : ∀ s t, a < s → s < t → D t = D s := by
    intro s t hs hst
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (f := D) (f' := fun _ => (0 : ℝ)) hst
      (fun x hx => (hD x (lt_of_lt_of_le hs hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => hD x (lt_trans hs hx.1))
    have hne : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
    have := hc'.symm
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · linarith [sub_eq_zero.1 h]
    · exact absurd h hne
  have hDc : ∀ t, a < t → D t = D (a + 1) := by
    intro t ht
    rcases lt_trichotomy t (a + 1) with h | h | h
    · exact (key t (a + 1) ht h).symm
    · rw [h]
    · exact key (a + 1) t (by linarith) h
  have hslope : ∀ s t, a < s → s < t → m t - m s = D (a + 1) * (t - s) := by
    intro s t hs hst
    obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope (f := m) (f' := D) hst
      (fun x hx => (hm x (lt_of_lt_of_le hs hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => hm x (lt_trans hs hx.1))
    rw [hDc ξ (lt_trans hs hξ.1)] at hξ'
    have hne : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
    rw [hξ']
    field_simp
  refine ⟨D (a + 1), m (a + 1) - D (a + 1) * (a + 1), fun t ht => ?_⟩
  rcases lt_trichotomy t (a + 1) with h | h | h
  · have := hslope t (a + 1) ht h
    linarith
  · rw [h]; ring
  · have := hslope (a + 1) t (by linarith) h
    linarith

/-- A bounded affine function on `(a, ∞)` tending to `0` vanishes. -/
theorem eq_zero_of_affine_bounded (m : ℝ → ℝ) (a α β B : ℝ)
    (haff : ∀ t, a < t → m t = α * t + β) (hb : ∀ t, a < t → |m t| ≤ B)
    (hlim : Tendsto m atTop (𝓝 0)) : ∀ t, a < t → m t = 0 := by
  have hα : α = 0 := by
    by_contra hne
    have hαpos : 0 < |α| := abs_pos.2 hne
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hb (a + 1) (by linarith))
    set t := |a| + 1 + (B + |β| + 1) / |α| with ht
    have hfrac : 0 ≤ (B + |β| + 1) / |α| := by positivity
    have hta : a < t := by
      have := le_abs_self a
      linarith
    have h1 := hb t hta
    rw [haff t hta] at h1
    have h2 : B + |β| + 1 ≤ |α| * t := by
      have : |α| * ((B + |β| + 1) / |α|) = B + |β| + 1 := mul_div_cancel₀ _ hαpos.ne'
      have h3 : 0 ≤ |α| * (|a| + 1) := by positivity
      rw [ht, mul_add, this]
      linarith
    have htpos : 0 < t := by
      rw [ht]
      have := abs_nonneg a
      linarith [hfrac]
    have h4 : |α| * t ≤ |α * t + β| + |β| := by
      have e : α * t = (α * t + β) + (-β) := by ring
      have := abs_add_le (α * t + β) (-β)
      rw [← e, abs_neg, abs_mul, abs_of_pos htpos] at this
      exact this
    linarith
  subst hα
  have hconst : ∀ t, a < t → m t = β := fun t ht => by rw [haff t ht]; ring
  have hlim' : Tendsto m atTop (𝓝 β) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop a] with t ht
    exact (hconst t ht).symm
  have hβ : β = 0 := tendsto_nhds_unique hlim' hlim
  intro t ht
  rw [hconst t ht, hβ]

/-! ### Proof of `hmoment_affine` (mean-value route)

Route 3 of the docstring of `hmoment_affine`.
* `hmoment_mvp`: integrating `F4.mean_value_phi` at the points `lift w t` against `⟪w, e⟫ᵏ dw`,
  swapping the integrals (`integrable_prod_mvp`), translating `w` and expanding binomially
  (`integral_shift`), the lower moments drop out and
  `m_k(t) ∫ φ = ∫ m_k(t + r z_d) φ(z) dz` for all small `r > 0`.
* `affine_of_mvp`: a continuous function with this one-dimensional mean value property is affine
  (maximum principle `le_zero_of_mvp`, applied to `±(f - chord)`; it uses `φ ≥ 0`, the symmetry
  `φ(-z) = φ(z)` and a point `z` with `z_d > 0`, `φ(z) > 0`).
* `continuousOn_hmoment`: continuity of the moments (dominated convergence).
-/

namespace W_L_moment

/-! ### Elementary geometry of `Space n = ℝⁿ × ℝ` -/

/-- The horizontal part of a point, as an element of `ℝⁿ`. -/
noncomputable def hpE (z : Space n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => z (Fin.castSucc i))

theorem hpE_apply (z : Space n) (i : Fin n) : hpE z i = z (Fin.castSucc i) := rfl

theorem lift_hpE (z : Space n) : lift (hpE z) (vcoord z) = z := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [F1.lift_apply_last, vcoord]
  · simp [F1.lift_apply_castSucc, hpE_apply]

theorem lift_add_smul (w : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (z : Space n) :
    lift w t + r • z = lift (w + r • hpE z) (t + r * vcoord z) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [F1.lift_apply_last, vcoord]
  · simp [F1.lift_apply_castSucc, hpE_apply]

theorem norm_hpE_le (z : Space n) : ‖hpE z‖ ≤ ‖z‖ := by
  have h := norm_lift_sq (hpE z) (vcoord z)
  rw [lift_hpE] at h
  nlinarith [norm_nonneg (hpE z), norm_nonneg z, sq_nonneg (vcoord z)]

theorem abs_vcoord_le (z : Space n) : |vcoord z| ≤ ‖z‖ := by
  have h := norm_lift_sq (hpE z) (vcoord z)
  rw [lift_hpE] at h
  have h2 : |vcoord z| ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [sq_abs]; nlinarith [sq_nonneg ‖hpE z‖]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 h2

theorem vcoord_sub (y x : Space n) : vcoord (y - x) = vcoord y - vcoord x := by
  simp [vcoord]

/-! ### The mollifier `φ` -/

theorem norm_le_of_phi_ne_zero {z : Space n} (hz : F4.phi z ≠ 0) : ‖z‖ ≤ 1 / 2 := by
  by_contra h
  push Not at h
  exact hz (F4.phi_eq_zero h)

theorem phi_neg (z : Space n) : F4.phi (-z) = F4.phi z := by
  simp [F4.phi, norm_neg]

theorem integral_vcoord_mul_phi : ∫ z : Space n, vcoord z * F4.phi z = 0 := by
  have h := integral_neg_eq_self (fun z : Space n => vcoord z * F4.phi z) volume
  have hneg : ∀ z : Space n, vcoord (-z) * F4.phi (-z) = -(vcoord z * F4.phi z) := by
    intro z
    rw [phi_neg]
    simp [vcoord]
  simp only [hneg, integral_neg] at h
  linarith

theorem exists_phi_pos : ∃ z : Space n, 0 < vcoord z ∧ 0 < F4.phi z := by
  obtain ⟨τ, hτ, hτ'⟩ := F4.exists_deriv_prof_pos
  refine ⟨Real.sqrt τ • ed n, ?_, ?_⟩
  · simp [vcoord, ed, Real.sqrt_pos.2 hτ]
  · have h1 : ‖Real.sqrt τ • ed n‖ ^ 2 = τ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      simp [ed, Real.sq_sqrt hτ.le]
    unfold F4.phi
    rw [h1]
    positivity

theorem continuous_vcoord_mul_phi : Continuous (fun z : Space n => vcoord z * F4.phi z) :=
  F1.continuous_vcoord.mul F4.continuous_phi

theorem integrable_vcoord_mul_phi : Integrable (fun z : Space n => vcoord z * F4.phi z) :=
  continuous_vcoord_mul_phi.integrable_of_hasCompactSupport F4.hasCompactSupport_phi.mul_left

/-- `z ↦ g (t + r z_d) φ(z)` is continuous when `g` is continuous on `(a, ∞)` and
`t - r/2 > a`. -/
theorem continuous_comp_mul_phi (g : ℝ → ℝ) (a t r : ℝ) (hg : ContinuousOn g (Set.Ioi a))
    (hr : 0 ≤ r) (ht : a < t - r / 2) :
    Continuous (fun z : Space n => g (t + r * vcoord z) * F4.phi z) := by
  set O : Set (Space n) := {z | a < t + r * vcoord z} with hO
  have hOo : IsOpen O :=
    isOpen_lt continuous_const (continuous_const.add (continuous_const.mul F1.continuous_vcoord))
  refine ContinuousOn.continuous_of_tsupport_subset ?_ hOo ?_
  · refine ContinuousOn.mul ?_ F4.continuous_phi.continuousOn
    refine hg.comp (continuous_const.add (continuous_const.mul F1.continuous_vcoord)).continuousOn
      (fun z hz => hz)
  · refine tsupport_mul_subset_right.trans (F4.tsupport_phi_subset.trans fun z hz => ?_)
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    have h1 := abs_le.1 ((abs_vcoord_le z).trans hz)
    have h2 : r * (-(1 / 2)) ≤ r * vcoord z := mul_le_mul_of_nonneg_left h1.1 hr
    show a < t + r * vcoord z
    linarith

theorem integrable_comp_mul_phi (g : ℝ → ℝ) (a t r : ℝ) (hg : ContinuousOn g (Set.Ioi a))
    (hr : 0 ≤ r) (ht : a < t - r / 2) :
    Integrable (fun z : Space n => g (t + r * vcoord z) * F4.phi z) :=
  (continuous_comp_mul_phi g a t r hg hr ht).integrable_of_hasCompactSupport
    F4.hasCompactSupport_phi.mul_left

/-! ### A one-dimensional mean value property forces affinity -/

/-- Maximum principle for the one-dimensional mean value property. -/
theorem le_zero_of_mvp (g : ℝ → ℝ) (a p q : ℝ) (hap : a < p) (_hpq : p ≤ q)
    (hg : ContinuousOn g (Set.Ioi a))
    (hmvp : ∀ t, a < t → ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      g t * ∫ z : Space n, F4.phi z = ∫ z : Space n, g (t + r * vcoord z) * F4.phi z)
    (hp : g p ≤ 0) (hq : g q ≤ 0) : ∀ t ∈ Set.Icc p q, g t ≤ 0 := by
  intro t₀ ht₀
  by_contra hpos
  push Not at hpos
  have hIcc : Set.Icc p q ⊆ Set.Ioi a := fun x hx => lt_of_lt_of_le hap hx.1
  have hgc : ContinuousOn g (Set.Icc p q) := hg.mono hIcc
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨t₀, ht₀⟩ hgc
  set M := g tm with hM
  have hMpos : 0 < M := lt_of_lt_of_le hpos (isMaxOn_iff.1 hmax t₀ ht₀)
  set S := Set.Icc p q ∩ g ⁻¹' {M} with hS
  have hSc : IsClosed S := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSk : IsCompact S := isCompact_Icc.of_isClosed_subset hSc Set.inter_subset_left
  have hSne : S.Nonempty := ⟨tm, htm, rfl⟩
  obtain ⟨t₁, ht₁S, ht₁g⟩ := hSk.exists_isGreatest hSne
  have ht₁ : t₁ ∈ Set.Icc p q := ht₁S.1
  have hgt₁ : g t₁ = M := ht₁S.2
  have ht₁q : t₁ < q := by
    rcases lt_or_eq_of_le ht₁.2 with h | h
    · exact h
    · exfalso; rw [h] at hgt₁; linarith
  have ht₁p : p < t₁ := by
    rcases lt_or_eq_of_le ht₁.1 with h | h
    · exact h
    · exfalso; rw [← h] at hgt₁; linarith
  obtain ⟨r₀, hr₀, hr₀'⟩ := hmvp t₁ (lt_trans hap ht₁p)
  set r := min (r₀ / 2) (min (q - t₁) (t₁ - p)) with hr
  have hrpos : 0 < r := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hrr₀ : r < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrq : r ≤ q - t₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrp : r ≤ t₁ - p := le_trans (min_le_right _ _) (min_le_right _ _)
  have hmv := hr₀' r hrpos hrr₀
  have hsupp : ∀ z : Space n, F4.phi z ≠ 0 → t₁ + r * vcoord z ∈ Set.Icc p q := by
    intro z hz
    have h1 := abs_le.1 ((abs_vcoord_le z).trans (norm_le_of_phi_ne_zero hz))
    have h2 : r * (-(1 / 2)) ≤ r * vcoord z := mul_le_mul_of_nonneg_left h1.1 hrpos.le
    have h3 : r * vcoord z ≤ r * (1 / 2) := mul_le_mul_of_nonneg_left h1.2 hrpos.le
    constructor <;> linarith
  have hat : a < t₁ - r / 2 := by linarith
  have hint : Integrable (fun z : Space n => g (t₁ + r * vcoord z) * F4.phi z) :=
    integrable_comp_mul_phi g a t₁ r hg hrpos.le hat
  have hcont : Continuous (fun z : Space n => g (t₁ + r * vcoord z) * F4.phi z) :=
    continuous_comp_mul_phi g a t₁ r hg hrpos.le hat
  set h : Space n → ℝ := fun z => M * F4.phi z - g (t₁ + r * vcoord z) * F4.phi z with hh
  have hh_cont : Continuous h := (continuous_const.mul F4.continuous_phi).sub hcont
  have hh_nonneg : 0 ≤ h := by
    intro z
    simp only [hh, Pi.zero_apply]
    by_cases hz : F4.phi z = 0
    · simp [hz]
    · have hle : g (t₁ + r * vcoord z) ≤ M := isMaxOn_iff.1 hmax _ (hsupp z hz)
      have := F4.phi_nonneg z
      nlinarith
  have hh_int : Integrable h := (F4.integrable_phi.const_mul M).sub hint
  have hh_zero : ∫ z, h z = 0 := by
    simp only [hh]
    rw [integral_sub (F4.integrable_phi.const_mul M) hint, integral_const_mul, ← hmv, hgt₁]
    ring
  have hae := (integral_eq_zero_iff_of_nonneg hh_nonneg hh_int).1 hh_zero
  have heq : h = 0 := (hh_cont.ae_eq_iff_eq volume continuous_zero).1 hae
  obtain ⟨z₀, hz₀v, hz₀φ⟩ := exists_phi_pos (n := n)
  have h0 := congrFun heq z₀
  simp only [hh, Pi.zero_apply] at h0
  have hgz : g (t₁ + r * vcoord z₀) = M := by
    have h5 : (M - g (t₁ + r * vcoord z₀)) * F4.phi z₀ = 0 := by rw [sub_mul]; exact h0
    rcases mul_eq_zero.1 h5 with h6 | h6
    · linarith
    · exact absurd h6 hz₀φ.ne'
  have hmem : t₁ + r * vcoord z₀ ∈ S := ⟨hsupp z₀ hz₀φ.ne', hgz⟩
  have := ht₁g hmem
  nlinarith [mul_pos hrpos hz₀v]

/-- Affine combinations preserve the mean value property. -/
theorem mvp_affine_comb (f : ℝ → ℝ) (a : ℝ) (hf : ContinuousOn f (Set.Ioi a))
    (hmvp : ∀ t, a < t → ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      f t * ∫ z : Space n, F4.phi z = ∫ z : Space n, f (t + r * vcoord z) * F4.phi z)
    (c α β : ℝ) :
    ∀ t, a < t → ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      (c * (f t - (α * t + β))) * ∫ z : Space n, F4.phi z =
        ∫ z : Space n, (c * (f (t + r * vcoord z) - (α * (t + r * vcoord z) + β))) *
          F4.phi z := by
  intro t ht
  obtain ⟨r₀, hr₀, hr₀'⟩ := hmvp t ht
  refine ⟨min r₀ (t - a), lt_min hr₀ (by linarith), fun r hr hrr => ?_⟩
  have hr1 : r < r₀ := lt_of_lt_of_le hrr (min_le_left _ _)
  have hr2 : r < t - a := lt_of_lt_of_le hrr (min_le_right _ _)
  have hat : a < t - r / 2 := by linarith
  have hint : Integrable (fun z : Space n => f (t + r * vcoord z) * F4.phi z) :=
    integrable_comp_mul_phi f a t r hf hr.le hat
  have e : ∀ z : Space n, (c * (f (t + r * vcoord z) - (α * (t + r * vcoord z) + β))) *
      F4.phi z = c * (f (t + r * vcoord z) * F4.phi z) - (c * (α * t + β)) * F4.phi z -
        (c * α * r) * (vcoord z * F4.phi z) := by
    intro z; ring
  simp_rw [e]
  have i1 : Integrable (fun z : Space n => c * (f (t + r * vcoord z) * F4.phi z)) :=
    hint.const_mul c
  have i2 : Integrable (fun z : Space n => (c * (α * t + β)) * F4.phi z) :=
    F4.integrable_phi.const_mul _
  have i3 : Integrable (fun z : Space n => (c * α * r) * (vcoord z * F4.phi z)) :=
    integrable_vcoord_mul_phi.const_mul _
  have i12 : Integrable (fun z : Space n =>
      c * (f (t + r * vcoord z) * F4.phi z) - (c * (α * t + β)) * F4.phi z) := i1.sub i2
  rw [integral_sub i12 i3, integral_sub i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_vcoord_mul_phi,
    ← hr₀' r hr hr1]
  ring

/-- **A continuous function with the one-dimensional mean value property is affine.** -/
theorem affine_of_mvp (f : ℝ → ℝ) (a : ℝ) (hf : ContinuousOn f (Set.Ioi a))
    (hmvp : ∀ t, a < t → ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      f t * ∫ z : Space n, F4.phi z = ∫ z : Space n, f (t + r * vcoord z) * F4.phi z) :
    ∃ α β : ℝ, ∀ t, a < t → f t = α * t + β := by
  -- on every interval `[p, q]`, `f` agrees with its chord
  have hchord : ∀ p q, a < p → p < q → ∀ t ∈ Set.Icc p q,
      f t = f p + (f q - f p) / (q - p) * (t - p) := by
    intro p q hap hpq t ht
    set s := (f q - f p) / (q - p) with hs
    have hqp : q - p ≠ 0 := sub_ne_zero.2 hpq.ne'
    have hsq : f q - (s * q + (f p - s * p)) = 0 := by
      rw [hs]; field_simp; ring
    have hsp : f p - (s * p + (f p - s * p)) = 0 := by ring
    have hgc : ∀ c : ℝ, ContinuousOn (fun t => c * (f t - (s * t + (f p - s * p))))
        (Set.Ioi a) := fun c =>
      continuousOn_const.mul (hf.sub (continuousOn_const.mul continuousOn_id |>.add
        continuousOn_const))
    have h1 := le_zero_of_mvp (n := n) (fun t => 1 * (f t - (s * t + (f p - s * p)))) a p q hap
      hpq.le (hgc 1) (mvp_affine_comb f a hf hmvp 1 s (f p - s * p))
      (show 1 * (f p - (s * p + (f p - s * p))) ≤ 0 by rw [hsp]; norm_num)
      (show 1 * (f q - (s * q + (f p - s * p))) ≤ 0 by rw [hsq]; norm_num) t ht
    have h2 := le_zero_of_mvp (n := n) (fun t => (-1) * (f t - (s * t + (f p - s * p)))) a p q
      hap hpq.le (hgc (-1)) (mvp_affine_comb f a hf hmvp (-1) s (f p - s * p))
      (show (-1) * (f p - (s * p + (f p - s * p))) ≤ 0 by rw [hsp]; norm_num)
      (show (-1) * (f q - (s * q + (f p - s * p))) ≤ 0 by rw [hsq]; norm_num) t ht
    have h1' : 1 * (f t - (s * t + (f p - s * p))) ≤ 0 := h1
    have h2' : (-1) * (f t - (s * t + (f p - s * p))) ≤ 0 := h2
    linarith
  refine ⟨f (a + 2) - f (a + 1), f (a + 1) - (f (a + 2) - f (a + 1)) * (a + 1), fun t ht => ?_⟩
  set p := min t (a + 1) with hp
  set q := max t (a + 2) with hq
  have hap : a < p := lt_min ht (by linarith)
  have hpq : p < q := lt_of_le_of_lt (min_le_right _ _)
    (lt_of_lt_of_le (by linarith) (le_max_right _ _))
  have hmem : ∀ x, a + 1 ≤ x → x ≤ a + 2 → x ∈ Set.Icc p q := fun x h1 h2 =>
    ⟨le_trans (min_le_right _ _) h1, le_trans h2 (le_max_right _ _)⟩
  have e1 := hchord p q hap hpq (a + 1) (hmem _ le_rfl (by linarith))
  have e2 := hchord p q hap hpq (a + 2) (hmem _ (by linarith) le_rfl)
  have e3 := hchord p q hap hpq t ⟨min_le_left _ _, le_max_left _ _⟩
  set s := (f q - f p) / (q - p)
  have hs : s = f (a + 2) - f (a + 1) := by linarith
  rw [e3, ← hs]
  linarith


/-! ### Decay of `U` and integrability of the moment integrands -/

theorem exp_neg_psiBar_le (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : ℝ, 0 ≤ ρ → Real.exp (-psiBar ψ ρ) ≤ K * ((1 + ρ) ^ N)⁻¹ := by
  obtain ⟨S, hS2, hS⟩ := exists_mul_log_le ψ hψ_log (N : ℝ)
  have hS0 : 0 ≤ S := by linarith
  set K : ℝ := 2 ^ N + Real.exp (-ψ 1) * (1 + S) ^ N with hK
  refine ⟨K, by positivity, fun ρ hρ => ?_⟩
  have hpos : 0 < 1 + ρ := by linarith
  have hE : 0 ≤ Real.exp (-ψ 1) * (1 + S) ^ N * ((1 + ρ) ^ N)⁻¹ := by positivity
  have h6 : 0 ≤ 2 ^ N * ((1 + ρ) ^ N)⁻¹ := by positivity
  have hK' : K * ((1 + ρ) ^ N)⁻¹ = 2 ^ N * ((1 + ρ) ^ N)⁻¹ +
      Real.exp (-ψ 1) * (1 + S) ^ N * ((1 + ρ) ^ N)⁻¹ := by rw [hK]; ring
  rw [hK']
  by_cases hρS : S ≤ ρ
  · have hρ1 : (1 : ℝ) ≤ ρ := by linarith
    have hρpos : 0 < ρ := by linarith
    have hψρ : psiBar ψ ρ = ψ ρ := by simp [psiBar, max_eq_left hρ1]
    have h1 : Real.exp (-psiBar ψ ρ) ≤ (ρ ^ N)⁻¹ := by
      rw [hψρ]
      have := hS ρ hρS
      calc Real.exp (-ψ ρ) ≤ Real.exp (-((N : ℝ) * Real.log ρ)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = (ρ ^ N)⁻¹ := by
          rw [← Real.log_pow, Real.exp_neg, Real.exp_log (pow_pos hρpos _)]
    have h3 : (ρ ^ N)⁻¹ ≤ 2 ^ N * ((1 + ρ) ^ N)⁻¹ := by
      have h4 : (1 + ρ) ^ N ≤ (2 * ρ) ^ N := pow_le_pow_left₀ hpos.le (by linarith) _
      rw [mul_pow] at h4
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc (ρ ^ N)⁻¹ * (1 + ρ) ^ N ≤ (ρ ^ N)⁻¹ * (2 ^ N * ρ ^ N) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 2 ^ N := by field_simp
    linarith
  · push Not at hρS
    have h1 : Real.exp (-psiBar ψ ρ) ≤ Real.exp (-ψ 1) :=
      Real.exp_le_exp.2 (neg_le_neg (le_psiBar ψ hψ_mono ρ))
    have h3 : 1 ≤ (1 + S) ^ N * ((1 + ρ) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hpos.le (by linarith) _
    have h5 : Real.exp (-ψ 1) ≤ Real.exp (-ψ 1) * (1 + S) ^ N * ((1 + ρ) ^ N)⁻¹ := by
      rw [mul_assoc]; exact le_mul_of_one_le_right (Real.exp_pos _).le h3
    linarith

theorem slice_poly_bound (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y' : EuclideanSpace ℝ (Fin n)) (t : ℝ), lam < t →
      |U (lift y' t)| ≤ C * ((1 + ‖y'‖) ^ N)⁻¹ := by
  obtain ⟨K, hK, hKb⟩ := exp_neg_psiBar_le ψ hψ_mono hψ_log N
  have hCu := cu_nonneg lam U ψ Cu hdecay
  refine ⟨Cu * K, mul_nonneg hCu hK, fun y' t ht => ?_⟩
  calc |U (lift y' t)| ≤ Cu * Real.exp (-psiBar ψ ‖y'‖) :=
        slice_bound lam hlam U ψ Cu hdecay hψ_mono t ht y'
    _ ≤ Cu * (K * ((1 + ‖y'‖) ^ N)⁻¹) := mul_le_mul_of_nonneg_left (hKb _ (norm_nonneg _)) hCu
    _ = Cu * K * ((1 + ‖y'‖) ^ N)⁻¹ := by ring

theorem moment_integrand_bound (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ) (ψ : ℝ → ℝ)
    (Cu : ℝ) (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1)) (e : EuclideanSpace ℝ (Fin n)) (j : ℕ) (s : ℝ)
    (hs : lam < s) (y' : EuclideanSpace ℝ (Fin n)) :
    ‖⟪y', e⟫_ℝ ^ j * U (lift y' s)‖ ≤ ‖e‖ ^ j * Cu * (‖y'‖ ^ j * Real.exp (-psiBar ψ ‖y'‖)) := by
  have hCu := cu_nonneg lam U ψ Cu hdecay
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : |⟪y', e⟫_ℝ| ^ j ≤ (‖e‖ * ‖y'‖) ^ j := by
    gcongr
    rw [mul_comm]
    exact abs_real_inner_le_norm y' e
  have h2 := slice_bound lam hlam U ψ Cu hdecay hψ_mono s hs y'
  calc |⟪y', e⟫_ℝ| ^ j * |U (lift y' s)| ≤ (‖e‖ * ‖y'‖) ^ j * (Cu * Real.exp (-psiBar ψ ‖y'‖)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = ‖e‖ ^ j * Cu * (‖y'‖ ^ j * Real.exp (-psiBar ψ ‖y'‖)) := by ring

theorem integrable_moment (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (j : ℕ) (s : ℝ) (hs : lam < s) :
    Integrable (fun y' : EuclideanSpace ℝ (Fin n) => ⟪y', e⟫_ℝ ^ j * U (lift y' s)) :=
  ((integrable_pow_mul_exp_neg_psiBar ψ hψ_mono hψ_log j).const_mul (‖e‖ ^ j * Cu)).mono'
    (((continuous_id.inner continuous_const).pow j).mul
      (slice_continuous lam U hU s hs)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y' =>
      moment_integrand_bound lam hlam U ψ Cu hdecay hψ_mono e j s hs y')

theorem continuousOn_hmoment (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ContinuousOn (hmoment U e k) (Set.Ioi lam) := by
  show ContinuousOn (fun t => ∫ y' : EuclideanSpace ℝ (Fin n), ⟪y', e⟫_ℝ ^ k * U (lift y' t)) _
  refine continuousOn_of_dominated
    (bound := fun y' => ‖e‖ ^ k * Cu * (‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖))) ?_ ?_
    ((integrable_pow_mul_exp_neg_psiBar ψ hψ_mono hψ_log k).const_mul _) ?_
  · intro t ht
    exact (((continuous_id.inner continuous_const).pow k).mul
      (slice_continuous lam U hU t ht)).aestronglyMeasurable
  · intro t ht
    exact Filter.Eventually.of_forall fun y' =>
      moment_integrand_bound lam hlam U ψ Cu hdecay hψ_mono e k t ht y'
  · refine Filter.Eventually.of_forall fun y' => ?_
    refine continuousOn_const.mul ?_
    refine hU.continuousOn.comp (F1.continuous_lift_right y').continuousOn fun t ht => ?_
    show lam < vcoord (lift y' t)
    rw [vcoord_lift]
    exact ht

/-! ### The mean value property of the moments -/

/-- Translating the horizontal variable and expanding binomially: the lower moments drop out. -/
theorem integral_shift (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hprev : ∀ j < k, ∀ t, lam + 1 / 2 < t → hmoment U e j t = 0)
    (s : ℝ) (hs : lam + 1 / 2 < s) (c : EuclideanSpace ℝ (Fin n)) :
    ∫ w : EuclideanSpace ℝ (Fin n), ⟪w, e⟫_ℝ ^ k * U (lift (w + c) s) = hmoment U e k s := by
  have hs' : lam < s := by linarith
  have h1 : ∫ w : EuclideanSpace ℝ (Fin n), ⟪w, e⟫_ℝ ^ k * U (lift (w + c) s) =
      ∫ v : EuclideanSpace ℝ (Fin n), ⟪v - c, e⟫_ℝ ^ k * U (lift v s) := by
    rw [← integral_add_right_eq_self (fun v : EuclideanSpace ℝ (Fin n) =>
      ⟪v - c, e⟫_ℝ ^ k * U (lift v s)) c]
    simp only [add_sub_cancel_right]
  rw [h1]
  have h2 : ∀ v : EuclideanSpace ℝ (Fin n), ⟪v - c, e⟫_ℝ ^ k * U (lift v s) =
      ∑ j ∈ Finset.range (k + 1),
        ((-⟪c, e⟫_ℝ) ^ (k - j) * (k.choose j : ℝ)) * (⟪v, e⟫_ℝ ^ j * U (lift v s)) := by
    intro v
    rw [inner_sub_left, sub_eq_add_neg, add_pow, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h2]
  rw [integral_finsetSum _ (fun j _ =>
    (integrable_moment lam hlam U hU ψ Cu hdecay hψ_mono hψ_log e j s hs').const_mul _)]
  rw [Finset.sum_range_succ]
  have h3 : ∑ j ∈ Finset.range k, ∫ v : EuclideanSpace ℝ (Fin n),
      ((-⟪c, e⟫_ℝ) ^ (k - j) * (k.choose j : ℝ)) * (⟪v, e⟫_ℝ ^ j * U (lift v s)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [integral_const_mul]
    have := hprev j (Finset.mem_range.1 hj) s hs
    rw [hmoment] at this
    rw [this, mul_zero]
  rw [h3, zero_add, integral_const_mul]
  simp [hmoment]

theorem inner_integral_eq (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hprev : ∀ j < k, ∀ t, lam + 1 / 2 < t → hmoment U e j t = 0)
    (t r : ℝ) (_ht : lam + 1 / 2 < t) (hr0 : 0 ≤ r) (hr : r < 2 * (t - (lam + 1 / 2)))
    (z : Space n) :
    ∫ w : EuclideanSpace ℝ (Fin n), ⟪w, e⟫_ℝ ^ k * U (lift w t + r • z) * F4.phi z =
      hmoment U e k (t + r * vcoord z) * F4.phi z := by
  by_cases hz : F4.phi z = 0
  · simp [hz]
  · have h1 := abs_le.1 ((abs_vcoord_le z).trans (norm_le_of_phi_ne_zero hz))
    have h2 : r * (-(1 / 2)) ≤ r * vcoord z := mul_le_mul_of_nonneg_left h1.1 hr0
    have hs : lam + 1 / 2 < t + r * vcoord z := by linarith
    rw [integral_mul_const]
    congr 1
    simp_rw [lift_add_smul]
    exact integral_shift lam hlam U hU ψ Cu hdecay hψ_mono hψ_log e k hprev _ hs _

/-- Integrability on `ℝⁿ × ℝⁿ⁺¹` of the integrand of the averaged mean value identity. -/
theorem integrable_prod_mvp (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (t r : ℝ) (ht : lam + 1 / 2 < t) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × Space n =>
      ⟪p.1, e⟫_ℝ ^ k * U (lift p.1 t + r • p.2) * F4.phi p.2) (volume.prod volume) := by
  set N := k + n + 1 with hN
  obtain ⟨C, hC, hCb⟩ := slice_poly_bound lam hlam U ψ Cu hdecay hψ_mono hψ_log N
  have hint1 : Integrable (fun w : EuclideanSpace ℝ (Fin n) => (1 + ‖w‖) ^ (-((n : ℝ) + 1))) :=
    integrable_one_add_norm (by simp)
  have hint1' : Integrable (fun w : EuclideanSpace ℝ (Fin n) => ((1 + ‖w‖) ^ (n + 1))⁻¹) := by
    refine hint1.congr (Filter.Eventually.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    show (1 + ‖w‖) ^ (-((n : ℝ) + 1)) = ((1 + ‖w‖) ^ (n + 1))⁻¹
    rw [Real.rpow_neg hpos.le]
    congr 1
    exact_mod_cast Real.rpow_natCast (1 + ‖w‖) (n + 1)
  have hint := (hint1'.mul_prod (F4.integrable_phi (n := n))).const_mul
    (‖e‖ ^ k * C * (4 / 3) ^ N)
  set O : Set (EuclideanSpace ℝ (Fin n) × Space n) := {p | lam < t + r * vcoord p.2} with hO
  have hOo : IsOpen O := isOpen_lt continuous_const
    (continuous_const.add (continuous_const.mul (F1.continuous_vcoord.comp continuous_snd)))
  have hsub : {p : EuclideanSpace ℝ (Fin n) × Space n | ‖p.2‖ ≤ 1 / 2} ⊆ O := by
    intro p hp
    have h1 := abs_le.1 ((abs_vcoord_le p.2).trans hp)
    have h2 : r * (-(1 / 2)) ≤ r * vcoord p.2 := mul_le_mul_of_nonneg_left h1.1 hr0
    show lam < t + r * vcoord p.2
    nlinarith
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × Space n =>
      ⟪p.1, e⟫_ℝ ^ k * U (lift p.1 t + r • p.2) * F4.phi p.2) := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hOo ?_
    · refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
      · exact ((continuous_fst.inner continuous_const).pow k).continuousOn
      · refine hU.continuousOn.comp (Continuous.continuousOn ?_) fun p hp => ?_
        · exact ((F1.continuous_lift_left t).comp continuous_fst).add
            (continuous_snd.const_smul r)
        · show lam < vcoord (lift p.1 t + r • p.2)
          rw [lift_add_smul, vcoord_lift]
          exact hp
      · exact (F4.continuous_phi.comp continuous_snd).continuousOn
    · refine Set.Subset.trans (closure_minimal (fun p hp => ?_)
        (isClosed_le continuous_snd.norm continuous_const)) hsub
      refine norm_le_of_phi_ne_zero fun h => (Function.mem_support.1 hp) ?_
      simp [h]
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨w, z⟩ := p
  show ‖⟪w, e⟫_ℝ ^ k * U (lift w t + r • z) * F4.phi z‖ ≤
    ‖e‖ ^ k * C * (4 / 3) ^ N * (((1 + ‖w‖) ^ (n + 1))⁻¹ * F4.phi z)
  have hφ := F4.phi_nonneg z
  by_cases hz : F4.phi z = 0
  · simp [hz]
  · have hz' := norm_le_of_phi_ne_zero hz
    have hs : lam < t + r * vcoord z := hsub (show ‖(w, z).2‖ ≤ 1 / 2 from hz')
    have hU1 : |U (lift w t + r • z)| ≤ C * ((1 + ‖w + r • hpE z‖) ^ N)⁻¹ := by
      rw [lift_add_smul]; exact hCb _ _ hs
    have hc : ‖r • hpE z‖ ≤ 1 / 4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
      have h5 : ‖hpE z‖ ≤ 1 / 2 := (norm_hpE_le z).trans hz'
      calc r * ‖hpE z‖ ≤ (1 / 2) * (1 / 2) := mul_le_mul hr1 h5 (norm_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    have hw : ‖w‖ ≤ ‖w + r • hpE z‖ + ‖r • hpE z‖ := by
      have := norm_sub_le (w + r • hpE z) (r • hpE z)
      rwa [add_sub_cancel_right] at this
    have hge : 3 / 4 * (1 + ‖w‖) ≤ 1 + ‖w + r • hpE z‖ := by linarith [norm_nonneg w]
    have hpos : 0 < 3 / 4 * (1 + ‖w‖) := by positivity
    have hinv : ((1 + ‖w + r • hpE z‖) ^ N)⁻¹ ≤ (4 / 3) ^ N * ((1 + ‖w‖) ^ N)⁻¹ := by
      have h1 : (3 / 4 * (1 + ‖w‖)) ^ N ≤ (1 + ‖w + r • hpE z‖) ^ N :=
        pow_le_pow_left₀ hpos.le hge N
      calc ((1 + ‖w + r • hpE z‖) ^ N)⁻¹ ≤ ((3 / 4 * (1 + ‖w‖)) ^ N)⁻¹ :=
            inv_anti₀ (pow_pos hpos N) h1
        _ = (4 / 3) ^ N * ((1 + ‖w‖) ^ N)⁻¹ := by
            rw [mul_pow, mul_inv, ← inv_pow]; norm_num
    have hpoly : |⟪w, e⟫_ℝ| ^ k ≤ ‖e‖ ^ k * (1 + ‖w‖) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ k
      calc |⟪w, e⟫_ℝ| ≤ ‖w‖ * ‖e‖ := abs_real_inner_le_norm w e
        _ ≤ ‖e‖ * (1 + ‖w‖) := by nlinarith [norm_nonneg e, norm_nonneg w]
    have hpos' : 0 < 1 + ‖w‖ := by positivity
    have hw1 : (1 + ‖w‖) ^ k * ((1 + ‖w‖) ^ N)⁻¹ = ((1 + ‖w‖) ^ (n + 1))⁻¹ := by
      rw [hN, show k + n + 1 = k + (n + 1) by ring, pow_add, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hpos'.ne'), one_mul]
    have hUb : |U (lift w t + r • z)| ≤ C * ((4 / 3) ^ N * ((1 + ‖w‖) ^ N)⁻¹) :=
      hU1.trans (mul_le_mul_of_nonneg_left hinv hC)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hφ]
    calc |⟪w, e⟫_ℝ| ^ k * |U (lift w t + r • z)| * F4.phi z
        ≤ (‖e‖ ^ k * (1 + ‖w‖) ^ k) * (C * ((4 / 3) ^ N * ((1 + ‖w‖) ^ N)⁻¹)) * F4.phi z :=
          mul_le_mul_of_nonneg_right (mul_le_mul hpoly hUb (abs_nonneg _) (by positivity)) hφ
      _ = ‖e‖ ^ k * C * (4 / 3) ^ N * (((1 + ‖w‖) ^ k * ((1 + ‖w‖) ^ N)⁻¹) * F4.phi z) := by
          ring
      _ = ‖e‖ ^ k * C * (4 / 3) ^ N * (((1 + ‖w‖) ^ (n + 1))⁻¹ * F4.phi z) := by rw [hw1]

/-- **The moments have the one-dimensional mean value property.** -/
theorem hmoment_mvp (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hprev : ∀ j < k, ∀ t, lam + 1 / 2 < t → hmoment U e j t = 0)
    (t r : ℝ) (ht : lam + 1 / 2 < t) (hr0 : 0 < r) (hr1 : r ≤ 1 / 2)
    (hr : r < 2 * (t - (lam + 1 / 2))) :
    hmoment U e k t * ∫ z : Space n, F4.phi z =
      ∫ z : Space n, hmoment U e k (t + r * vcoord z) * F4.phi z := by
  have hpt : ∀ w : EuclideanSpace ℝ (Fin n),
      U (lift w t) * ∫ z : Space n, F4.phi z =
        ∫ z : Space n, U (lift w t + r • z) * F4.phi z := by
    intro w
    refine F4.mean_value_phi hr0 (hU.mono fun y hy => ?_)
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 := abs_le.1 ((abs_vcoord_le (y - lift w t)).trans hy.le)
    rw [vcoord_sub, vcoord_lift] at h1
    show lam < vcoord y
    linarith [h1.1]
  calc hmoment U e k t * ∫ z : Space n, F4.phi z
      = ∫ w : EuclideanSpace ℝ (Fin n),
          ⟪w, e⟫_ℝ ^ k * U (lift w t) * ∫ z : Space n, F4.phi z := by
        rw [hmoment, integral_mul_const]
    _ = ∫ w : EuclideanSpace ℝ (Fin n), ∫ z : Space n,
          ⟪w, e⟫_ℝ ^ k * U (lift w t + r • z) * F4.phi z := by
        congr 1
        funext w
        rw [mul_assoc, hpt w, ← integral_const_mul]
        congr 1
        funext z
        ring
    _ = ∫ z : Space n, ∫ w : EuclideanSpace ℝ (Fin n),
          ⟪w, e⟫_ℝ ^ k * U (lift w t + r • z) * F4.phi z :=
        integral_integral_swap
          (integrable_prod_mvp lam hlam U hU ψ Cu hdecay hψ_mono hψ_log e k t r ht hr0.le hr1)
    _ = ∫ z : Space n, hmoment U e k (t + r * vcoord z) * F4.phi z := by
        congr 1
        funext z
        exact inner_integral_eq lam hlam U hU ψ Cu hdecay hψ_mono hψ_log e k hprev t r ht
          hr0.le hr z

end W_L_moment

/-- **The moments are affine** (PDE input): if all lower moments `m_j` (`j < k`) vanish on
`(λ + 1/2, ∞)`, then `m_k` is affine there.

Classical route: `m_k'' = -k(k-1)‖e‖² m_{k-2}` (then apply `affine_of_hasDerivAt`). Put
`D t = ∫ ⟪y', e⟫ᵏ ∂ₜU(y', t) dy'`; interior derivative estimates for `U` on balls of radius `1/2`
(from the mean value property `F4.mean_value_phi`, after writing `U` as a convolution with the
smooth radial bump `F4.phi`) give `|∂^α U(y', t)| ≤ C e^{-ψ̄(|y'|/2)}` for `|α| ≤ 2` and
`t > λ + 1/2`; this justifies differentiating twice under the integral sign; then `∂ₜ²U = -Δ'U`
and two integrations by parts in `y'` give `∫ ⟪y', e⟫ᵏ Δ'U = k(k-1)‖e‖² ∫ ⟪y', e⟫ᵏ⁻² U`.
Weak route: test `ΔU = 0` against `⟪y', e⟫ᵏ χ(t) η(y'/R)`, let `R → ∞` using only the decay of
`U`, and use that a continuous function with vanishing distributional second derivative on an
interval is affine.
Mean-value route: integrate `F4.mean_value_phi` against `⟪y', e⟫ᵏ dy'`; expanding
`⟪w' - r z', e⟫ᵏ` binomially, the lower moments `m_j` (`j < k`, all `0` by strong induction; the
odd ones also vanish by the symmetry of `φ`) drop out, so `m_k(t) ∫φ = ∫ K(s) m_k(t + r s) ds`
with the even kernel `K(s) = ∫ φ(z', s) dz'`, for all small `r`; a continuous function with this
one-dimensional mean value property is affine. -/
theorem hmoment_affine (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (e : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hprev : ∀ j < k, ∀ t, lam + 1 / 2 < t → hmoment U e j t = 0) :
    ∃ α β : ℝ, ∀ t, lam + 1 / 2 < t → hmoment U e k t = α * t + β := by
  refine W_L_moment.affine_of_mvp (n := n) (hmoment U e k) (lam + 1 / 2)
    ((W_L_moment.continuousOn_hmoment lam hlam U hU ψ Cu hdecay hψ_mono hψ_log e k).mono
      (Set.Ioi_subset_Ioi (by linarith))) fun t ht => ?_
  refine ⟨min (1 / 2) (2 * (t - (lam + 1 / 2))), lt_min (by norm_num) (by linarith),
    fun r hr0 hr => ?_⟩
  exact W_L_moment.hmoment_mvp lam hlam U hU ψ Cu hdecay hψ_mono hψ_log e k hprev t r ht hr0
    (lt_of_lt_of_le hr (min_le_left _ _)).le (lt_of_lt_of_le hr (min_le_right _ _))

/-- **Vanishing of the horizontal moments.** For a harmonic function on `{t > λ}` decaying faster
than every power, all moments `∫ ⟪y', e⟫ᵏ U(y', t) dy'` vanish for `t > λ + 1`.
(The moments `m_k(t)` satisfy `m_k'' = -k(k-1)‖e‖² m_{k-2}`, are bounded, and tend to `0`.) -/
theorem flat_moments_eq_zero (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (t : ℝ) (ht : lam + 1 < t) (e : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ∫ y' : EuclideanSpace ℝ (Fin n), ⟪y', e⟫_ℝ ^ k * U (lift y' t) = 0 := by
  suffices h : ∀ k : ℕ, ∀ t, lam + 1 / 2 < t → hmoment U e k t = 0 from
    h k t (by linarith)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hprev : ∀ j < k, ∀ t, lam + 1 / 2 < t → hmoment U e j t = 0 := fun j hj => ih j hj
    obtain ⟨α, β, haff⟩ := hmoment_affine lam hlam U hU ψ Cu hdecay hψ_mono hψ_log e k hprev
    exact eq_zero_of_affine_bounded (hmoment U e k) (lam + 1 / 2) α β _ haff
      (fun t ht => hmoment_bound lam hlam U ψ Cu hdecay hψ_mono hψ_log e k t (by linarith))
      (hmoment_tendsto_zero lam hlam U hU ψ Cu hdecay hψ_mono hψ_log e k)

/-- The line pairing `L y s = ⟪e, y⟫ s` (from the Fourier scouting checks). -/
noncomputable def lineL (e : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).comp (innerSL ℝ e)

open scoped FourierTransform in
theorem lineFourier_eq (e : EuclideanSpace ℝ (Fin n)) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (s : ℝ) :
    VectorFourier.fourierIntegral Real.fourierChar volume (lineL e).toLinearMap₁₂ F s =
      𝓕 F (s • e) := by
  simp only [VectorFourier.fourierIntegral, Real.fourier_eq, lineL,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, innerSL_apply_apply, ContinuousLinearMap.mul_apply', inner_smul_right]
  congr 1
  ext y
  rw [real_inner_comm, mul_comm]

theorem norm_lineL_le (e : EuclideanSpace ℝ (Fin n)) : ‖lineL e‖ ≤ ‖e‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg e) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_
  simp only [lineL, ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.mul_apply', norm_mul]
  have := norm_inner_le_norm (𝕜 := ℝ) e v
  gcongr

theorem integral_pow_mul_exp_neg_psiBar_pos (hn : 0 < n) (ψ : ℝ → ℝ)
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop) (k : ℕ) :
    0 < ∫ y' : EuclideanSpace ℝ (Fin n), ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖) := by
  rw [integral_pos_iff_support_of_nonneg (fun y' => by positivity)
    (integrable_pow_mul_exp_neg_psiBar ψ hψ_mono hψ_log k)]
  set e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have hsub : Metric.ball e₀ (1 / 2) ⊆ Function.support
      (fun y' : EuclideanSpace ℝ (Fin n) => ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖)) := by
    intro y' hy'
    rw [Function.mem_support]
    have hy0 : y' ≠ 0 := by
      rintro rfl
      rw [Metric.mem_ball, dist_zero_left, he₀] at hy'
      norm_num at hy'
    have : 0 < ‖y'‖ := norm_pos_iff.2 hy0
    positivity
  exact lt_of_lt_of_le (Metric.measure_ball_pos volume e₀ (by norm_num)) (measure_mono hsub)

/-- The Legendre-type exponent `L_k = sup_{σ ≥ 0} (σ - ψ̄(e^σ)/(2k))`, so that
`sup_{r ≥ 0} r^k e^{-ψ̄(r)/2} = e^{k L_k}`. -/
noncomputable def carlemanL (ψ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ⨆ σ : Set.Ici (0 : ℝ), ((σ : ℝ) - psiBar ψ (Real.exp σ) / (2 * k))

theorem carlemanL_bddAbove (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop) (k : ℕ) (hk : 1 ≤ k) :
    BddAbove (Set.range fun σ : Set.Ici (0 : ℝ) =>
      (σ : ℝ) - psiBar ψ (Real.exp σ) / (2 * k)) := by
  obtain ⟨S, hS2, hS⟩ := exists_mul_log_le ψ hψ_log (4 * k)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨Real.log S + |ψ 1|, ?_⟩
  rintro _ ⟨⟨σ, hσ⟩, rfl⟩
  simp only [Set.mem_Ici] at hσ
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hψ1 : ψ 1 ≤ psiBar ψ (Real.exp σ) := le_psiBar ψ hψ_mono _
  by_cases hσS : S ≤ Real.exp σ
  · have hexp1 : 1 ≤ Real.exp σ := Real.one_le_exp hσ
    have h1 : psiBar ψ (Real.exp σ) = ψ (Real.exp σ) := by simp [psiBar, max_eq_left hexp1]
    have h2 := hS (Real.exp σ) hσS
    rw [Real.log_exp] at h2
    have h3 : 2 * σ ≤ psiBar ψ (Real.exp σ) / (2 * k) := by
      rw [le_div_iff₀ (by positivity), h1]
      nlinarith
    have := abs_nonneg (ψ 1)
    show σ - psiBar ψ (Real.exp σ) / (2 * k) ≤ Real.log S + |ψ 1|
    linarith
  · push Not at hσS
    have h1 : σ < Real.log S := by
      rw [← Real.log_exp σ]
      exact Real.log_lt_log (Real.exp_pos σ) hσS
    have h2 : -(psiBar ψ (Real.exp σ) / (2 * k)) ≤ |ψ 1| := by
      have h3 : -ψ 1 ≤ |ψ 1| := neg_le_abs _
      have h4 : -(psiBar ψ (Real.exp σ) / (2 * k)) ≤ -(ψ 1) / (2 * k) := by
        rw [neg_div]
        exact neg_le_neg (div_le_div_of_nonneg_right hψ1 (by positivity))
      have h5 : -(ψ 1) / (2 * k) ≤ |ψ 1| := by
        rw [div_le_iff₀ (by positivity)]
        have : |ψ 1| ≤ |ψ 1| * (2 * k) := by
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          have : (1 : ℝ) ≤ 2 * k := by linarith
          nlinarith [abs_nonneg (ψ 1)]
        linarith
      linarith
    show σ - psiBar ψ (Real.exp σ) / (2 * k) ≤ Real.log S + |ψ 1|
    linarith

theorem pow_mul_exp_neg_psiBar_le (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop) (k : ℕ) (hk : 1 ≤ k)
    (r : ℝ) (hr : 0 ≤ r) :
    r ^ k * Real.exp (-(psiBar ψ r / 2)) ≤ Real.exp (carlemanL ψ k) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hbdd := carlemanL_bddAbove ψ hψ_mono hψ_log k hk
  have hle : ∀ σ : ℝ, 0 ≤ σ → σ - psiBar ψ (Real.exp σ) / (2 * k) ≤ carlemanL ψ k :=
    fun σ hσ => le_ciSup hbdd (⟨σ, hσ⟩ : Set.Ici (0 : ℝ))
  rw [← Real.exp_nat_mul]
  rcases lt_or_ge r 1 with hr1 | hr1
  · -- `0 ≤ r < 1`
    have h0 := hle 0 le_rfl
    rw [Real.exp_zero] at h0
    have hψr : psiBar ψ r = psiBar ψ 1 := by simp [psiBar, max_eq_right hr1.le]
    have hrk : r ^ k ≤ 1 := pow_le_one₀ hr hr1.le
    calc r ^ k * Real.exp (-(psiBar ψ r / 2)) ≤ 1 * Real.exp (-(psiBar ψ 1 / 2)) := by
          rw [hψr]
          exact mul_le_mul_of_nonneg_right hrk (Real.exp_pos _).le
      _ = Real.exp (-(psiBar ψ 1 / 2)) := one_mul _
      _ ≤ Real.exp (k * carlemanL ψ k) := by
          refine Real.exp_le_exp.2 ?_
          have : -(psiBar ψ 1 / 2) = k * (0 - psiBar ψ 1 / (2 * k)) := by
            field_simp
            ring
          rw [this]
          exact mul_le_mul_of_nonneg_left h0 hkpos.le
  · -- `r ≥ 1`, write `r = e^σ`
    have hrpos : 0 < r := by linarith
    set σ := Real.log r with hσ
    have hσ0 : 0 ≤ σ := Real.log_nonneg hr1
    have hexpσ : Real.exp σ = r := Real.exp_log hrpos
    have h1 := hle σ hσ0
    rw [hexpσ] at h1
    calc r ^ k * Real.exp (-(psiBar ψ r / 2))
        = Real.exp (k * σ) * Real.exp (-(psiBar ψ r / 2)) := by
          rw [Real.exp_nat_mul, hexpσ]
      _ = Real.exp (k * (σ - psiBar ψ r / (2 * k))) := by
          rw [← Real.exp_add]
          congr 1
          field_simp
          ring
      _ ≤ Real.exp (k * carlemanL ψ k) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 hkpos.le)

/-- **Block bound** (convexity): if the chord slope of `σ ↦ ψ(e^σ)` on `[j, j+1]` is at least
`2k`, then `L_k ≤ j + 1 + |ψ 1|`. -/
theorem carlemanL_le_of_slope (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop) (σ₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ))) (j : ℕ) (hj : σ₀ ≤ j)
    (k : ℕ) (hk : 1 ≤ k)
    (hslope : 2 * (k : ℝ) ≤ ψ (Real.exp ((j : ℝ) + 1)) - ψ (Real.exp j)) :
    carlemanL ψ k ≤ (j : ℝ) + 1 + |ψ 1| := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, le_rfl⟩⟩
  refine ciSup_le fun ⟨σ, hσ⟩ => ?_
  simp only [Set.mem_Ici] at hσ
  show σ - psiBar ψ (Real.exp σ) / (2 * k) ≤ (j : ℝ) + 1 + |ψ 1|
  have hpsi : ∀ τ : ℝ, 0 ≤ τ → psiBar ψ (Real.exp τ) = ψ (Real.exp τ) := fun τ hτ => by
    simp [psiBar, max_eq_left (Real.one_le_exp hτ)]
  have hneg : ∀ τ : ℝ, 0 ≤ τ → -(ψ (Real.exp τ) / (2 * k)) ≤ |ψ 1| := by
    intro τ hτ
    have h1 : ψ 1 ≤ ψ (Real.exp τ) := hψ_mono (Set.mem_Ici.2 le_rfl)
      (Set.mem_Ici.2 (Real.one_le_exp hτ)) (Real.one_le_exp hτ)
    have h4 : -(ψ (Real.exp τ) / (2 * k)) ≤ -(ψ 1) / (2 * k) := by
      rw [neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_right h1 (by positivity))
    have h5 : -(ψ 1) / (2 * k) ≤ |ψ 1| := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ 2 * k := by linarith
      nlinarith [abs_nonneg (ψ 1), neg_le_abs (ψ 1)]
    linarith
  rw [hpsi σ hσ]
  rcases le_or_gt σ ((j : ℝ) + 1) with h | h
  · have := hneg σ hσ
    linarith
  · -- convexity on `j < j + 1 < σ`
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hsl := hconv.slope_mono_adjacent (x := (j : ℝ)) (y := (j : ℝ) + 1) (z := σ)
      (Set.mem_Ici.2 hj) (Set.mem_Ici.2 (by linarith)) (by linarith) h
    simp only [add_sub_cancel_left, div_one] at hsl
    have hpos : 0 < σ - ((j : ℝ) + 1) := by linarith
    rw [le_div_iff₀ hpos] at hsl
    have h2 : ψ (Real.exp ((j : ℝ) + 1)) + 2 * k * (σ - ((j : ℝ) + 1)) ≤ ψ (Real.exp σ) := by
      nlinarith
    have h3 : σ - ψ (Real.exp σ) / (2 * k) ≤
        (j : ℝ) + 1 - ψ (Real.exp ((j : ℝ) + 1)) / (2 * k) := by
      have : ψ (Real.exp σ) / (2 * k) ≥
          ψ (Real.exp ((j : ℝ) + 1)) / (2 * k) + (σ - ((j : ℝ) + 1)) := by
        rw [ge_iff_le, ← sub_nonneg]
        have e : ψ (Real.exp σ) / (2 * k) -
            (ψ (Real.exp ((j : ℝ) + 1)) / (2 * k) + (σ - ((j : ℝ) + 1))) =
            (ψ (Real.exp σ) - (ψ (Real.exp ((j : ℝ) + 1)) + 2 * k * (σ - ((j : ℝ) + 1)))) /
              (2 * k) := by
          field_simp
        rw [e]
        exact div_nonneg (by linarith) (by positivity)
      linarith
    have := hneg ((j : ℝ) + 1) (by linarith)
    linarith

/-- Telescoping: `∑_{j < m, a ≤ j} (x^j - x^{j+1}) ≤ x^a` for `0 ≤ x`. -/
theorem sum_tele_le (x : ℝ) (hx : 0 ≤ x) (a m : ℕ) :
    ∑ j ∈ Finset.range m, (if a ≤ j then x ^ j - x ^ (j + 1) else 0) ≤ x ^ a := by
  have key : ∀ m : ℕ, ∑ j ∈ Finset.range m, (if a ≤ j then x ^ j - x ^ (j + 1) else 0) +
      x ^ (max a m) = x ^ a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      by_cases ham : a ≤ m
      · rw [if_pos ham]
        have h1 : max a (m + 1) = m + 1 := max_eq_right (by omega)
        have h2 : max a m = m := max_eq_right ham
        rw [h2] at ih
        rw [h1]
        linarith
      · rw [if_neg ham]
        have h1 : max a (m + 1) = a := max_eq_left (by omega)
        have h2 : max a m = a := max_eq_left (by omega)
        rw [h2] at ih
        rw [h1]
        linarith
  have := key m
  have hpos : 0 ≤ x ^ (max a m) := pow_nonneg hx _
  linarith

/-- Abel summation: `∑_{j ≤ N} (Ψ j - Ψ 0) x^j + (Ψ N - Ψ 0) x^{N+1}/(1-x) =
∑_{i < N} (Ψ (i+1) - Ψ i) x^{i+1}/(1-x)`. -/
theorem abel_identity (Ψ : ℕ → ℝ) (x : ℝ) (hx : x ≠ 1) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (Ψ j - Ψ 0) * x ^ j + (Ψ N - Ψ 0) * x ^ (N + 1) / (1 - x) =
      ∑ i ∈ Finset.range N, (Ψ (i + 1) - Ψ i) * x ^ (i + 1) / (1 - x) := by
  have h1x : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => (Ψ (i + 1) - Ψ i) * x ^ (i + 1) / (1 - x)),
      ← ih]
    field_simp
    ring

/-- **Abel summation core** (pure sequences): if the increments `s_j = Ψ(j+1) - Ψ(j) ≥ 0` are
eventually nondecreasing and `Λ_k ≤ j + c` whenever `2k ≤ s_j`, then `∑ e^{-Λ_k} < ∞` forces
`∑ Ψ(j) e^{-j} < ∞`.

Proof plan: for `j ≥ J`, every integer `k ∈ (s_{j-1}/2, s_j/2]` has `e^{-Λ_k} ≥ e^{-c} e^{-j}`, and
these blocks are disjoint; so the partial sums of `∑_j (⌊s_j/2⌋ - ⌊s_{j-1}/2⌋) e^{-j}` are bounded.
Abel summation turns this into a bound on `∑_j ⌊s_j/2⌋ e^{-j}`, hence on `∑_j s_j e^{-j}`, and a
second Abel summation (with `Ψ` bounded below) bounds `∑_j Ψ(j) e^{-j}`. If `s_j` stays bounded,
`Ψ(j) = O(j)` and the conclusion is immediate. -/
theorem summable_of_block_bound (Ψ : ℕ → ℝ) (J : ℕ) (hmono : ∀ j, Ψ j ≤ Ψ (j + 1))
    (hconv : ∀ j, J ≤ j → Ψ (j + 1) - Ψ j ≤ Ψ (j + 2) - Ψ (j + 1))
    (Λ : ℕ → ℝ) (c : ℝ)
    (hΛ : ∀ j, J ≤ j → ∀ k : ℕ, 1 ≤ k → 2 * (k : ℝ) ≤ Ψ (j + 1) - Ψ j → Λ k ≤ j + c)
    (hsum : Summable (fun k => Real.exp (-Λ k))) :
    Summable (fun j : ℕ => Ψ j * Real.exp (-(j : ℝ))) := by
  classical
  set x : ℝ := Real.exp (-1) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hq : 0 < 1 - x := by linarith
  have hexp : ∀ j : ℕ, Real.exp (-(j : ℝ)) = x ^ j := by
    intro j
    rw [hxdef, ← Real.exp_nat_mul]
    ring_nf
  simp_rw [hexp]
  set s : ℕ → ℝ := fun j => Ψ (j + 1) - Ψ j with hs
  have hs0 : ∀ j, 0 ≤ s j := fun j => sub_nonneg.2 (hmono j)
  set T := ∑' k, Real.exp (-Λ k) with hT
  set w : ℕ → ℝ := fun j => x ^ j - x ^ (j + 1) with hw
  have hw_eq : ∀ j : ℕ, w j = (1 - x) * x ^ j := fun j => by simp only [hw]; ring
  have hw0 : ∀ j, 0 ≤ w j := fun j => by rw [hw_eq]; positivity
  -- the per-`k` bound
  have hk' : ∀ N k : ℕ, 1 ≤ k → ∑ j ∈ Finset.range N,
      (if J ≤ j ∧ 2 * (k : ℝ) ≤ s j then w j else 0) ≤ Real.exp c * Real.exp (-Λ k) := by
    intro N k hk1
    by_cases hex : ∃ j, J ≤ j ∧ 2 * (k : ℝ) ≤ s j
    · have hj₀ := Nat.find_spec hex
      have hΛk : Λ k ≤ (Nat.find hex : ℝ) + c := hΛ _ hj₀.1 k hk1 hj₀.2
      calc ∑ j ∈ Finset.range N, (if J ≤ j ∧ 2 * (k : ℝ) ≤ s j then w j else 0)
          ≤ ∑ j ∈ Finset.range N, (if Nat.find hex ≤ j then x ^ j - x ^ (j + 1) else 0) := by
            refine Finset.sum_le_sum fun j _ => ?_
            by_cases hc : J ≤ j ∧ 2 * (k : ℝ) ≤ s j
            · rw [if_pos hc, if_pos (Nat.find_min' hex hc)]
            · rw [if_neg hc]
              split_ifs
              · exact hw0 j
              · exact le_rfl
        _ ≤ x ^ (Nat.find hex) := sum_tele_le x hx0.le _ N
        _ = Real.exp (-((Nat.find hex : ℕ) : ℝ)) := (hexp _).symm
        _ ≤ Real.exp c * Real.exp (-Λ k) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.2 (by linarith)
    · push Not at hex
      rw [Finset.sum_eq_zero fun j _ => if_neg (fun h => absurd h.2 (not_le.2 (hex j h.1)))]
      positivity
  -- counting
  have hcount : ∀ N, ∑ j ∈ Finset.range N, (if J ≤ j then w j * (s j / 2 - 1) else 0) ≤
      Real.exp c * T := by
    intro N
    set M : ℕ := ∑ j ∈ Finset.range N, ⌊s j⌋₊ with hM
    calc ∑ j ∈ Finset.range N, (if J ≤ j then w j * (s j / 2 - 1) else 0)
        ≤ ∑ j ∈ Finset.range N, ∑ k ∈ Finset.Icc 1 M,
            (if J ≤ j ∧ 2 * (k : ℝ) ≤ s j then w j else 0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          by_cases hJ : J ≤ j
          · rw [if_pos hJ]
            simp only [hJ, true_and]
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
            have hsub : Finset.Icc 1 ⌊s j / 2⌋₊ ⊆
                (Finset.Icc 1 M).filter (fun k : ℕ => 2 * (k : ℝ) ≤ s j) := by
              intro k hk
              rw [Finset.mem_Icc] at hk
              rw [Finset.mem_filter, Finset.mem_Icc]
              have hk2 : (k : ℝ) ≤ s j / 2 :=
                (Nat.cast_le.2 hk.2).trans (Nat.floor_le (by linarith [hs0 j]))
              refine ⟨⟨hk.1, hk.2.trans ?_⟩, by linarith⟩
              calc ⌊s j / 2⌋₊ ≤ ⌊s j⌋₊ := Nat.floor_le_floor (by linarith [hs0 j])
                _ ≤ M := Finset.single_le_sum (f := fun i => ⌊s i⌋₊)
                    (fun i _ => Nat.zero_le _) hj
            have hcard := Finset.card_le_card hsub
            rw [Nat.card_Icc, add_tsub_cancel_right] at hcard
            have hfl : s j / 2 - 1 ≤ (⌊s j / 2⌋₊ : ℝ) := by
              have := Nat.lt_floor_add_one (s j / 2)
              linarith
            have hcard' : (⌊s j / 2⌋₊ : ℝ) ≤
                (((Finset.Icc 1 M).filter (fun k : ℕ => 2 * (k : ℝ) ≤ s j)).card : ℝ) := by
              exact_mod_cast hcard
            rw [mul_comm (w j)]
            exact mul_le_mul_of_nonneg_right (hfl.trans hcard') (hw0 j)
          · rw [if_neg hJ]
            refine Finset.sum_nonneg fun k _ => ?_
            split_ifs
            · exact hw0 j
            · exact le_rfl
      _ = ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.range N,
            (if J ≤ j ∧ 2 * (k : ℝ) ≤ s j then w j else 0) := Finset.sum_comm
      _ ≤ ∑ k ∈ Finset.Icc 1 M, Real.exp c * Real.exp (-Λ k) :=
          Finset.sum_le_sum fun k hk => hk' N k (Finset.mem_Icc.1 hk).1
      _ = Real.exp c * ∑ k ∈ Finset.Icc 1 M, Real.exp (-Λ k) := by rw [Finset.mul_sum]
      _ ≤ Real.exp c * T := mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ (fun k _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
  -- summability of `s_j x^j`
  have hgeo : Summable (fun j : ℕ => x ^ j) := summable_geometric_of_lt_one hx0.le hx1
  set A := ∑ j ∈ Finset.range J, s j * x ^ j with hA
  have hsumS : Summable (fun j => s j * x ^ j) := by
    refine summable_of_sum_range_le (c := A + 2 / (1 - x) * (Real.exp c * T) +
      2 * ∑' j, x ^ j) (fun j => mul_nonneg (hs0 j) (pow_nonneg hx0.le _)) fun N => ?_
    have hterm : ∀ j, s j * x ^ j ≤ (if j < J then s j * x ^ j else 0) +
        2 / (1 - x) * (if J ≤ j then w j * (s j / 2 - 1) else 0) + 2 * x ^ j := by
      intro j
      by_cases hj : j < J
      · rw [if_pos hj, if_neg (by omega)]
        have := pow_nonneg hx0.le j
        linarith
      · rw [if_neg hj, if_pos (by omega), hw_eq]
        have e : 2 / (1 - x) * ((1 - x) * x ^ j * (s j / 2 - 1)) = x ^ j * (s j - 2) := by
          field_simp
        rw [e]
        linarith
    calc ∑ i ∈ Finset.range N, s i * x ^ i
        ≤ ∑ i ∈ Finset.range N, ((if i < J then s i * x ^ i else 0) +
            2 / (1 - x) * (if J ≤ i then w i * (s i / 2 - 1) else 0) + 2 * x ^ i) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ∑ i ∈ Finset.range N, (if i < J then s i * x ^ i else 0) +
            2 / (1 - x) * ∑ i ∈ Finset.range N, (if J ≤ i then w i * (s i / 2 - 1) else 0) +
            2 * ∑ i ∈ Finset.range N, x ^ i := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ A + 2 / (1 - x) * (Real.exp c * T) + 2 * ∑' j, x ^ j := by
          have h1 : ∑ i ∈ Finset.range N, (if i < J then s i * x ^ i else 0) ≤ A := by
            rw [← Finset.sum_filter, hA]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
              mul_nonneg (hs0 i) (pow_nonneg hx0.le _)
            intro i hi
            rw [Finset.mem_filter] at hi
            exact Finset.mem_range.2 hi.2
          have h2 := hcount N
          have h3 : ∑ i ∈ Finset.range N, x ^ i ≤ ∑' j, x ^ j :=
            hgeo.sum_le_tsum _ (fun i _ => pow_nonneg hx0.le _)
          have h4 : 0 ≤ 2 / (1 - x) := by positivity
          nlinarith
  -- Abel summation: from `∑ s_j x^j` to `∑ Ψ j x^j`
  have hD : Summable (fun j => (Ψ j - Ψ 0) * x ^ j) := by
    refine summable_of_sum_range_le (c := (∑' i, s i * x ^ i) * x / (1 - x))
      (fun j => mul_nonneg (by
        induction j with
        | zero => simp
        | succ j ih => linarith [hmono j]) (pow_nonneg hx0.le _)) fun N => ?_
    have hD0 : ∀ j, 0 ≤ Ψ j - Ψ 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => linarith [hmono j]
    rcases N with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty]
      have : 0 ≤ ∑' i, s i * x ^ i :=
        tsum_nonneg (fun i => mul_nonneg (hs0 i) (pow_nonneg hx0.le (n := i)))
      positivity
    · have hab := abel_identity Ψ x hx1.ne N
      have hrem : 0 ≤ (Ψ N - Ψ 0) * x ^ (N + 1) / (1 - x) := by
        have := hD0 N
        positivity
      have hR : ∑ i ∈ Finset.range N, (Ψ (i + 1) - Ψ i) * x ^ (i + 1) / (1 - x) ≤
          (∑' i, s i * x ^ i) * x / (1 - x) := by
        have e : ∑ i ∈ Finset.range N, (Ψ (i + 1) - Ψ i) * x ^ (i + 1) / (1 - x) =
            (∑ i ∈ Finset.range N, s i * x ^ i) * x / (1 - x) := by
          rw [Finset.sum_mul, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hs]
          ring
        rw [e]
        have := hsumS.sum_le_tsum (Finset.range N)
          (fun i _ => mul_nonneg (hs0 i) (pow_nonneg hx0.le _))
        have h5 : 0 ≤ x / (1 - x) := by positivity
        calc (∑ i ∈ Finset.range N, s i * x ^ i) * x / (1 - x)
            = (∑ i ∈ Finset.range N, s i * x ^ i) * (x / (1 - x)) := by ring
          _ ≤ (∑' i, s i * x ^ i) * (x / (1 - x)) := mul_le_mul_of_nonneg_right this h5
          _ = (∑' i, s i * x ^ i) * x / (1 - x) := by ring
      linarith
  have hfin := hD.add (hgeo.mul_left (Ψ 0))
  refine hfin.congr fun j => ?_
  ring

/-- **From dyadic sums to the integral**: `∑ ψ(e^j) e^{-j} < ∞` gives `∫_1^∞ ψ(s)/s² ds < ∞`. -/
theorem integrableOn_of_summable_exp (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (h : Summable (fun j : ℕ => ψ (Real.exp j) * Real.exp (-(j : ℝ)))) :
    IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1) := by
  set S : ℕ → Set ℝ := fun j => Set.Icc (Real.exp j) (Real.exp ((j : ℝ) + 1)) with hS
  have hU : (⋃ j, S j) = Set.Ici 1 := by
    ext x
    simp only [Set.mem_iUnion, hS, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨j, hj, -⟩
      exact (Real.one_le_exp (Nat.cast_nonneg j)).trans hj
    · intro hx
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
      refine ⟨⌊Real.log x⌋₊, ?_, ?_⟩
      · calc Real.exp (⌊Real.log x⌋₊ : ℝ) ≤ Real.exp (Real.log x) :=
              Real.exp_le_exp.2 (Nat.floor_le hlog)
          _ = x := Real.exp_log (by linarith)
      · calc x = Real.exp (Real.log x) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp ((⌊Real.log x⌋₊ : ℝ) + 1) :=
              Real.exp_le_exp.2 (Nat.lt_floor_add_one _).le
  rw [← hU]
  -- a measurable representative on `[1, ∞)`
  have hg : Measurable (fun s : ℝ => psiBar ψ s / s ^ 2) :=
    (psiBar_mono ψ hψ_mono).measurable.div (continuous_pow 2).measurable
  have hfg : ∀ j, ∀ x ∈ S j, ψ x / x ^ 2 = psiBar ψ x / x ^ 2 := by
    intro j x hx
    have hx1 : 1 ≤ x := (Real.one_le_exp (Nat.cast_nonneg j)).trans hx.1
    simp [psiBar, max_eq_left hx1]
  set bnd : ℕ → ℝ := fun j =>
    (|ψ (Real.exp ((j : ℝ) + 1))| + |ψ 1|) * Real.exp (-(2 * (j : ℝ))) with hbnd
  have hbound : ∀ j, ∀ x ∈ S j, ‖ψ x / x ^ 2‖ ≤ bnd j := by
    intro j x hx
    have hx1 : 1 ≤ x := (Real.one_le_exp (Nat.cast_nonneg j)).trans hx.1
    have hxpos : 0 < x := by linarith
    have hψx : |ψ x| ≤ |ψ (Real.exp ((j : ℝ) + 1))| + |ψ 1| := by
      have h1 : ψ 1 ≤ ψ x := hψ_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx1) hx1
      have h2 : ψ x ≤ ψ (Real.exp ((j : ℝ) + 1)) :=
        hψ_mono (Set.mem_Ici.2 hx1) (Set.mem_Ici.2 (hx1.trans hx.2)) hx.2
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (ψ 1), abs_nonneg (ψ (Real.exp ((j : ℝ) + 1)))]
      · linarith [le_abs_self (ψ (Real.exp ((j : ℝ) + 1))), abs_nonneg (ψ 1)]
    have hx2 : Real.exp (2 * (j : ℝ)) ≤ x ^ 2 := by
      rw [show 2 * (j : ℝ) = (j : ℝ) + j by ring, Real.exp_add, sq]
      exact mul_le_mul hx.1 hx.1 (Real.exp_pos _).le hxpos.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2), hbnd]
    simp only
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div₀ (by positivity) hψx (Real.exp_pos _) hx2
  have hint : ∀ j, IntegrableOn (fun s => ψ s / s ^ 2) (S j) := by
    intro j
    refine IntegrableOn.of_bound (C := bnd j) (by simp [hS, Real.volume_Icc]) ?_ ?_
    · refine hg.aestronglyMeasurable.congr ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => ?_)
      exact (hfg j x hx).symm
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (hbound j))
  refine integrableOn_iUnion_of_summable_integral_norm hint ?_
  -- summability of the pieces
  have hsum1 : Summable (fun j : ℕ => |ψ (Real.exp ((j : ℝ) + 1))| * Real.exp (-(j : ℝ))) := by
    have h1 := (summable_nat_add_iff 1).2 h.abs
    have h2 := h1.mul_left (Real.exp 1)
    refine h2.congr fun j => ?_
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
    push_cast
    have e1 : Real.exp (-((j : ℝ) + 1)) = Real.exp (-(j : ℝ)) * Real.exp (-1) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1]
    have : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp 1 * (|ψ (Real.exp ((j : ℝ) + 1))| * (Real.exp (-(j : ℝ)) * Real.exp (-1)))
        = |ψ (Real.exp ((j : ℝ) + 1))| * Real.exp (-(j : ℝ)) * (Real.exp 1 * Real.exp (-1)) := by
          ring
      _ = |ψ (Real.exp ((j : ℝ) + 1))| * Real.exp (-(j : ℝ)) := by rw [this, mul_one]
  have hsum2 : Summable (fun j : ℕ => Real.exp 1 *
      ((|ψ (Real.exp ((j : ℝ) + 1))| + |ψ 1|) * Real.exp (-(j : ℝ)))) := by
    refine Summable.mul_left _ ?_
    simp_rw [add_mul]
    exact hsum1.add (Real.summable_exp_neg_nat.mul_left _)
  refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) (fun j => ?_)
    hsum2
  have hle : ‖∫ x in S j, ‖ψ x / x ^ 2‖‖ ≤ bnd j * volume.real (S j) :=
    norm_setIntegral_le_of_norm_le_const (by simp [hS, Real.volume_Icc])
      (fun x hx => by rw [norm_norm]; exact hbound j x hx)
  rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at hle
  refine hle.trans ?_
  have hej : Real.exp (j : ℝ) ≤ Real.exp ((j : ℝ) + 1) := Real.exp_le_exp.2 (by linarith)
  rw [hS]
  simp only
  rw [Real.volume_real_Icc_of_le hej, hbnd]
  simp only
  have hvol : Real.exp ((j : ℝ) + 1) - Real.exp j ≤ Real.exp 1 * Real.exp (j : ℝ) := by
    rw [Real.exp_add]
    nlinarith [Real.exp_pos (j : ℝ), Real.exp_pos 1]
  have hA : 0 ≤ |ψ (Real.exp ((j : ℝ) + 1))| + |ψ 1| := by positivity
  calc (|ψ (Real.exp ((j : ℝ) + 1))| + |ψ 1|) * Real.exp (-(2 * (j : ℝ))) *
        (Real.exp ((j : ℝ) + 1) - Real.exp j)
      ≤ (|ψ (Real.exp ((j : ℝ) + 1))| + |ψ 1|) * Real.exp (-(2 * (j : ℝ))) *
        (Real.exp 1 * Real.exp (j : ℝ)) :=
        mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = Real.exp 1 * ((|ψ (Real.exp ((j : ℝ) + 1))| + |ψ 1|) *
        (Real.exp (-(2 * (j : ℝ))) * Real.exp (j : ℝ))) := by ring
    _ = Real.exp 1 * ((|ψ (Real.exp ((j : ℝ) + 1))| + |ψ 1|) * Real.exp (-(j : ℝ))) := by
        rw [← Real.exp_add]
        congr 3
        ring

/-- **Carleman's divergence, one-dimensional core** (pure real analysis): `∑ e^{-L_k} = ∞`. -/
theorem not_summable_exp_neg_carlemanL (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)))
    (hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1)) :
    ¬ Summable (fun k => 1 / Real.exp (carlemanL ψ k)) := by
  obtain ⟨σ₀, hconv⟩ := hψ_convex
  intro hsum
  apply hψ_div
  refine integrableOn_of_summable_exp ψ hψ_mono ?_
  set J : ℕ := ⌈σ₀⌉₊ with hJ
  have hJσ : σ₀ ≤ (J : ℝ) := Nat.le_ceil σ₀
  have hmono : ∀ j : ℕ, ψ (Real.exp (j : ℝ)) ≤ ψ (Real.exp ((j + 1 : ℕ) : ℝ)) := by
    intro j
    have h1 : (1 : ℝ) ≤ Real.exp (j : ℝ) := Real.one_le_exp (Nat.cast_nonneg j)
    exact hψ_mono (Set.mem_Ici.2 h1) (Set.mem_Ici.2 (h1.trans (Real.exp_le_exp.2 (by simp))))
      (Real.exp_le_exp.2 (by simp))
  have hconv' : ∀ j : ℕ, J ≤ j →
      ψ (Real.exp ((j + 1 : ℕ) : ℝ)) - ψ (Real.exp (j : ℝ)) ≤
        ψ (Real.exp ((j + 2 : ℕ) : ℝ)) - ψ (Real.exp ((j + 1 : ℕ) : ℝ)) := by
    intro j hj
    have hjσ : σ₀ ≤ (j : ℝ) := hJσ.trans (by exact_mod_cast hj)
    have hsl := hconv.slope_mono_adjacent (x := (j : ℝ)) (y := (j : ℝ) + 1) (z := (j : ℝ) + 2)
      (Set.mem_Ici.2 hjσ) (Set.mem_Ici.2 (by linarith)) (by linarith) (by linarith)
    have e1 : ((j : ℝ) + 1) - j = 1 := by ring
    have e2 : ((j : ℝ) + 2) - ((j : ℝ) + 1) = 1 := by ring
    rw [e1, e2, div_one, div_one] at hsl
    push_cast
    convert hsl using 3 <;> ring_nf
  have hΛ : ∀ j : ℕ, J ≤ j → ∀ k : ℕ, 1 ≤ k →
      2 * (k : ℝ) ≤ ψ (Real.exp ((j + 1 : ℕ) : ℝ)) - ψ (Real.exp (j : ℝ)) →
      carlemanL ψ k ≤ j + (1 + |ψ 1|) := by
    intro j hj k hk hsl
    have hjσ : σ₀ ≤ (j : ℝ) := hJσ.trans (by exact_mod_cast hj)
    have := carlemanL_le_of_slope ψ hψ_mono hψ_log σ₀ hconv j hjσ k hk (by
      push_cast at hsl
      exact hsl)
    linarith
  have hsum' : Summable (fun k => Real.exp (-carlemanL ψ k)) :=
    hsum.congr fun k => by rw [one_div, Real.exp_neg]
  exact summable_of_block_bound (fun j => ψ (Real.exp (j : ℝ))) J hmono hconv'
    (carlemanL ψ) (1 + |ψ 1|) hΛ hsum'

/-- **Carleman's divergence, one-dimensional core**: radii `R_k = e^{L_k}` with
`r^k e^{-ψ̄(r)/2} ≤ R_kᵏ` for all `r ≥ 0` and `∑ 1/R_k = ∞`. -/
theorem exists_carleman_radii (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)))
    (hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1)) :
    ∃ R : ℕ → ℝ, (∀ k, 0 < R k) ∧
      (∀ k, 1 ≤ k → ∀ r, 0 ≤ r → r ^ k * Real.exp (-(psiBar ψ r / 2)) ≤ R k ^ k) ∧
      ¬ Summable (fun k => 1 / R k) :=
  ⟨fun k => Real.exp (carlemanL ψ k), fun k => Real.exp_pos _,
    fun k hk r hr => pow_mul_exp_neg_psiBar_le ψ hψ_mono hψ_log k hk r hr,
    not_summable_exp_neg_carlemanL ψ hψ_mono hψ_log hψ_convex hψ_div⟩

/-- **Carleman's divergence condition** for the moment sequence of `e^{-ψ̄}`. -/
theorem not_summable_moment_bound (hn : 0 < n) (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)))
    (hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1)) (C : ℝ) (hC : 0 < C) :
    ¬ Summable (fun k : ℕ => (C * (2 * Real.pi) ^ k *
      ∫ y' : EuclideanSpace ℝ (Fin n), ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖)) ^ (-(1 : ℝ) / k)) := by
  obtain ⟨R, hRpos, hRbd, hRdiv⟩ := exists_carleman_radii ψ hψ_mono hψ_log hψ_convex hψ_div
  have hψ2_mono : MonotoneOn (fun s => ψ s / 2) (Set.Ici 1) := fun a ha b hb hab => by
    have := hψ_mono ha hb hab
    simp only
    linarith
  have hψ2_log : Tendsto (fun s => (ψ s / 2) / Real.log s) atTop atTop := by
    have : (fun s => (ψ s / 2) / Real.log s) = fun s => (1 / 2) * (ψ s / Real.log s) := by
      funext s; ring
    rw [this]
    exact hψ_log.const_mul_atTop (by norm_num)
  set B := ∫ y' : EuclideanSpace ℝ (Fin n), Real.exp (-(psiBar ψ ‖y'‖ / 2)) with hB
  have hBint : Integrable
      (fun y' : EuclideanSpace ℝ (Fin n) => Real.exp (-(psiBar ψ ‖y'‖ / 2))) := by
    have := integrable_pow_mul_exp_neg_psiBar (n := n) (fun s => ψ s / 2) hψ2_mono hψ2_log 0
    simpa [psiBar] using this
  have hBpos : 0 < B := by
    have := integral_pow_mul_exp_neg_psiBar_pos hn (fun s => ψ s / 2) hψ2_mono hψ2_log 0
    rw [hB]
    simpa [psiBar] using this
  set I : ℕ → ℝ := fun k =>
    ∫ y' : EuclideanSpace ℝ (Fin n), ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖) with hI
  have hIle : ∀ k, 1 ≤ k → I k ≤ R k ^ k * B := by
    intro k hk
    rw [hB, ← integral_const_mul]
    refine integral_mono (integrable_pow_mul_exp_neg_psiBar ψ hψ_mono hψ_log k)
      (hBint.const_mul _) (fun y' => ?_)
    have h1 := hRbd k hk ‖y'‖ (norm_nonneg _)
    have e : Real.exp (-psiBar ψ ‖y'‖) =
        Real.exp (-(psiBar ψ ‖y'‖ / 2)) * Real.exp (-(psiBar ψ ‖y'‖ / 2)) := by
      rw [← Real.exp_add]; ring_nf
    show ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖) ≤ R k ^ k * Real.exp (-(psiBar ψ ‖y'‖ / 2))
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hIpos : ∀ k, 0 < I k := fun k => integral_pow_mul_exp_neg_psiBar_pos hn ψ hψ_mono hψ_log k
  set c₀ := min 1 (C * B)⁻¹ with hc₀
  have hCB : 0 < C * B := mul_pos hC hBpos
  have hc₀pos : 0 < c₀ := lt_min one_pos (inv_pos.2 hCB)
  have hterm : ∀ k, 1 ≤ k →
      c₀ / (2 * Real.pi) * (1 / R k) ≤ (C * (2 * Real.pi) ^ k * I k) ^ (-(1 : ℝ) / k) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hRk := hRpos k
    have hMpos : 0 < C * (2 * Real.pi) ^ k * I k := by
      have := hIpos k
      positivity
    have hMle : C * (2 * Real.pi) ^ k * I k ≤ (C * B) * (2 * Real.pi * R k) ^ k := by
      calc C * (2 * Real.pi) ^ k * I k ≤ C * (2 * Real.pi) ^ k * (R k ^ k * B) :=
            mul_le_mul_of_nonneg_left (hIle k hk) (by positivity)
        _ = (C * B) * (2 * Real.pi * R k) ^ k := by rw [mul_pow]; ring
    have hexp : -(1 : ℝ) / k ≤ 0 := by
      rw [neg_div]
      exact neg_nonpos.2 (by positivity)
    have hc₀le : c₀ ≤ (C * B) ^ (-(1 : ℝ) / k) := by
      rcases le_or_gt 1 (C * B) with h | h
      · calc c₀ ≤ (C * B)⁻¹ := min_le_right _ _
          _ = (C * B) ^ (-(1 : ℝ)) := (Real.rpow_neg_one _).symm
          _ ≤ (C * B) ^ (-(1 : ℝ) / k) := by
            refine Real.rpow_le_rpow_of_exponent_le h ?_
            rw [neg_div, neg_le_neg_iff, div_le_one hkpos]
            exact hk1
      · calc c₀ ≤ 1 := min_le_left _ _
          _ ≤ (C * B) ^ (-(1 : ℝ) / k) :=
            Real.one_le_rpow_of_pos_of_le_one_of_nonpos hCB h.le hexp
    calc c₀ / (2 * Real.pi) * (1 / R k) = c₀ * (2 * Real.pi * R k)⁻¹ := by
          field_simp
      _ ≤ (C * B) ^ (-(1 : ℝ) / k) * (2 * Real.pi * R k)⁻¹ :=
          mul_le_mul_of_nonneg_right hc₀le (by positivity)
      _ = ((C * B) * (2 * Real.pi * R k) ^ k) ^ (-(1 : ℝ) / k) := by
          rw [Real.mul_rpow hCB.le (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity)]
          congr 1
          rw [show (k : ℝ) * (-(1 : ℝ) / k) = -1 by field_simp, Real.rpow_neg_one]
      _ ≤ (C * (2 * Real.pi) ^ k * I k) ^ (-(1 : ℝ) / k) :=
          Real.rpow_le_rpow_of_nonpos hMpos hMle hexp
  intro hsum
  apply hRdiv
  have h1 : Summable (fun k : ℕ =>
      (C * (2 * Real.pi) ^ (k + 1) * I (k + 1)) ^ (-(1 : ℝ) / ((k + 1 : ℕ) : ℝ))) :=
    (summable_nat_add_iff 1).2 hsum
  have h2 : Summable (fun k : ℕ => c₀ / (2 * Real.pi) * (1 / R (k + 1))) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => hterm (k + 1) (by omega)) h1
    have := hRpos (k + 1)
    positivity
  have h3 : Summable (fun k : ℕ => 1 / R (k + 1)) := by
    have := h2.mul_left (c₀ / (2 * Real.pi))⁻¹
    refine this.congr (fun k => ?_)
    have : c₀ / (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  exact (summable_nat_add_iff 1).1 h3

/-- **Quasianalytic uniqueness for the Fourier transform.** A continuous function on `ℝⁿ`
bounded by `C e^{-ψ̄(|y'|)}` all of whose moments vanish is zero (Denjoy–Carleman applied to
the restrictions of its Fourier transform to lines through `0`, then Fourier inversion). -/
theorem eq_zero_of_moments_eq_zero (hn : 0 < n) (ψ : ℝ → ℝ) (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)))
    (hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) (C : ℝ)
    (hfC : ∀ y', |f y'| ≤ C * Real.exp (-psiBar ψ ‖y'‖))
    (hmom : ∀ (e : EuclideanSpace ℝ (Fin n)) (k : ℕ), ∫ y', ⟪y', e⟫_ℝ ^ k * f y' = 0) :
    ∀ y', f y' = 0 := by
  by_cases hC : C ≤ 0
  · intro y'
    have h1 := hfC y'
    have h2 : C * Real.exp (-psiBar ψ ‖y'‖) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le
    exact abs_nonpos_iff.1 (h1.trans h2)
  push Not at hC
  set F : EuclideanSpace ℝ (Fin n) → ℂ := fun y' => (f y' : ℂ) with hFdef
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf
  have hFm : AEStronglyMeasurable F volume := hFc.aestronglyMeasurable
  set I : ℕ → ℝ := fun k =>
    ∫ y' : EuclideanSpace ℝ (Fin n), ‖y'‖ ^ k * Real.exp (-psiBar ψ ‖y'‖) with hI
  have hIint := integrable_pow_mul_exp_neg_psiBar (n := n) ψ hψ_mono hψ_log
  have hnormF : ∀ v, ‖F v‖ = |f v| := fun v => by simp [hFdef]
  have hFk : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * ‖F v‖) := by
    intro k
    refine ((hIint k).const_mul C).mono'
      ((continuous_norm.pow k).mul hFc.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnormF]
    calc ‖v‖ ^ k * |f v| ≤ ‖v‖ ^ k * (C * Real.exp (-psiBar ψ ‖v‖)) :=
          mul_le_mul_of_nonneg_left (hfC v) (by positivity)
      _ = C * (‖v‖ ^ k * Real.exp (-psiBar ψ ‖v‖)) := by ring
  have hFint : Integrable F := by
    have h0 := hFk 0
    have h0' : Integrable (fun v => ‖F v‖) := h0.congr (Filter.Eventually.of_forall fun v => by simp)
    exact (integrable_norm_iff hFm).1 h0'
  have hIpos : ∀ k, 0 < I k := fun k =>
    integral_pow_mul_exp_neg_psiBar_pos hn ψ hψ_mono hψ_log k
  have hline : ∀ e : EuclideanSpace ℝ (Fin n), ‖e‖ ≤ 1 → ∀ s : ℝ, 𝓕 F (s • e) = 0 := by
    intro e he s
    set g := VectorFourier.fourierIntegral Real.fourierChar volume (lineL e).toLinearMap₁₂ F
      with hg
    have hgsmooth : ContDiff ℝ ∞ g :=
      VectorFourier.contDiff_fourierIntegral (N := (⊤ : ℕ∞)) (lineL e) (fun k _ => hFk k)
    have hgderiv : ∀ k, iteratedFDeriv ℝ k g =
        VectorFourier.fourierIntegral Real.fourierChar volume (lineL e).toLinearMap₁₂
          (fun v => VectorFourier.fourierPowSMulRight (lineL e) F v k) := fun k =>
      VectorFourier.iteratedFDeriv_fourierIntegral (N := (⊤ : ℕ∞)) (lineL e)
        (fun j _ => hFk j) hFm (by exact_mod_cast le_top)
    have hbound : ∀ k x, ‖iteratedDeriv k g x‖ ≤ C * (2 * Real.pi) ^ k * I k := by
      intro k x
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hgderiv k]
      refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_
      calc ∫ v, ‖VectorFourier.fourierPowSMulRight (lineL e) F v k‖
          ≤ ∫ v, (2 * Real.pi) ^ k * (C * (‖v‖ ^ k * Real.exp (-psiBar ψ ‖v‖))) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
              (((hIint k).const_mul C).const_mul _) (Filter.Eventually.of_forall fun v => ?_)
            refine (VectorFourier.norm_fourierPowSMulRight_le (lineL e) F v k).trans ?_
            have hL : ‖lineL e‖ ≤ 1 := (norm_lineL_le e).trans he
            have h1 : (2 * Real.pi * ‖lineL e‖) ^ k ≤ (2 * Real.pi) ^ k :=
              pow_le_pow_left₀ (by positivity)
                (mul_le_of_le_one_right (by positivity) hL) k
            rw [hnormF]
            calc (2 * Real.pi * ‖lineL e‖) ^ k * ‖v‖ ^ k * |f v|
                ≤ (2 * Real.pi) ^ k * ‖v‖ ^ k * (C * Real.exp (-psiBar ψ ‖v‖)) := by
                  gcongr
                  exact hfC v
              _ = (2 * Real.pi) ^ k * (C * (‖v‖ ^ k * Real.exp (-psiBar ψ ‖v‖))) := by ring
        _ = C * (2 * Real.pi) ^ k * I k := by
            rw [integral_const_mul, integral_const_mul]
            ring
    have hzero : ∀ k, iteratedDeriv k g 0 = 0 := by
      intro k
      rw [iteratedDeriv_eq_iteratedFDeriv, hgderiv k,
        VectorFourier.fourierIntegral_continuousMultilinearMap_apply Real.continuous_fourierChar
          (VectorFourier.integrable_fourierPowSMulRight (lineL e) (hFk k) hFm)]
      have hpt : ∀ v, VectorFourier.fourierPowSMulRight (lineL e) F v k (fun _ => (1 : ℝ)) =
          (-(2 * (Real.pi : ℂ) * Complex.I)) ^ k * ((⟪v, e⟫_ℝ ^ k * f v : ℝ) : ℂ) := by
        intro v
        rw [VectorFourier.fourierPowSMulRight_apply]
        simp only [lineL, ContinuousLinearMap.coe_comp', Function.comp_apply,
          innerSL_apply_apply, ContinuousLinearMap.mul_apply', mul_one, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, hFdef, real_inner_comm e v]
        push_cast
        rw [Complex.real_smul]
        push_cast
        ring
      simp only [VectorFourier.fourierIntegral, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
        map_zero, neg_zero, AddChar.map_zero_eq_one, one_smul, hpt]
      rw [integral_const_mul, integral_complex_ofReal, hmom e k]
      simp
    have hdc := denjoy_carleman g (fun k => C * (2 * Real.pi) ^ k * I k) hgsmooth
      (fun k => by have := hIpos k; positivity) hbound hzero
      (not_summable_moment_bound hn ψ hψ_mono hψ_log hψ_convex hψ_div C hC)
    rw [← lineFourier_eq]
    exact hdc s
  have hFF : 𝓕 F = 0 := by
    funext ξ
    have hpos : 0 < ‖ξ‖ + 1 := by positivity
    have hξ : (‖ξ‖ + 1) • ((‖ξ‖ + 1)⁻¹ • ξ) = ξ := by
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    rw [← hξ]
    refine hline _ ?_ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), inv_mul_le_iff₀ hpos]
    linarith
  have key := hFc.fourierInv_fourier_eq hFint (by rw [hFF]; exact integrable_zero _ _ _)
  intro y'
  have h1 : F y' = 0 := by
    rw [← key, hFF]
    simp [Real.fourierInv_eq]
  simpa [hFdef] using h1

/-- **Lemma DC, flat case.** -/
theorem flat_DC (hn : 0 < n) (lam : ℝ) (hlam : 1 ≤ lam) (U : Space n → ℝ)
    (hU : HarmonicOnNhd U {y | lam < vcoord y}) (ψ : ℝ → ℝ) (Cu : ℝ)
    (hdecay : ∀ y, lam < vcoord y → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)))
    (hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1)) :
    ∀ y, lam + 1 < vcoord y → U y = 0 := by
  intro y hy
  set t := vcoord y with ht
  -- write `y = lift y' t`
  obtain ⟨p, rfl⟩ : ∃ p, F1.liftEquiv n p = y := (F1.liftEquiv n).surjective y
  rw [F1.liftEquiv_apply] at ht ⊢
  rw [vcoord_lift] at ht
  have hp2 : p.2 = t := ht.symm
  -- the slice is continuous
  have hcont : Continuous (fun y' : EuclideanSpace ℝ (Fin n) => U (lift y' t)) := by
    have hU' : ContinuousOn U {y | lam < vcoord y} := hU.continuousOn
    refine hU'.comp_continuous (F1.continuous_lift_left t) fun y' => ?_
    show lam < vcoord (lift y' t)
    rw [vcoord_lift]; linarith
  -- `Cu ≥ 0`
  have hCu : 0 ≤ Cu := by
    have h1 := hdecay (lift 0 t) (by rw [vcoord_lift]; linarith)
    have h2 := abs_nonneg (U (lift 0 t))
    have h3 := Real.exp_pos (-ψ ‖lift (0 : EuclideanSpace ℝ (Fin n)) t‖)
    by_contra hneg
    push Not at hneg
    nlinarith
  -- decay of the slice
  have hbound : ∀ y' : EuclideanSpace ℝ (Fin n),
      |U (lift y' t)| ≤ Cu * Real.exp (-psiBar ψ ‖y'‖) := by
    intro y'
    refine (hdecay _ (by rw [vcoord_lift]; linarith)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) hCu
    have h1 : max ‖y'‖ 1 ≤ ‖lift y' t‖ := by
      refine max_le (F1.norm_le_norm_lift y' t) ?_
      have := norm_lift_sq y' t
      have h4 : (1 : ℝ) ≤ t ^ 2 := by nlinarith
      nlinarith [norm_nonneg (lift y' t), sq_nonneg ‖y'‖]
    exact hψ_mono (Set.mem_Ici.2 (le_max_right _ _))
      (Set.mem_Ici.2 ((le_max_right _ _).trans h1)) h1
  have hzero := eq_zero_of_moments_eq_zero hn ψ hψ_mono hψ_log hψ_convex hψ_div
    (fun y' => U (lift y' t)) hcont Cu hbound
    (fun e k => flat_moments_eq_zero lam hlam U hU ψ Cu hdecay hψ_mono hψ_log t hy e k)
  rw [hp2]
  exact hzero p.1

end LPkg

open LPkg in
/-- **Lemma DC.** A harmonic function on a half-space `{⟪y, ν⟫ > λ}` that decays like
`e^{-ψ(|y|)}`, with `∫^∞ ψ(s)/s² ds = ∞` and `ψ` regular, vanishes on `{⟪y, ν⟫ > λ + 1}`. -/
theorem harmonic_halfSpace_eq_zero (hn : 0 < n) (ν : Space n) (hν : ‖ν‖ = 1) (lam : ℝ)
    (hlam : 1 ≤ lam) (U : Space n → ℝ) (hU : HarmonicOnNhd U {y | lam < ⟪y, ν⟫_ℝ})
    (ψ : ℝ → ℝ) (Cu : ℝ) (hdecay : ∀ y, lam < ⟪y, ν⟫_ℝ → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)))
    (hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1)) :
    ∀ y, lam + 1 < ⟪y, ν⟫_ℝ → U y = 0 := by
  obtain ⟨T, hT⟩ := exists_linearIsometryEquiv_ed ν hν
  have hinner : ∀ z : Space n, ⟪T z, ν⟫_ℝ = vcoord z := by
    intro z
    rw [← hT, LinearIsometryEquiv.inner_map_map, F1.inner_ed]
    rfl
  have hU' : HarmonicOnNhd (U ∘ T) {z | lam < vcoord z} := by
    intro z hz
    refine harmonicAt_comp_linearIsometryEquiv T (hU (T z) ?_)
    show lam < ⟪T z, ν⟫_ℝ
    rw [hinner]; exact hz
  have hdecay' : ∀ z, lam < vcoord z → |(U ∘ T) z| ≤ Cu * Real.exp (-ψ ‖z‖) := by
    intro z hz
    have := hdecay (T z) (by rw [hinner]; exact hz)
    simpa using this
  intro y hy
  have := flat_DC hn lam hlam (U ∘ T) hU' ψ Cu hdecay' hψ_mono hψ_log hψ_convex hψ_div
    (T.symm y) (by rw [← hinner, LinearIsometryEquiv.apply_symm_apply]; exact hy)
  simpa using this

end MazyaRefinedCauchy
