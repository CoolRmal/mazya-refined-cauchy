module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F1

The theorems stated in this file are the frozen contract of package F1 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

The proofs of the half-space divergence theorem for globally `C¹` fields follow the scouting
proof of concept of this project (`IBPScout.integral_halfSpace_divergence`), rewritten in terms of
`lift`.
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
  simp [vcoord, lift]

theorem norm_lift_sq (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖lift y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [lift]

namespace F1

/-! ### The horizontal embedding and the splitting `ℝⁿ⁺¹ = ℝⁿ × ℝ` -/

theorem lift_apply_castSucc (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) (j : Fin n) :
    lift y t (Fin.castSucc j) = y j := by
  simp [lift]

theorem lift_apply_last (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    lift y t (Fin.last n) = t := by
  simp [lift]

/-- The horizontal embedding `y ↦ lift y 0`, as a linear map. -/
noncomputable def horizL (n : ℕ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Space n where
  toFun y := lift y 0
  map_add' y z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [lift_apply_last]
    · simp [lift_apply_castSucc]
  map_smul' a y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [lift_apply_last]
    · simp [lift_apply_castSucc]

/-- The horizontal embedding `y ↦ lift y 0`, as a continuous linear map. -/
noncomputable def horiz (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] Space n :=
  LinearMap.toContinuousLinearMap (horizL n)

theorem horiz_apply (y : EuclideanSpace ℝ (Fin n)) : horiz n y = lift y 0 := rfl

theorem lift_eq (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) : lift y t = horiz n y + t • ed n := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [horiz_apply, lift_apply_last, ed]
  · simp [horiz_apply, lift_apply_castSucc, ed, Fin.castSucc_ne_last]

theorem continuous_lift :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => lift p.1 p.2) := by
  simp_rw [lift_eq]
  fun_prop

theorem horiz_single (j : Fin n) :
    horiz n (EuclideanSpace.single j 1) = EuclideanSpace.single (Fin.castSucc j) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [horiz_apply, lift_apply_last, Fin.castSucc_ne_last]
  · by_cases hk : k = j
    · subst hk; simp [horiz_apply, lift_apply_castSucc]
    · simp [horiz_apply, lift_apply_castSucc, hk]

theorem horiz_injective : Function.Injective (horiz n) := by
  intro y z h
  ext j
  have := congrArg (fun x : Space n => x (Fin.castSucc j)) h
  simpa [horiz_apply, lift_apply_castSucc] using this

/-- The measurable equivalence `(y, t) ↦ lift y t`. -/
noncomputable def liftEquiv (n : ℕ) : EuclideanSpace ℝ (Fin n) × ℝ ≃ᵐ Space n :=
  (((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.prodCongr (MeasurableEquiv.refl ℝ)).trans
    MeasurableEquiv.prodComm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm.trans
      (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)))

theorem liftEquiv_apply (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    liftEquiv n p = lift p.1 p.2 := by
  simp [liftEquiv, lift, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last']
  exact ⟨rfl, rfl⟩

theorem measurePreserving_liftEquiv :
    MeasurePreserving (liftEquiv n) (volume.prod volume) volume := by
  have h1 : MeasurePreserving
      ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.prodCongr (MeasurableEquiv.refl ℝ))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).prod
      (MeasurePreserving.id volume)
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodComm : (Fin n → ℝ) × ℝ ≃ᵐ ℝ × (Fin n → ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
    Measure.measurePreserving_swap
  have h3 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin (n + 1) → ℝ)) :=
    MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ)
      (Fin.last n))
  have h4 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))
      (volume : Measure (Fin (n + 1) → ℝ)) (volume : Measure (Space n)) :=
    MeasurePreserving.symm _
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1)))
  exact (h1.trans h2).trans (h3.trans h4)

/-- Fubini through `lift`: the integral over `ℝⁿ⁺¹` as an integral over `ℝⁿ × ℝ`. -/
theorem integral_eq_integral_prod_lift (f : Space n → ℝ) :
    ∫ x, f x = ∫ p, f (lift p.1 p.2) ∂(volume.prod volume) := by
  rw [← measurePreserving_liftEquiv.integral_comp' f]
  simp [liftEquiv_apply]

theorem integrable_comp_lift_iff (f : Space n → ℝ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ => f (lift p.1 p.2)) (volume.prod volume)
      ↔ Integrable f := by
  rw [← measurePreserving_liftEquiv.integrable_comp_emb (liftEquiv n).measurableEmbedding]
  simp [Function.comp_def, liftEquiv_apply]

theorem preimage_liftEquiv_halfSpace (η : ℝ) :
    liftEquiv n ⁻¹' {x : Space n | η < vcoord x} = Set.univ ×ˢ Set.Ioi η := by
  ext p
  simp [liftEquiv_apply, vcoord_lift]

/-- Fubini through `lift` on a half-space `{t > η}`. -/
theorem setIntegral_halfSpace_eq (η : ℝ) (g : Space n → ℝ) :
    ∫ x in {x : Space n | η < vcoord x}, g x
      = ∫ p, g (lift p.1 p.2) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
          (volume.restrict (Set.Ioi η))) := by
  rw [← measurePreserving_liftEquiv.setIntegral_preimage_emb (liftEquiv n).measurableEmbedding,
    preimage_liftEquiv_halfSpace, ← Measure.prod_restrict, Measure.restrict_univ]
  simp [liftEquiv_apply]

theorem integrable_halfSpace_lift (η : ℝ) (g : Space n → ℝ)
    (hg : IntegrableOn g {x : Space n | η < vcoord x}) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × ℝ => g (lift p.1 p.2))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume.restrict (Set.Ioi η))) := by
  have h := (measurePreserving_liftEquiv (n := n)).integrableOn_comp_preimage
    (liftEquiv n).measurableEmbedding (f := g) (s := {x : Space n | η < vcoord x})
  rw [preimage_liftEquiv_halfSpace] at h
  have h' := h.mpr hg
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h'
  simpa [Function.comp_def, liftEquiv_apply] using h'

/-- Fubini on a half-space `{t > η}`, horizontal variables outside. -/
theorem setIntegral_halfSpace_y_t (η : ℝ) (g : Space n → ℝ)
    (hg : IntegrableOn g {x : Space n | η < vcoord x}) :
    ∫ x in {x : Space n | η < vcoord x}, g x
      = ∫ y : EuclideanSpace ℝ (Fin n), ∫ t in Set.Ioi η, g (lift y t) := by
  rw [setIntegral_halfSpace_eq, integral_prod _ (integrable_halfSpace_lift η g hg)]

/-- Fubini on a half-space `{t > η}`, vertical variable outside. -/
theorem setIntegral_halfSpace_t_y (η : ℝ) (g : Space n → ℝ)
    (hg : IntegrableOn g {x : Space n | η < vcoord x}) :
    ∫ x in {x : Space n | η < vcoord x}, g x
      = ∫ t in Set.Ioi η, ∫ y : EuclideanSpace ℝ (Fin n), g (lift y t) := by
  rw [setIntegral_halfSpace_eq, integral_prod_symm _ (integrable_halfSpace_lift η g hg)]

/-! ### Directional derivatives of compactly supported functions -/

/-- Whole space: the integral of a directional derivative of a `C¹` compactly supported
function vanishes (from `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` with `f = 1`). -/
theorem integral_fderiv_apply_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] (G : E → ℝ) (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) (w : E) :
    ∫ y, fderiv ℝ G y w ∂μ = 0 := by
  have hcs : HasCompactSupport (fun x => fderiv ℝ G x w) :=
    (hGc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L w) (by simp)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
    (f := fun _ => (1 : ℝ)) (g := G) (v := w) (by simp)
    (by simpa using ((hG.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport hcs)
    (by simpa using hG.continuous.integrable_of_hasCompactSupport hGc)
    (fun _ _ => differentiableAt_const _) (fun x _ => (hG.differentiable one_ne_zero) x)
  simpa using h

theorem integrable_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    (G : E → ℝ) (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) (w : E) :
    Integrable (fun x => fderiv ℝ G x w) μ := by
  have hcs : HasCompactSupport (fun x => fderiv ℝ G x w) :=
    (hGc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L w) (by simp)
  exact ((hG.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport hcs

/-- Divergence theorem on a half-space, vertical component. -/
theorem integral_halfSpace_fderiv_ed (η : ℝ) (g : Space n → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫ x in {x : Space n | η < vcoord x}, fderiv ℝ g x (ed n)
      = -∫ y : EuclideanSpace ℝ (Fin n), g (lift y η) := by
  have hint : Integrable (fun x => fderiv ℝ g x (ed n)) := integrable_fderiv_apply g hg hgc _
  rw [setIntegral_halfSpace_y_t η _ hint.integrableOn, ← integral_neg]
  congr 1 with y
  have hv : ed n ≠ 0 := by simp [ed]
  set c : Space n := horiz n y
  let h : ℝ → ℝ := fun t => g (c + t • ed n)
  have hderiv : ∀ t, HasDerivAt h (fderiv ℝ g (c + t • ed n) (ed n)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => c + t • ed n) (ed n) t := by
      simpa using ((hasDerivAt_id t).smul_const (ed n)).const_add c
    exact ((hg.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t h1
  have hC1 : ContDiff ℝ 1 h := hg.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hemb : Topology.IsClosedEmbedding (fun t : ℝ => c + t • ed n) :=
    (Homeomorph.addLeft c).isClosedEmbedding.comp (isClosedEmbedding_smul_left hv)
  have hhc : HasCompactSupport h := hgc.comp_isClosedEmbedding hemb
  have key := hhc.integral_Ioi_deriv_eq hC1 η
  simp only [fun t => (hderiv t).deriv] at key
  simp only [lift_eq, c, h] at key ⊢
  exact key

/-- Divergence theorem on a half-space, horizontal components. -/
theorem integral_halfSpace_fderiv_castSucc (η : ℝ) (g : Space n → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (j : Fin n) :
    ∫ x in {x : Space n | η < vcoord x},
        fderiv ℝ g x (EuclideanSpace.single (Fin.castSucc j) 1) = 0 := by
  set w : Space n := EuclideanSpace.single (Fin.castSucc j) 1
  have hint : Integrable (fun x => fderiv ℝ g x w) := integrable_fderiv_apply g hg hgc _
  rw [setIntegral_halfSpace_t_y η _ hint.integrableOn]
  refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans (integral_zero _ _)
  set c : Space n := t • ed n
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun y => g (horiz n y + c)
  have hGd : ∀ y, HasFDerivAt G ((fderiv ℝ g (horiz n y + c)).comp (horiz n)) y := by
    intro y
    have h2 : HasFDerivAt (fun y => horiz n y + c) (horiz n) y :=
      (horiz n).hasFDerivAt.add_const c
    exact ((hg.differentiable one_ne_zero) _).hasFDerivAt.comp y h2
  have hG1 : ContDiff ℝ 1 G := hg.comp ((horiz n).contDiff.add contDiff_const)
  have hemb : Topology.IsClosedEmbedding (fun y => horiz n y + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.comp
      ((horiz n : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Space n).isClosedEmbedding_of_injective
        (LinearMap.ker_eq_bot.mpr horiz_injective))
  have hGc : HasCompactSupport G := hgc.comp_isClosedEmbedding hemb
  have key := integral_fderiv_apply_eq_zero (μ := volume) G hG1 hGc
    (EuclideanSpace.single j 1)
  simp only [fun y => (hGd y).fderiv, ContinuousLinearMap.comp_apply, horiz_single] at key
  rw [← key]
  congr 1 with y
  simp only [lift_eq, c, w]

/-- The divergence as a sum of partial derivatives of the components. -/
theorem divergence_eq_sum (F : Space n → Space n) (x : Space n)
    (hF : DifferentiableAt ℝ F x) :
    divergence F x = ∑ i, fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1) := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : fderiv ℝ (fun y => F y i) x = (EuclideanSpace.proj i).comp (fderiv ℝ F x) :=
    ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  simp [this, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem inner_ed (v : Space n) : ⟪v, ed n⟫_ℝ = v (Fin.last n) := by
  simp [ed, EuclideanSpace.inner_single_right]

/-- **Divergence theorem on a half-space** `{t > η}` for a globally `C¹` compactly supported
field. -/
theorem integral_divergence_halfSpace_of_contDiff (η : ℝ) (F : Space n → Space n)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ∫ x in {x : Space n | η < vcoord x}, divergence F x
      = -∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y η), ed n⟫_ℝ := by
  have hFi : ∀ i, ContDiff ℝ 1 (fun y => F y i) := fun i =>
    (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).contDiff.comp hF
  have hFic : ∀ i, HasCompactSupport (fun y => F y i) := fun i =>
    hFc.comp_left (g := fun v : Space n => v i) (by simp)
  have hint : ∀ i, IntegrableOn
      (fun x => fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1))
      {x : Space n | η < vcoord x} := fun i =>
    (integrable_fderiv_apply _ (hFi i) (hFic i) _).integrableOn
  simp_rw [fun x => divergence_eq_sum F x ((hF.differentiable one_ne_zero) x)]
  rw [integral_finsetSum _ (fun i _ => hint i), Fin.sum_univ_castSucc]
  simp only [integral_halfSpace_fderiv_castSucc η _ (hFi _) (hFic _), Finset.sum_const_zero,
    zero_add, inner_ed]
  exact integral_halfSpace_fderiv_ed η _ (hFi _) (hFic _)

/-! ### Localization: fields that are `C¹` only near the closed half-space -/

theorem vcoord_eq_proj : (vcoord : Space n → ℝ) = EuclideanSpace.proj (Fin.last n) := by
  funext x
  simp [vcoord]

theorem continuous_vcoord : Continuous (vcoord : Space n → ℝ) := by
  rw [vcoord_eq_proj]
  exact (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).continuous

theorem contDiff_vcoord : ContDiff ℝ 1 (vcoord : Space n → ℝ) := by
  rw [vcoord_eq_proj]
  exact (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).contDiff

theorem measurableSet_halfSpace (η : ℝ) : MeasurableSet {x : Space n | η < vcoord x} :=
  measurableSet_lt measurable_const continuous_vcoord.measurable

/-- The set of points near which `F` is `C¹` is open. -/
theorem isOpen_setOf_contDiffAt (F : Space n → Space n) :
    IsOpen {x | ContDiffAt ℝ 1 F x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact hx.eventually (by simp)

/-- If `F` is `C¹` near every point of `{t ≥ η}` and has compact support, then it is `C¹` near
every point of `{t ≥ a}` for some `a < η`. -/
theorem exists_lt_forall_contDiffAt (η : ℝ) (F : Space n → Space n)
    (hF : ∀ x, η ≤ vcoord x → ContDiffAt ℝ 1 F x) (hsupp : HasCompactSupport F) :
    ∃ a < η, ∀ x, a ≤ vcoord x → ContDiffAt ℝ 1 F x := by
  set S := {x | ¬ ContDiffAt ℝ 1 F x} with hS_def
  have hSc : IsClosed S := (isOpen_setOf_contDiffAt F).isClosed_compl
  have hSsub : S ⊆ tsupport F := by
    intro x hx
    by_contra hxt
    apply hx
    have h0 : F =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hxt
    exact contDiffAt_const.congr_of_eventuallyEq h0
  have hSk : IsCompact S := hsupp.isCompact.of_isClosed_subset hSc hSsub
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨η - 1, by linarith, fun x _ => ?_⟩
    by_contra h
    have hx : x ∈ S := h
    simp [hS] at hx
  · obtain ⟨s₀, hs₀, hmax⟩ := hSk.exists_isMaxOn hS continuous_vcoord.continuousOn
    have hlt : vcoord s₀ < η := by
      by_contra h
      push Not at h
      exact hs₀ (hF s₀ h)
    refine ⟨(vcoord s₀ + η) / 2, by linarith, fun x hx => ?_⟩
    by_contra h
    have := isMaxOn_iff.mp hmax x h
    linarith

/-- A field that is `C¹` near `{t ≥ η}` agrees on `{t > b}`, for some `b < η`, with a globally
`C¹` field with compact support. -/
theorem exists_contDiff_eq (η : ℝ) (F : Space n → Space n)
    (hF : ∀ x, η ≤ vcoord x → ContDiffAt ℝ 1 F x) (hsupp : HasCompactSupport F) :
    ∃ G : Space n → Space n, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ∃ b < η, ∀ x, b < vcoord x → G x = F x := by
  obtain ⟨a, ha, haF⟩ := exists_lt_forall_contDiffAt η F hF hsupp
  set a' := (a + η) / 2 with ha'
  set b := (a' + η) / 2 with hb
  have hab : a' < b := by rw [hb]; linarith
  let ψ : Space n → ℝ := fun x => Real.smoothTransition ((vcoord x - a') / (b - a'))
  have hψ : ContDiff ℝ 1 ψ :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_vcoord.sub contDiff_const).div_const _)
  refine ⟨fun x => ψ x • F x, ?_, ?_, b, by linarith, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : a < vcoord x
    · exact hψ.contDiffAt.smul (haF x hx.le)
    · have hopen : IsOpen {y : Space n | vcoord y < a'} :=
        isOpen_lt continuous_vcoord continuous_const
      have hxm : x ∈ {y : Space n | vcoord y < a'} := by
        simp only [Set.mem_ofPred_eq]; linarith
      have h0 : (fun x => ψ x • F x) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds hxm] with y hy
        simp only [ψ]
        rw [Real.smoothTransition.zero_of_nonpos, zero_smul]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      exact contDiffAt_const.congr_of_eventuallyEq h0
  · exact hsupp.smul_left (f := ψ)
  · intro x hx
    simp only [ψ]
    rw [Real.smoothTransition.one_of_one_le, one_smul]
    rw [le_div_iff₀ (by linarith)]
    linarith

/-! ### Uniform bounds for the limit `η → 0⁺` -/

theorem norm_le_norm_lift (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ‖y‖ ≤ ‖lift y t‖ := by
  have h := norm_lift_sq y t
  have h1 : 0 ≤ ‖y‖ := norm_nonneg _
  have h2 : 0 ≤ ‖lift y t‖ := norm_nonneg _
  nlinarith [sq_nonneg t]

theorem continuous_lift_left (t : ℝ) : Continuous (fun y : EuclideanSpace ℝ (Fin n) => lift y t) :=
  continuous_lift.comp (continuous_id.prodMk continuous_const)

theorem continuous_lift_right (y : EuclideanSpace ℝ (Fin n)) : Continuous (fun t : ℝ => lift y t) :=
  continuous_lift.comp (continuous_const.prodMk continuous_id)

end F1

open F1

/-- Fubini in the splitting `ℝⁿ⁺¹ = ℝⁿ × ℝ`. -/
theorem integral_eq_integral_lift (f : Space n → ℝ) (hf : Integrable f) :
    ∫ x, f x = ∫ y : EuclideanSpace ℝ (Fin n), ∫ t : ℝ, f (lift y t) := by
  rw [integral_eq_integral_prod_lift, integral_prod _ ((integrable_comp_lift_iff f).mpr hf)]

/-- Divergence theorem on the half-space `{t > η}` for a compactly supported field that is `C¹`
on a neighbourhood of the closed half-space; the outer normal is `-e_d`. -/
theorem integral_divergence_halfSpace (η : ℝ) (F : Space n → Space n)
    (hF : ∀ x, η ≤ vcoord x → ContDiffAt ℝ 1 F x) (hsupp : HasCompactSupport F) :
    ∫ x in {x : Space n | η < vcoord x}, divergence F x
      = -∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y η), ed n⟫_ℝ := by
  obtain ⟨G, hG, hGc, b, hb, hGF⟩ := exists_contDiff_eq η F hF hsupp
  have hdiv : Set.EqOn (divergence G) (divergence F) {x : Space n | η < vcoord x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    have hev : G =ᶠ[𝓝 x] F := by
      have hopen : IsOpen {y : Space n | b < vcoord y} :=
        isOpen_lt continuous_const continuous_vcoord
      filter_upwards [hopen.mem_nhds (show b < vcoord x by linarith)] with y hy
      exact hGF y hy
    simp only [divergence, hev.fderiv_eq]
  have hbd : ∀ y : EuclideanSpace ℝ (Fin n), G (lift y η) = F (lift y η) := fun y =>
    hGF _ (by rw [vcoord_lift]; linarith)
  rw [← setIntegral_congr_fun (measurableSet_halfSpace η) hdiv]
  simp_rw [← hbd]
  exact integral_divergence_halfSpace_of_contDiff η G hG hGc

/-- Divergence theorem on `{t > 0}` for a compactly supported field that is `C¹` in the open
half-space and only continuous up to `{t = 0}`, provided its divergence is integrable. -/
theorem integral_divergence_halfSpace_of_continuousOn (F : Space n → Space n)
    (hF : ∀ x, 0 < vcoord x → ContDiffAt ℝ 1 F x)
    (hFc : ContinuousOn F {x | 0 ≤ vcoord x}) (hsupp : HasCompactSupport F)
    (hint : IntegrableOn (divergence F) {x | 0 < vcoord x}) :
    ∫ x in {x : Space n | 0 < vcoord x}, divergence F x
      = -∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y 0), ed n⟫_ℝ := by
  -- the interior integrals converge by dominated convergence
  have hL : Tendsto (fun η => ∫ x in {x : Space n | η < vcoord x}, divergence F x) (𝓝[>] 0)
      (𝓝 (∫ x in {x : Space n | 0 < vcoord x}, divergence F x)) := by
    have heq : ∀ η : ℝ, 0 ≤ η → ∫ x in {x : Space n | η < vcoord x}, divergence F x
        = ∫ x in {x : Space n | 0 < vcoord x},
            Set.indicator {x : Space n | η < vcoord x} (divergence F) x := by
      intro η hη
      rw [setIntegral_indicator (measurableSet_halfSpace η)]
      congr 2
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨by linarith, h⟩
      · intro h; exact h.2
    refine Tendsto.congr' ?_ (tendsto_integral_filter_of_dominated_convergence
      (F := fun η x => Set.indicator {x : Space n | η < vcoord x} (divergence F) x)
      (fun x => ‖divergence F x‖) ?_ ?_ hint.norm ?_)
    · filter_upwards [self_mem_nhdsWithin] with η hη using (heq η (le_of_lt hη)).symm
    · exact Eventually.of_forall fun η =>
        hint.aestronglyMeasurable.indicator (measurableSet_halfSpace η)
    · refine Eventually.of_forall fun η => Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ {x : Space n | η < vcoord x}
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
    · rw [ae_restrict_iff' (measurableSet_halfSpace 0)]
      refine Eventually.of_forall fun x hx => ?_
      simp only [Set.mem_ofPred_eq] at hx
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hx] with η hη
      rw [Set.indicator_of_mem (show x ∈ {x : Space n | η < vcoord x} from hη.2)]
  -- the boundary integrals converge by dominated convergence
  have hR : Tendsto (fun η => ∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y η), ed n⟫_ℝ) (𝓝[>] 0)
      (𝓝 (∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y 0), ed n⟫_ℝ)) := by
    have hK : IsCompact (tsupport F ∩ {x : Space n | 0 ≤ vcoord x}) :=
      hsupp.isCompact.inter_right (isClosed_le continuous_const continuous_vcoord)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hFc.mono Set.inter_subset_right)
    have hM : ∀ x : Space n, 0 ≤ vcoord x → ‖F x‖ ≤ max C 0 := by
      intro x hx
      by_cases hxt : x ∈ tsupport F
      · exact (hC x ⟨hxt, hx⟩).trans (le_max_left _ _)
      · rw [image_eq_zero_of_notMem_tsupport hxt, norm_zero]; exact le_max_right _ _
    obtain ⟨R, hRsub⟩ := hsupp.isCompact.isBounded.subset_closedBall 0
    have hzero : ∀ x : Space n, R < ‖x‖ → F x = 0 := by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      have := hRsub hxt
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    have hed : ‖ed n‖ = 1 := by simp [ed]
    have hcont : ∀ η : ℝ, 0 ≤ η →
        Continuous (fun y : EuclideanSpace ℝ (Fin n) => ⟪F (lift y η), ed n⟫_ℝ) := by
      intro η hη
      have : Continuous (fun y : EuclideanSpace ℝ (Fin n) => F (lift y η)) :=
        hFc.comp_continuous (continuous_lift_left η) (fun y => by
          simp only [Set.mem_ofPred_eq, vcoord_lift]; exact hη)
      exact this.inner continuous_const
    refine tendsto_integral_filter_of_dominated_convergence
      (Set.indicator (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) (fun _ => max C 0))
      ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (hcont η (le_of_lt hη)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with η hη
      refine Eventually.of_forall fun y => ?_
      have hη' : (0 : ℝ) ≤ η := le_of_lt hη
      by_cases hy : ‖y‖ ≤ R
      · rw [Set.indicator_of_mem (by simpa using hy)]
        calc ‖⟪F (lift y η), ed n⟫_ℝ‖ ≤ ‖F (lift y η)‖ * ‖ed n‖ := norm_inner_le_norm _ _
          _ = ‖F (lift y η)‖ := by rw [hed, mul_one]
          _ ≤ max C 0 := hM _ (by rw [vcoord_lift]; exact hη')
      · push Not at hy
        rw [Set.indicator_of_notMem (by simpa using hy),
          hzero _ (lt_of_lt_of_le hy (norm_le_norm_lift y η))]
        simp
    · exact (integrableOn_const (measure_closedBall_lt_top).ne).integrable_indicator
        Metric.isClosed_closedBall.measurableSet
    · refine Eventually.of_forall fun y => ?_
      have hcw : ContinuousWithinAt F {x | 0 ≤ vcoord x} (lift y 0) :=
        hFc _ (by simp only [Set.mem_ofPred_eq, vcoord_lift]; exact le_rfl)
      have hl : Tendsto (fun η : ℝ => lift y η) (𝓝[>] 0)
          (𝓝[{x : Space n | 0 ≤ vcoord x}] (lift y 0)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨((continuous_lift_right y).tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with η hη
        simp only [vcoord_lift]
        exact le_of_lt hη
      exact (hcw.tendsto.comp hl).inner tendsto_const_nhds
  have heq : (fun η => ∫ x in {x : Space n | η < vcoord x}, divergence F x)
      =ᶠ[𝓝[>] 0] fun η => -∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y η), ed n⟫_ℝ := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact integral_divergence_halfSpace η F
      (fun x hx => hF x (lt_of_lt_of_le hη hx)) hsupp
  exact tendsto_nhds_unique (Tendsto.congr' heq hL) hR.neg

/-- The integral of the divergence of a compactly supported `C¹` field vanishes. -/
theorem integral_divergence_eq_zero (F : Space n → Space n) (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) : ∫ x, divergence F x = 0 := by
  have hFi : ∀ i, ContDiff ℝ 1 (fun y => F y i) := fun i =>
    (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).contDiff.comp hF
  have hFic : ∀ i, HasCompactSupport (fun y => F y i) := fun i =>
    hsupp.comp_left (g := fun v : Space n => v i) (by simp)
  simp_rw [fun x => divergence_eq_sum F x ((hF.differentiable one_ne_zero) x)]
  rw [integral_finsetSum _ (fun i _ => integrable_fderiv_apply _ (hFi i) (hFic i) _)]
  exact Finset.sum_eq_zero fun i _ => integral_fderiv_apply_eq_zero _ (hFi i) (hFic i) _

end MazyaRefinedCauchy
