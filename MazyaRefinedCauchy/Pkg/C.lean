module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1

@[expose] public section

/-!
# Work package C

The theorems stated in this file are the frozen contract of package C (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## Plan of the proof of `collar_reduction`

The proof is split into four independent parts, all in the namespace `MazyaRefinedCauchy.PkgC`.

1. `PkgC.exists_collarMap` (geometry): there are a smooth map `F`, a radius `R₀` and a constant
   `κ₀` with the properties bundled in `PkgC.CollarMap`: `F` sends `{t > 0}` into the domain,
   `{t = 0}` into the boundary piece and `{t ≤ 0}` outside the domain (all inside `B(0, R₀)`),
   it is bi-Lipschitz at `0`, injective with invertible derivative on `B(0, R₀)`, covers a
   neighbourhood of `0`, `DF⁻ᵀ e_d` is normal to the boundary, `a ν ∥ DF e_d` on `{t = 0}`, and
   `DF(0) DF(0)ᵀ = a(0)`. Construction: `F = F₀ ∘ L` with the conormal collar
   `F₀(x', t) = γ(x') + t a(γ(x')) ν̂(x')`, `ν̂ = -∇(graphFn Γ) ∘ γ`, and `L` the symmetric square
   root of `DF₀(0)⁻¹ a(0) DF₀(0)⁻ᵀ` (which is block diagonal).
2. `PkgC.transformed_equation` (calculus): `v = u ∘ F` solves a divergence-form equation with
   principal coefficient `PkgC.tildeA F a = DF⁻¹ (a ∘ F) DF⁻ᵀ`, a continuous first-order
   coefficient and zeroth-order coefficient `c ∘ F`.
3. `PkgC.globalize` (cutoff): a coefficient triple that is good on `B(0, R₀)` agrees on
   `B(0, R₀/2)` with a triple satisfying `GoodCoeffs` globally.
4. `PkgC.l2_comparison` (change of variables).

The assembly is `collar_reduction` at the end of the file. Status: everything in this file is
proved (no placeholders); `collar_reduction` depends only on `propext`, `Classical.choice` and
`Quot.sound`.

Implementation notes: in this module setting, instance-diamond unification on iterated operator
types such as `Space n →L[ℝ] Space n →L[ℝ] Space n` is fragile (`simp`/`rw` with `zero_smul`,
`norm_zero` may fail, and `HasCompactSupport.exists_bound_of_continuous` timed out), so such
facts are proved through general helper lemmas over abstract spaces or via
`ContinuousLinearMap.opNorm_zero`; traces are handled through `trace_eq_sum_basis`.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

namespace PkgC

/-! ### Elementary facts about the sets involved -/

theorem continuous_graphFn {Γ : (Fin n → ℝ) → ℝ} (hΓ : Continuous Γ) :
    Continuous (graphFn Γ) := by
  unfold graphFn
  fun_prop

theorem contDiff_graphFn {Γ : (Fin n → ℝ) → ℝ} {k : ℕ∞ω} (hΓ : ContDiff ℝ k Γ) :
    ContDiff ℝ k (graphFn Γ) := by
  unfold graphFn
  have h1 : ContDiff ℝ k (fun x : Space n => fun i : Fin n => x (Fin.castSucc i)) := by
    rw [contDiff_pi]
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i)).contDiff
  exact (hΓ.comp h1).sub (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).contDiff

theorem isOpen_domain {Γ : (Fin n → ℝ) → ℝ} (hΓ : Continuous Γ) (ρ : ℝ) :
    IsOpen (domain Γ ρ) := by
  have h1 : IsOpen {x : Space n | ‖x‖ < ρ} := isOpen_lt continuous_norm continuous_const
  have h2 : IsOpen {x : Space n | graphFn Γ x < 0} :=
    isOpen_lt (continuous_graphFn hΓ) continuous_const
  exact h1.inter h2

theorem domain_subset_domainWithBoundary (Γ : (Fin n → ℝ) → ℝ) (ρ : ℝ) :
    domain Γ ρ ⊆ domainWithBoundary Γ ρ := fun _ hx => ⟨hx.1, hx.2.le⟩

theorem boundaryPiece_subset_domainWithBoundary (Γ : (Fin n → ℝ) → ℝ) (ρ : ℝ) :
    boundaryPiece Γ ρ ⊆ domainWithBoundary Γ ρ := fun _ hx => ⟨hx.1, hx.2.le⟩

theorem continuous_vcoord' : Continuous (vcoord : Space n → ℝ) := by
  have : (vcoord : Space n → ℝ) = fun x => x (Fin.last n) := rfl
  rw [this]
  fun_prop

theorem isOpen_halfBall (R : ℝ) : IsOpen (halfBall n R) := by
  have h1 : IsOpen {x : Space n | ‖x‖ < R} := isOpen_lt continuous_norm continuous_const
  have h2 : IsOpen {x : Space n | 0 < vcoord x} := isOpen_lt continuous_const continuous_vcoord'
  exact h1.inter h2

theorem halfBall_subset_ball (R : ℝ) : halfBall n R ⊆ Metric.ball 0 R := by
  intro x hx
  simpa [Metric.mem_ball, dist_zero_right] using hx.1

theorem closedHalfBall_subset_ball (R : ℝ) : closedHalfBall n R ⊆ Metric.ball 0 R := by
  intro x hx
  simpa [Metric.mem_ball, dist_zero_right] using hx.1

theorem flatPiece_subset_ball (R : ℝ) : flatPiece n R ⊆ Metric.ball 0 R := by
  intro x hx
  simpa [Metric.mem_ball, dist_zero_right] using hx.1

theorem halfBall_mono {R R' : ℝ} (h : R ≤ R') : halfBall n R ⊆ halfBall n R' :=
  fun _ hx => ⟨hx.1.trans_le h, hx.2⟩

theorem closedHalfBall_mono {R R' : ℝ} (h : R ≤ R') : closedHalfBall n R ⊆ closedHalfBall n R' :=
  fun _ hx => ⟨hx.1.trans_le h, hx.2⟩

theorem flatPiece_mono {R R' : ℝ} (h : R ≤ R') : flatPiece n R ⊆ flatPiece n R' :=
  fun _ hx => ⟨hx.1.trans_le h, hx.2⟩

/-! ### The transformed principal coefficient -/

/-- The transformed principal coefficient `DF⁻¹ (a ∘ F) DF⁻ᵀ`. -/
noncomputable def tildeA (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (X : Space n) : Space n →L[ℝ] Space n :=
  (fderiv ℝ F X).inverse ∘L a (F X) ∘L ContinuousLinearMap.adjoint ((fderiv ℝ F X).inverse)

/-! ### Algebra of `tildeA` -/

theorem adjoint_inverse_adjoint_apply {T : Space n →L[ℝ] Space n} (hT : T.IsInvertible)
    (w : Space n) :
    ContinuousLinearMap.adjoint T.inverse (ContinuousLinearMap.adjoint T w) = w := by
  have h : ContinuousLinearMap.adjoint T.inverse ∘L ContinuousLinearMap.adjoint T =
      ContinuousLinearMap.id ℝ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hT.self_comp_inverse, ContinuousLinearMap.adjoint_id]
  exact DFunLike.congr_fun h w

theorem adjoint_adjoint_inverse_apply {T : Space n →L[ℝ] Space n} (hT : T.IsInvertible)
    (w : Space n) :
    ContinuousLinearMap.adjoint T (ContinuousLinearMap.adjoint T.inverse w) = w := by
  have h : ContinuousLinearMap.adjoint T ∘L ContinuousLinearMap.adjoint T.inverse =
      ContinuousLinearMap.id ℝ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hT.inverse_comp_self, ContinuousLinearMap.adjoint_id]
  exact DFunLike.congr_fun h w

theorem tildeA_symm (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (ha_symm : ∀ x ξ η, ⟪a x ξ, η⟫_ℝ = ⟪ξ, a x η⟫_ℝ) (X ξ η : Space n) :
    ⟪tildeA F a X ξ, η⟫_ℝ = ⟪ξ, tildeA F a X η⟫_ℝ := by
  simp only [tildeA, ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_right, ha_symm, ContinuousLinearMap.adjoint_inner_left]

theorem tildeA_adjoint_apply (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    {X : Space n} (hX : (fderiv ℝ F X).IsInvertible) (w : Space n) :
    tildeA F a X (ContinuousLinearMap.adjoint (fderiv ℝ F X) w) =
      (fderiv ℝ F X).inverse (a (F X) w) := by
  simp only [tildeA, ContinuousLinearMap.comp_apply, adjoint_inverse_adjoint_apply hX]

theorem inner_tildeA_self (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (X ξ : Space n) :
    ⟪tildeA F a X ξ, ξ⟫_ℝ = ⟪a (F X) (ContinuousLinearMap.adjoint (fderiv ℝ F X).inverse ξ),
      ContinuousLinearMap.adjoint (fderiv ℝ F X).inverse ξ⟫_ℝ := by
  simp only [tildeA, ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_right]

theorem tildeA_ell (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    {lam M : ℝ} (hlam : 0 < lam) (hM : 0 < M) (ha_ell : ∀ x ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x ξ, ξ⟫_ℝ)
    {X : Space n} (hX : (fderiv ℝ F X).IsInvertible) (hXM : ‖fderiv ℝ F X‖ ≤ M) (ξ : Space n) :
    lam / M ^ 2 * ‖ξ‖ ^ 2 ≤ ⟪tildeA F a X ξ, ξ⟫_ℝ := by
  rw [inner_tildeA_self]
  set w := ContinuousLinearMap.adjoint (fderiv ℝ F X).inverse ξ
  have hξ : ξ = ContinuousLinearMap.adjoint (fderiv ℝ F X) w :=
    (adjoint_adjoint_inverse_apply hX ξ).symm
  have hnorm : ‖ξ‖ ≤ M * ‖w‖ := by
    calc ‖ξ‖ = ‖ContinuousLinearMap.adjoint (fderiv ℝ F X) w‖ := by rw [← hξ]
      _ ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ F X)‖ * ‖w‖ :=
          (ContinuousLinearMap.adjoint (fderiv ℝ F X)).le_opNorm w
      _ = ‖fderiv ℝ F X‖ * ‖w‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ M * ‖w‖ := by gcongr
  have h1 : ‖ξ‖ ^ 2 ≤ M ^ 2 * ‖w‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg ξ) hnorm 2
    nlinarith [this]
  have h2 : lam * ‖w‖ ^ 2 ≤ ⟪a (F X) w, w⟫_ℝ := ha_ell _ w
  have hM2 : 0 < M ^ 2 := by positivity
  calc lam / M ^ 2 * ‖ξ‖ ^ 2 ≤ lam / M ^ 2 * (M ^ 2 * ‖w‖ ^ 2) := by gcongr
    _ = lam * ‖w‖ ^ 2 := by field_simp
    _ ≤ _ := h2

theorem tildeA_zero (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (h0 : (fderiv ℝ F 0).IsInvertible)
    (hat : fderiv ℝ F 0 ∘L ContinuousLinearMap.adjoint (fderiv ℝ F 0) = a 0) (hF0 : F 0 = 0) :
    tildeA F a 0 = ContinuousLinearMap.id ℝ (Space n) := by
  ext1 ξ
  simp only [tildeA, ContinuousLinearMap.comp_apply, hF0, ← hat,
    adjoint_adjoint_inverse_apply h0, h0.inverse_apply_self, ContinuousLinearMap.id_apply]

theorem tildeA_conormal (Γ : (Fin n → ℝ) → ℝ) (F : Space n → Space n)
    (a : Space n → Space n →L[ℝ] Space n) {X : Space n} (hX : (fderiv ℝ F X).IsInvertible)
    {μ : ℝ} (hμ : ∀ w, ⟪(fderiv ℝ F X).inverse w, ed n⟫_ℝ = μ * ⟪w, outerNormal Γ (F X)⟫_ℝ)
    {s : ℝ} (hs : a (F X) (outerNormal Γ (F X)) = s • fderiv ℝ F X (ed n)) :
    tildeA F a X (ed n) = (μ * s) • ed n := by
  have hadj : ContinuousLinearMap.adjoint (fderiv ℝ F X).inverse (ed n) =
      μ • outerNormal Γ (F X) := by
    apply ext_inner_right ℝ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, hμ, inner_smul_left]
    simp [real_inner_comm]
  simp only [tildeA, ContinuousLinearMap.comp_apply, hadj, map_smul, hs, hX.inverse_apply_self,
    smul_smul]

/-- The adjoint, as a real continuous linear equivalence. -/
noncomputable def adjointCLE : (Space n →L[ℝ] Space n) ≃L[ℝ] (Space n →L[ℝ] Space n) :=
  (ContinuousLinearMap.adjoint : (Space n →L[ℝ] Space n) ≃ₗᵢ⋆[ℝ] (Space n →L[ℝ] Space n)).toContinuousLinearEquiv

theorem adjointCLE_apply (T : Space n →L[ℝ] Space n) :
    adjointCLE T = ContinuousLinearMap.adjoint T := rfl

theorem contDiffOn_tildeA (F : Space n → Space n) (hF : ContDiff ℝ ∞ F)
    (a : Space n → Space n →L[ℝ] Space n) (ha : ContDiff ℝ ∞ a) (U : Set (Space n))
    (hU : IsOpen U) (hinv : ∀ X ∈ U, (fderiv ℝ F X).IsInvertible) :
    ContDiffOn ℝ 2 (tildeA F a) U := by
  intro X hX
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨e, he⟩ := hinv X hX
  have hDF : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hP : ContDiffAt ℝ 2 (fun Y => (fderiv ℝ F Y).inverse) X := by
    have h1 : ContDiffAt ℝ 2 ContinuousLinearMap.inverse (fderiv ℝ F X) := by
      rw [← he]; exact contDiffAt_map_inverse e
    exact h1.comp X hDF.contDiffAt
  have hPadj : ContDiffAt ℝ 2
      (fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y).inverse) X :=
    (adjointCLE (n := n)).contDiff.contDiffAt.comp X hP
  have haF : ContDiffAt ℝ 2 (fun Y => a (F Y)) X := ((ha.comp hF).of_le (by simp)).contDiffAt
  exact hP.clm_comp (haF.clm_comp hPadj)

/-! ### Auxiliary facts for the assembly -/

/-- `ellOp` only depends on the germ of `A` and on the values of `B` and `C` at the point. -/
theorem ellOp_congr {A A' : Space n → Space n →L[ℝ] Space n} {B B' : Space n → Space n}
    {C C' : Space n → ℝ} {v : Space n → ℝ} {x : Space n} (hA : A =ᶠ[𝓝 x] A')
    (hB : B x = B' x) (hC : C x = C' x) : ellOp A B C v x = ellOp A' B' C' v x := by
  unfold ellOp
  have h : (fun y => A y (gradient v y)) =ᶠ[𝓝 x] (fun y => A' y (gradient v y)) := by
    filter_upwards [hA] with y hy
    rw [hy]
  unfold divergence
  rw [h.fderiv_eq, hB, hC]

/-- The chain rule for the gradient: `∇(u ∘ F) x = DF(x)ᵀ ∇u(F x)`. -/
theorem gradient_comp {u : Space n → ℝ} {F : Space n → Space n} {x : Space n}
    (hu : DifferentiableAt ℝ u (F x)) (hF : DifferentiableAt ℝ F x) :
    gradient (fun y => u (F y)) x =
      ContinuousLinearMap.adjoint (fderiv ℝ F x) (gradient u (F x)) := by
  apply ext_inner_right ℝ
  intro w
  have : (fun y => u (F y)) = u ∘ F := rfl
  rw [this, inner_gradient_left, fderiv_comp x hu hF, ContinuousLinearMap.adjoint_inner_left,
    inner_gradient_left]
  rfl

/-! ### Part 1: the collar map -/

/-- The properties of the collar map `F` used in the assembly of `collar_reduction`. -/
structure CollarMap (Γ : (Fin n → ℝ) → ℝ) (ρ : ℝ) (a : Space n → Space n →L[ℝ] Space n)
    (F : Space n → Space n) (R₀ κ₀ : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ F
  R₀_pos : 0 < R₀
  one_le_κ₀ : 1 ≤ κ₀
  pos : ∀ X ∈ Metric.ball (0 : Space n) R₀, 0 < vcoord X → F X ∈ domain Γ ρ
  flat : ∀ X ∈ Metric.ball (0 : Space n) R₀, vcoord X = 0 → F X ∈ boundaryPiece Γ ρ
  nonpos : ∀ X ∈ Metric.ball (0 : Space n) R₀, vcoord X ≤ 0 → F X ∉ domain Γ ρ
  lip : ∀ X ∈ Metric.ball (0 : Space n) R₀, ‖F X‖ ≤ κ₀ * ‖X‖
  antilip : ∀ X ∈ Metric.ball (0 : Space n) R₀, ‖X‖ ≤ κ₀ * ‖F X‖
  cover : ∃ ε > 0, Metric.ball 0 ε ⊆ F '' Metric.ball 0 R₀
  injOn : Set.InjOn F (Metric.ball 0 R₀)
  invertible : ∀ X ∈ Metric.ball (0 : Space n) R₀, (fderiv ℝ F X).IsInvertible
  det_le : ∀ X ∈ Metric.ball (0 : Space n) R₀, |(fderiv ℝ F X).det| ≤ κ₀
  normal : ∀ X ∈ Metric.ball (0 : Space n) R₀, vcoord X = 0 → ∃ μ : ℝ, |μ| ≤ κ₀ ∧
    ∀ w, ⟪(fderiv ℝ F X).inverse w, ed n⟫_ℝ = μ * ⟪w, outerNormal Γ (F X)⟫_ℝ
  conormal : ∀ X ∈ Metric.ball (0 : Space n) R₀, vcoord X = 0 →
    ∃ s : ℝ, a (F X) (outerNormal Γ (F X)) = s • fderiv ℝ F X (ed n)
  at_zero : fderiv ℝ F 0 ∘L ContinuousLinearMap.adjoint (fderiv ℝ F 0) = a 0

/-! #### Sub-steps of the construction of the collar map

The proof of `exists_collarMap` is split as follows (all statements below are used in it).

* `exists_collar0`: the conormal collar `F₀(x', t) = γ(x') + t a(γ(x')) ν̂(x')`, where
  `γ(x') = (x', Γ(x'))` and `ν̂(x') = -∇(graphFn Γ)(γ(x'))`, with its first order properties:
  smoothness, `F₀ 0 = 0`, `F₀ {t = 0} ⊆ graph Γ`, transversality `∂_t (graphFn Γ ∘ F₀) < 0`
  near `0`, invertibility of `DF₀` near `0`, the normal relation `DF₀⁻ᵀ e_d ∥ outerNormal`
  (from `⟪∇ graphFn, DF₀ h⟫ = 0` for horizontal `h` on `{t = 0}`, i.e. the derivative of
  `graphFn Γ ∘ γ = 0`) and the conormal relation `a n ∥ DF₀ e_d = a(γ) ν̂`.
* `exists_normalization`: the block-diagonal symmetric square root `L` of
  `DF₀(0)⁻¹ a(0) DF₀(0)⁻ᵀ` (spectral theorem: `LinearMap.IsSymmetric.eigenvectorBasis`).
* `sign_of_vertical`: a `C¹` function vanishing on `{t = 0}` with `∂_t φ < 0` on a ball is
  negative on the upper half and positive on the lower half of the ball (mean value theorem on
  vertical segments, which stay in the ball).
* `local_diffeo`: inverse function theorem package for `F = F₀ ∘ L` at `0`.
-/

/-! #### The conormal collar `F₀` -/

/-- Horizontal coordinates `x ↦ (x (castSucc i))ᵢ`. -/
noncomputable def hproj (n : ℕ) : Space n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => EuclideanSpace.proj (Fin.castSucc i)

theorem hproj_apply (x : Space n) (i : Fin n) : hproj n x i = x (Fin.castSucc i) := rfl

/-- The point `(y, Γ y)` of the graph. -/
noncomputable def graphPt (Γ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : Space n :=
  lift (WithLp.toLp 2 y) (Γ y)

/-- The (non-normalized) inner normal `-∇(graphFn Γ)` at the graph point over `y`. -/
noncomputable def innerNormal (Γ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : Space n :=
  -gradient (graphFn Γ) (graphPt Γ y)

/-- The conormal collar `F₀(x', t) = γ(x') + t a(γ(x')) ν̂(x')`. -/
noncomputable def collar0 (Γ : (Fin n → ℝ) → ℝ) (a : Space n → Space n →L[ℝ] Space n)
    (X : Space n) : Space n :=
  graphPt Γ (hproj n X) + vcoord X • a (graphPt Γ (hproj n X)) (innerNormal Γ (hproj n X))

theorem graphPt_apply_castSucc (Γ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    graphPt Γ y (Fin.castSucc i) = y i := by
  simp [graphPt, F1.lift_apply_castSucc]

theorem graphPt_apply_last (Γ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) :
    graphPt Γ y (Fin.last n) = Γ y := by
  simp [graphPt, F1.lift_apply_last]

theorem graphFn_graphPt (Γ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : graphFn Γ (graphPt Γ y) = 0 := by
  unfold graphFn
  simp only [graphPt_apply_castSucc, graphPt_apply_last]
  exact sub_self _

theorem collar0_of_vcoord_eq_zero (Γ : (Fin n → ℝ) → ℝ) (a : Space n → Space n →L[ℝ] Space n)
    {X : Space n} (hX : vcoord X = 0) : collar0 Γ a X = graphPt Γ (hproj n X) := by
  rw [collar0, hX, zero_smul, add_zero]

theorem graphFn_collar0_flat (Γ : (Fin n → ℝ) → ℝ) (a : Space n → Space n →L[ℝ] Space n)
    {X : Space n} (hX : vcoord X = 0) : graphFn Γ (collar0 Γ a X) = 0 := by
  rw [collar0_of_vcoord_eq_zero Γ a hX, graphFn_graphPt]

theorem collar0_zero (Γ : (Fin n → ℝ) → ℝ) (hΓ0 : Γ 0 = 0)
    (a : Space n → Space n →L[ℝ] Space n) : collar0 Γ a 0 = 0 := by
  have hv : vcoord (0 : Space n) = 0 := by simp [vcoord]
  rw [collar0_of_vcoord_eq_zero Γ a hv, map_zero]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [graphPt_apply_last, hΓ0]; rfl
  · rw [graphPt_apply_castSucc]; rfl

theorem hproj_ed : hproj n (ed n) = 0 := by
  funext i
  rw [hproj_apply]
  simp [ed, Fin.castSucc_ne_last]

theorem vcoord_ed : vcoord (ed n) = 1 := by
  simp [vcoord, ed]

theorem hasFDerivAt_graphFn {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ) (x : Space n) :
    HasFDerivAt (graphFn Γ)
      ((fderiv ℝ Γ (hproj n x)).comp (hproj n) -
        (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ)) x := by
  have h1 : HasFDerivAt (fun y => Γ (hproj n y)) ((fderiv ℝ Γ (hproj n x)).comp (hproj n)) x :=
    ((hΓ.differentiable (by simp)) _).hasFDerivAt.comp x (hproj n).hasFDerivAt
  exact h1.sub (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).hasFDerivAt

theorem inner_gradient_graphFn_ed {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ) (x : Space n) :
    ⟪gradient (graphFn Γ) x, ed n⟫_ℝ = -1 := by
  rw [inner_gradient_left, (hasFDerivAt_graphFn hΓ x).fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, hproj_ed, map_zero]
  simp [ed]

theorem graphPt_eq (Γ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) :
    graphPt Γ y = F1.horiz n (WithLp.toLp 2 y) + Γ y • ed n :=
  F1.lift_eq _ _

theorem contDiff_graphPt {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ) :
    ContDiff ℝ ∞ (graphPt Γ) := by
  have h : graphPt Γ = fun y => F1.horiz n (WithLp.toLp 2 y) + Γ y • ed n :=
    funext (graphPt_eq Γ)
  rw [h]
  have h1 : ContDiff ℝ ∞ (fun y : Fin n → ℝ => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff
  exact ((F1.horiz n).contDiff.comp h1).add (hΓ.smul contDiff_const)

/-- `toDual.symm` as a real continuous linear equivalence. -/
noncomputable def toDualSymmCLE : StrongDual ℝ (Space n) ≃L[ℝ] Space n :=
  ((toDual ℝ (Space n)).symm : StrongDual ℝ (Space n) ≃ₗᵢ⋆[ℝ] Space n).toContinuousLinearEquiv

theorem contDiff_gradient_graphFn {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ) :
    ContDiff ℝ ∞ (gradient (graphFn Γ) : Space n → Space n) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ (graphFn Γ)) := (contDiff_graphFn hΓ).fderiv_right (by simp)
  exact (toDualSymmCLE (n := n)).contDiff.comp h1

theorem contDiff_collar0 {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ)
    {a : Space n → Space n →L[ℝ] Space n} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (collar0 Γ a) := by
  have hG : ContDiff ℝ ∞ (fun X : Space n => graphPt Γ (hproj n X)) :=
    (contDiff_graphPt hΓ).comp (hproj n).contDiff
  have hv : ContDiff ℝ ∞ (vcoord : Space n → ℝ) := by
    rw [F1.vcoord_eq_proj]; exact (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).contDiff
  have hN : ContDiff ℝ ∞ (fun X : Space n =>
      a (graphPt Γ (hproj n X)) (innerNormal Γ (hproj n X))) :=
    (ha.comp hG).clm_apply ((contDiff_gradient_graphFn hΓ).comp hG).neg
  exact hG.add (hv.smul hN)

theorem contDiff_conormalField {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ)
    {a : Space n → Space n →L[ℝ] Space n} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun y => a (graphPt Γ y) (innerNormal Γ y)) :=
  (ha.comp (contDiff_graphPt hΓ)).clm_apply
    ((contDiff_gradient_graphFn hΓ).comp (contDiff_graphPt hΓ)).neg

theorem hasFDerivAt_collar0 {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ)
    {a : Space n → Space n →L[ℝ] Space n} (ha : ContDiff ℝ ∞ a) (X : Space n) :
    HasFDerivAt (collar0 Γ a)
      ((fderiv ℝ (graphPt Γ) (hproj n X)).comp (hproj n) +
        (vcoord X • (fderiv ℝ (fun y => a (graphPt Γ y) (innerNormal Γ y)) (hproj n X)).comp
            (hproj n) +
          (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).smulRight
            (a (graphPt Γ (hproj n X)) (innerNormal Γ (hproj n X))))) X := by
  have hG : HasFDerivAt (fun X => graphPt Γ (hproj n X))
      ((fderiv ℝ (graphPt Γ) (hproj n X)).comp (hproj n)) X :=
    ((contDiff_graphPt hΓ).differentiable (by simp) _).hasFDerivAt.comp X (hproj n).hasFDerivAt
  have hN : HasFDerivAt (fun X => a (graphPt Γ (hproj n X)) (innerNormal Γ (hproj n X)))
      ((fderiv ℝ (fun y => a (graphPt Γ y) (innerNormal Γ y)) (hproj n X)).comp (hproj n)) X :=
    ((contDiff_conormalField hΓ ha).differentiable (by simp) _).hasFDerivAt.comp X
      (hproj n).hasFDerivAt
  have hv : HasFDerivAt (vcoord : Space n → ℝ)
      (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ) X := by
    rw [F1.vcoord_eq_proj]; exact (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).hasFDerivAt
  exact hG.add (hv.smul hN)

/-- `∂_t F₀ = a(γ) ν̂`. -/
theorem fderiv_collar0_ed {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ)
    {a : Space n → Space n →L[ℝ] Space n} (ha : ContDiff ℝ ∞ a) (X : Space n) :
    fderiv ℝ (collar0 Γ a) X (ed n) =
      a (graphPt Γ (hproj n X)) (innerNormal Γ (hproj n X)) := by
  rw [(hasFDerivAt_collar0 hΓ ha X).fderiv]
  have hpe : (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ) (ed n) = 1 := vcoord_ed
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, hproj_ed, map_zero,
    smul_zero, zero_add, hpe, one_smul]

theorem inner_gradient_fderiv_graphPt {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ)
    (y k : Fin n → ℝ) :
    ⟪gradient (graphFn Γ) (graphPt Γ y), fderiv ℝ (graphPt Γ) y k⟫_ℝ = 0 := by
  rw [inner_gradient_left]
  have h1 : fderiv ℝ (graphFn Γ ∘ graphPt Γ) y =
      fderiv ℝ (graphFn Γ) (graphPt Γ y) ∘L fderiv ℝ (graphPt Γ) y :=
    (((contDiff_graphFn hΓ).differentiable (by simp) _).hasFDerivAt.comp y
      ((contDiff_graphPt hΓ).differentiable (by simp) _).hasFDerivAt).fderiv
  have h2 : (graphFn Γ ∘ graphPt Γ) = fun _ => (0 : ℝ) := funext (graphFn_graphPt Γ)
  rw [h2, fderiv_const_apply] at h1
  have h3 := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L k) h1
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply] at h3
  exact h3.symm

/-- Tangency: on `{t = 0}`, `DF₀` maps horizontal vectors into the tangent space of the graph
(derivative of `graphFn Γ ∘ graphPt Γ = 0`). -/
theorem inner_gradient_fderiv_collar0_horizontal {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ)
    {a : Space n → Space n →L[ℝ] Space n} (ha : ContDiff ℝ ∞ a) {X h : Space n}
    (hX : vcoord X = 0) (hh : vcoord h = 0) :
    ⟪gradient (graphFn Γ) (collar0 Γ a X), fderiv ℝ (collar0 Γ a) X h⟫_ℝ = 0 := by
  rw [(hasFDerivAt_collar0 hΓ ha X).fderiv, collar0_of_vcoord_eq_zero Γ a hX]
  have hph : (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ) h = 0 := hh
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, hX, hph, zero_smul,
    add_zero]
  exact inner_gradient_fderiv_graphPt hΓ _ _

/-- `DF₀(0)` is invertible: test `DF₀(0) h = 0` against `∇ graphFn` (tangency and
`⟪∇g, a(0) ν̂⟫ = -⟪a ν̂, ν̂⟫ < 0`) to get `vcoord h = 0`, then read off the horizontal
coordinates. -/
theorem isInvertible_fderiv_collar0_zero {Γ : (Fin n → ℝ) → ℝ} (hΓ : ContDiff ℝ ∞ Γ)
    (hΓ0 : Γ 0 = 0) {a : Space n → Space n →L[ℝ] Space n} (ha : ContDiff ℝ ∞ a)
    (ha_ell : ∃ lam > 0, ∀ x ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x ξ, ξ⟫_ℝ) :
    (fderiv ℝ (collar0 Γ a) 0).IsInvertible := by
  obtain ⟨lam, hlam, hell⟩ := ha_ell
  have hv0 : vcoord (0 : Space n) = 0 := by simp [vcoord]
  have hπ0 : hproj n (0 : Space n) = 0 := map_zero _
  have hG0 : graphPt Γ (0 : Fin n → ℝ) = 0 := by
    have := collar0_zero Γ hΓ0 a
    rwa [collar0_of_vcoord_eq_zero Γ a hv0, hπ0] at this
  set g0 := gradient (graphFn Γ) (0 : Space n) with hg0
  have hT : ∀ h, fderiv ℝ (collar0 Γ a) 0 h =
      fderiv ℝ (graphPt Γ) 0 (hproj n h) + vcoord h • a 0 (-g0) := by
    intro h
    rw [(hasFDerivAt_collar0 hΓ ha 0).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, hv0, zero_smul,
      zero_add, hπ0, innerNormal, hG0]
    rfl
  have hpos0 : 0 < ⟪a 0 g0, g0⟫_ℝ := by
    have hne : g0 ≠ 0 := by
      intro h
      have := inner_gradient_graphFn_ed hΓ (0 : Space n)
      rw [← hg0, h, inner_zero_left] at this
      norm_num at this
    have h1 := hell 0 g0
    have h2 : 0 < ‖g0‖ := norm_pos_iff.mpr hne
    have h3 : 0 < lam * ‖g0‖ ^ 2 := by positivity
    linarith
  have htan : ∀ k, ⟪g0, fderiv ℝ (graphPt Γ) 0 k⟫_ℝ = 0 := by
    intro k
    have := inner_gradient_fderiv_graphPt hΓ (0 : Fin n → ℝ) k
    rwa [hG0] at this
  have hproj_d : ∀ k, hproj n (fderiv ℝ (graphPt Γ) 0 k) = k := by
    intro k
    have h1 : fderiv ℝ (hproj n ∘ graphPt Γ) 0 = (hproj n) ∘L fderiv ℝ (graphPt Γ) 0 :=
      ((hproj n).hasFDerivAt.comp 0
        ((contDiff_graphPt hΓ).differentiable (by simp) 0).hasFDerivAt).fderiv
    have h2 : hproj n ∘ graphPt Γ = id := funext fun y => by
      funext i; rw [Function.comp_apply, hproj_apply, graphPt_apply_castSucc]; rfl
    rw [h2, fderiv_id] at h1
    have h3 := congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L k) h1
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at h3
    exact h3.symm
  have hinj : Function.Injective (fderiv ℝ (collar0 Γ a) 0) := by
    intro h₁ h₂ heq
    have hTh : fderiv ℝ (collar0 Γ a) 0 (h₁ - h₂) = 0 := by rw [map_sub, heq, sub_self]
    rw [hT] at hTh
    have hd : vcoord (h₁ - h₂) = 0 := by
      have h1 := congrArg (fun v => ⟪g0, v⟫_ℝ) hTh
      simp only [inner_add_right, real_inner_smul_right, htan, zero_add, map_neg,
        inner_neg_right, inner_zero_right] at h1
      have h2 : ⟪g0, a 0 g0⟫_ℝ ≠ 0 := by rw [real_inner_comm]; exact hpos0.ne'
      simp only [mul_neg, neg_eq_zero, mul_eq_zero] at h1
      rcases h1 with h | h
      · exact h
      · exact absurd h h2
    have hh : hproj n (h₁ - h₂) = 0 := by
      rw [hd, zero_smul, add_zero] at hTh
      have := congrArg (hproj n) hTh
      rwa [hproj_d, map_zero] at this
    rw [← sub_eq_zero]
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [vcoord] using hd
    · have := congrFun hh j
      simpa [hproj_apply] using this
  let e := LinearEquiv.ofInjectiveEndo
    ((fderiv ℝ (collar0 Γ a) 0 : Space n →L[ℝ] Space n) : Space n →ₗ[ℝ] Space n) hinj
  exact ⟨e.toContinuousLinearEquiv, ContinuousLinearMap.ext fun x => rfl⟩

/-- The conormal collar `F₀` and its first order properties. Construction:
`F₀ X = γ (π X) + vcoord X • a (γ (π X)) (ν̂ (π X))` with `π X = (X (castSucc i))ᵢ`,
`γ y = toLp (Fin.snoc y (Γ y))` and `ν̂ y = - gradient (graphFn Γ) (γ y)`. -/
theorem exists_collar0 (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ) (hΓ0 : Γ 0 = 0)
    (a : Space n → Space n →L[ℝ] Space n) (ha : ContDiff ℝ ∞ a)
    (ha_symm : ∀ x ξ η, ⟪a x ξ, η⟫_ℝ = ⟪ξ, a x η⟫_ℝ)
    (ha_ell : ∃ lam > 0, ∀ x ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x ξ, ξ⟫_ℝ) :
    ∃ F₀ : Space n → Space n, ContDiff ℝ ∞ F₀ ∧ F₀ 0 = 0 ∧
      (∀ X, vcoord X = 0 → graphFn Γ (F₀ X) = 0) ∧
      ∃ r > 0, ∃ M : ℝ,
        (∀ X ∈ Metric.ball (0 : Space n) r, (fderiv ℝ F₀ X).IsInvertible) ∧
        (∀ X ∈ Metric.ball (0 : Space n) r,
          fderiv ℝ (fun Y => graphFn Γ (F₀ Y)) X (ed n) < 0) ∧
        (∀ X ∈ Metric.ball (0 : Space n) r, vcoord X = 0 → ∃ μ : ℝ, |μ| ≤ M ∧
          ∀ w, ⟪(fderiv ℝ F₀ X).inverse w, ed n⟫_ℝ = μ * ⟪w, outerNormal Γ (F₀ X)⟫_ℝ) ∧
        (∀ X ∈ Metric.ball (0 : Space n) r, vcoord X = 0 →
          ∃ s : ℝ, a (F₀ X) (outerNormal Γ (F₀ X)) = s • fderiv ℝ F₀ X (ed n)) := by
  obtain ⟨lam, hlam, hell⟩ := ha_ell
  have hF₀s : ContDiff ℝ ∞ (collar0 Γ a) := contDiff_collar0 hΓ ha
  have hgc : Continuous (gradient (graphFn Γ) : Space n → Space n) :=
    (contDiff_gradient_graphFn hΓ).continuous
  have hgne : ∀ x : Space n, gradient (graphFn Γ) x ≠ 0 := by
    intro x h
    have := inner_gradient_graphFn_ed hΓ x
    rw [h, inner_zero_left] at this
    norm_num at this
  have hgnorm : ∀ x : Space n, 0 < ‖gradient (graphFn Γ) x‖ := fun x =>
    norm_pos_iff.mpr (hgne x)
  have hnc : Continuous (fun X => outerNormal Γ (collar0 Γ a X)) := by
    unfold outerNormal
    have h1 : Continuous (fun X => gradient (graphFn Γ) (collar0 Γ a X)) :=
      hgc.comp hF₀s.continuous
    exact ((continuous_norm.comp h1).inv₀ (fun X => (hgnorm _).ne')).smul h1
  have hDF₀c : Continuous (fderiv ℝ (collar0 Γ a)) := hF₀s.continuous_fderiv (by simp)
  have hF₀0 : collar0 Γ a 0 = 0 := collar0_zero Γ hΓ0 a
  have hv0 : vcoord (0 : Space n) = 0 := by simp [vcoord]
  have hπ0 : hproj n (0 : Space n) = 0 := map_zero _
  have hG0 : graphPt Γ (0 : Fin n → ℝ) = 0 := by
    have := collar0_zero Γ hΓ0 a
    rwa [collar0_of_vcoord_eq_zero Γ a hv0, hπ0] at this
  have hDe0 : fderiv ℝ (collar0 Γ a) 0 (ed n) = -(a 0 (gradient (graphFn Γ) 0)) := by
    rw [fderiv_collar0_ed hΓ ha, hπ0, innerNormal, hG0, map_neg]
  have hpos0 : 0 < ⟪a 0 (gradient (graphFn Γ) 0), gradient (graphFn Γ) 0⟫_ℝ := by
    have h1 := hell 0 (gradient (graphFn Γ) 0)
    have h2 := hgnorm 0
    have h3 : 0 < lam * ‖gradient (graphFn Γ) (0 : Space n)‖ ^ 2 := by positivity
    linarith
  -- (i) invertibility near `0`
  have hinv0 := isInvertible_fderiv_collar0_zero hΓ hΓ0 ha ⟨lam, hlam, hell⟩
  have hopen : IsOpen {X : Space n | (fderiv ℝ (collar0 Γ a) X).IsInvertible} :=
    ContinuousLinearEquiv.isOpen.preimage hDF₀c
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp hopen 0 hinv0
  -- (ii) transversality
  have hφ : ∀ X, fderiv ℝ (fun Y => graphFn Γ (collar0 Γ a Y)) X (ed n) =
      ⟪gradient (graphFn Γ) (collar0 Γ a X), fderiv ℝ (collar0 Γ a) X (ed n)⟫_ℝ := by
    intro X
    have h1 := (((contDiff_graphFn hΓ).differentiable (by simp) (collar0 Γ a X)).hasFDerivAt.comp
      X ((hF₀s.differentiable (by simp)) X).hasFDerivAt).fderiv
    show fderiv ℝ (graphFn Γ ∘ collar0 Γ a) X (ed n) = _
    rw [h1, ContinuousLinearMap.comp_apply, inner_gradient_left]
  have hφc : Continuous (fun X =>
      ⟪gradient (graphFn Γ) (collar0 Γ a X), fderiv ℝ (collar0 Γ a) X (ed n)⟫_ℝ) :=
    (hgc.comp hF₀s.continuous).inner (hDF₀c.clm_apply continuous_const)
  have hφ0 : ⟪gradient (graphFn Γ) (collar0 Γ a 0), fderiv ℝ (collar0 Γ a) 0 (ed n)⟫_ℝ < 0 := by
    rw [hDe0, hF₀0, inner_neg_right, real_inner_comm]
    linarith
  obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.isOpen_iff.mp (isOpen_lt hφc continuous_const) 0 hφ0
  -- (iii) the normal relation
  have hψc : Continuous (fun X =>
      ⟪outerNormal Γ (collar0 Γ a X), fderiv ℝ (collar0 Γ a) X (ed n)⟫_ℝ) :=
    hnc.inner (hDF₀c.clm_apply continuous_const)
  have hψ0 : ⟪outerNormal Γ (collar0 Γ a 0), fderiv ℝ (collar0 Γ a) 0 (ed n)⟫_ℝ < 0 := by
    rw [hDe0, hF₀0, outerNormal, inner_neg_right, real_inner_smul_left, real_inner_comm]
    have := inv_pos.mpr (hgnorm 0)
    have := mul_pos this hpos0
    linarith
  set ψ0 := ⟪outerNormal Γ (collar0 Γ a 0), fderiv ℝ (collar0 Γ a) 0 (ed n)⟫_ℝ with hψ0def
  obtain ⟨r₃, hr₃, hr₃sub⟩ := Metric.isOpen_iff.mp (isOpen_lt hψc continuous_const) 0
    (show _ < ψ0 / 2 by linarith)
  refine ⟨collar0 Γ a, hF₀s, hF₀0, fun X hX => graphFn_collar0_flat Γ a hX,
    min r₁ (min r₂ r₃), lt_min hr₁ (lt_min hr₂ hr₃), 2 / |ψ0|, ?_, ?_, ?_, ?_⟩
  · intro X hX
    exact hr₁sub (Metric.ball_subset_ball (min_le_left _ _) hX)
  · intro X hX
    rw [hφ]
    exact hr₂sub (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hX)
  · intro X hX hXv
    have hXinv : (fderiv ℝ (collar0 Γ a) X).IsInvertible :=
      hr₁sub (Metric.ball_subset_ball (min_le_left _ _) hX)
    have hψX : ⟪outerNormal Γ (collar0 Γ a X), fderiv ℝ (collar0 Γ a) X (ed n)⟫_ℝ < ψ0 / 2 :=
      hr₃sub (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hX)
    set ψX := ⟪outerNormal Γ (collar0 Γ a X), fderiv ℝ (collar0 Γ a) X (ed n)⟫_ℝ with hψXdef
    have hψXneg : ψX < 0 := by linarith
    refine ⟨ψX⁻¹, ?_, fun w => ?_⟩
    · rw [abs_inv]
      have h1 : |ψ0| / 2 ≤ |ψX| := by
        rw [abs_of_neg hψ0, abs_of_neg hψXneg]; linarith
      have h2 : 0 < |ψ0| := abs_pos.mpr hψ0.ne
      calc |ψX|⁻¹ ≤ (|ψ0| / 2)⁻¹ := inv_anti₀ (by positivity) h1
        _ = 2 / |ψ0| := by rw [inv_div]
    · obtain ⟨z, hzdef⟩ : ∃ z, z = (fderiv ℝ (collar0 Γ a) X).inverse w := ⟨_, rfl⟩
      rw [← hzdef]
      have hw : w = fderiv ℝ (collar0 Γ a) X z := by
        rw [hzdef, hXinv.self_apply_inverse]
      obtain ⟨h, hhdef⟩ : ∃ h, h = z - vcoord z • ed n := ⟨_, rfl⟩
      have hh : vcoord h = 0 := by
        rw [hhdef]; simp [vcoord, ed]
      have hz : z = vcoord z • ed n + h := by
        rw [hhdef, add_sub_cancel]
      have htan : ⟪outerNormal Γ (collar0 Γ a X), fderiv ℝ (collar0 Γ a) X h⟫_ℝ = 0 := by
        rw [outerNormal, real_inner_smul_left,
          inner_gradient_fderiv_collar0_horizontal hΓ ha hXv hh, mul_zero]
      have hnw : ⟪w, outerNormal Γ (collar0 Γ a X)⟫_ℝ = vcoord z * ψX := by
        conv_lhs => rw [hw, hz]
        rw [map_add, map_smul, inner_add_left, real_inner_smul_left,
          real_inner_comm (outerNormal Γ (collar0 Γ a X)) (fderiv ℝ (collar0 Γ a) X h), htan,
          add_zero, hψXdef, real_inner_comm]
      have hze : ⟪z, ed n⟫_ℝ = vcoord z := F1.inner_ed z
      rw [hnw, hze, inv_mul_eq_div, mul_div_assoc, div_self hψXneg.ne, mul_one]
  · intro X _ hXv
    refine ⟨-(‖gradient (graphFn Γ) (collar0 Γ a X)‖)⁻¹, ?_⟩
    rw [fderiv_collar0_ed hΓ ha X, outerNormal, map_smul]
    conv_lhs => rw [collar0_of_vcoord_eq_zero Γ a hXv]
    rw [innerNormal, map_neg, smul_neg, neg_smul]
    conv_rhs => rw [collar0_of_vcoord_eq_zero Γ a hXv]
    rw [neg_neg]

/-- Symmetric square root of a symmetric positive definite operator which preserves the vertical
direction (spectral theorem). -/
theorem exists_sqrt (S : Space n →L[ℝ] Space n) (hS : ∀ ξ η, ⟪S ξ, η⟫_ℝ = ⟪ξ, S η⟫_ℝ)
    (hpos : ∀ ξ, ξ ≠ 0 → 0 < ⟪S ξ, ξ⟫_ℝ) (s : ℝ) (hs : S (ed n) = s • ed n) :
    ∃ L : Space n →L[ℝ] Space n, L.IsInvertible ∧ (∀ ξ η, ⟪L ξ, η⟫_ℝ = ⟪ξ, L η⟫_ℝ) ∧
      (∀ x, L (L x) = S x) ∧ L (ed n) = Real.sqrt s • ed n := by
  have hT : (S : Space n →ₗ[ℝ] Space n).IsSymmetric := fun x y => hS x y
  have hd : Module.finrank ℝ (Space n) = n + 1 := by simp
  set b := hT.eigenvectorBasis hd with hbdef
  set lam := hT.eigenvalues hd with hlamdef
  have hb : ∀ i, S (b i) = lam i • b i := fun i => by
    exact hT.apply_eigenvectorBasis hd i
  have hon : Orthonormal ℝ b := b.orthonormal
  have hlam : ∀ i, 0 < lam i := by
    intro i
    have h1 := hpos (b i) (hon.ne_zero i)
    rw [hb i, real_inner_smul_left, real_inner_self_eq_norm_sq, hon.1 i] at h1
    simpa using h1
  let D : (Fin (n + 1) → ℝ) → Space n →L[ℝ] Space n := fun c => LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, (c i * ⟪b i, x⟫_ℝ) • b i
      map_add' := fun x y => by
        simp only [inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [real_inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
        congr 1
        ext i
        ring_nf }
  have hD : ∀ c x, D c x = ∑ i, (c i * ⟪b i, x⟫_ℝ) • b i := fun c x => rfl
  have hDb : ∀ c x j, ⟪b j, D c x⟫_ℝ = c j * ⟪b j, x⟫_ℝ := fun c x j => by
    rw [hD]; exact hon.inner_right_fintype _ j
  have hext : ∀ x y : Space n, (∀ j, ⟪b j, x⟫_ℝ = ⟪b j, y⟫_ℝ) → x = y := fun x y h =>
    ext_inner_left_basis b.toBasis (fun j => by rw [b.coe_toBasis]; exact h j)
  have hDD : ∀ c c' x, D c (D c' x) = D (fun i => c i * c' i) x := by
    intro c c' x; apply hext; intro j; rw [hDb, hDb, hDb]; ring
  have hD1 : ∀ x, D (fun _ => 1) x = x := by
    intro x; apply hext; intro j; rw [hDb, one_mul]
  have hDS : ∀ x, D lam x = S x := by
    intro x; apply hext; intro j
    rw [hDb, ← real_inner_comm (b j) (S x), hS, hb j, real_inner_smul_right, real_inner_comm]
  have hDsymm : ∀ c ξ η, ⟪D c ξ, η⟫_ℝ = ⟪ξ, D c η⟫_ℝ := by
    intro c ξ η
    rw [hD, hD, sum_inner, inner_sum]
    congr 1
    ext i
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm (b i) ξ]
    ring
  refine ⟨D (fun i => Real.sqrt (lam i)), ?_, hDsymm _, ?_, ?_⟩
  · refine ContinuousLinearMap.IsInvertible.of_inverse (g := D (fun i => (Real.sqrt (lam i))⁻¹))
      ?_ ?_
    · ext1 x
      rw [ContinuousLinearMap.comp_apply, hDD, ContinuousLinearMap.id_apply]
      conv_rhs => rw [← hD1 x]
      congr 2
      ext i
      exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (hlam i)).ne'
    · ext1 x
      rw [ContinuousLinearMap.comp_apply, hDD, ContinuousLinearMap.id_apply]
      conv_rhs => rw [← hD1 x]
      congr 2
      ext i
      exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hlam i)).ne'
  · intro x
    rw [hDD, ← hDS]
    congr 2
    ext i
    exact Real.mul_self_sqrt (hlam i).le
  · apply hext
    intro j
    rw [hDb, real_inner_smul_right]
    have h1 : lam j * ⟪b j, ed n⟫_ℝ = s * ⟪b j, ed n⟫_ℝ := by
      rw [← real_inner_smul_left, ← hb j, hS, hs, real_inner_smul_right]
    by_cases h0 : ⟪b j, ed n⟫_ℝ = 0
    · rw [h0, mul_zero, mul_zero]
    · have : lam j = s := mul_right_cancel₀ h0 h1
      rw [this]

/-- The linear normalization: a block-diagonal symmetric `L` with
`M L Lᵀ Mᵀ = a₀`, provided `M⁻¹ a₀ M⁻ᵀ` preserves the vertical direction. -/
theorem exists_normalization (M : Space n →L[ℝ] Space n) (hM : M.IsInvertible)
    (a₀ : Space n →L[ℝ] Space n) (ha₀_symm : ∀ ξ η, ⟪a₀ ξ, η⟫_ℝ = ⟪ξ, a₀ η⟫_ℝ)
    (ha₀_pos : ∀ ξ, ξ ≠ 0 → 0 < ⟪a₀ ξ, ξ⟫_ℝ)
    (hblock : ∃ s : ℝ, M.inverse (a₀ (ContinuousLinearMap.adjoint M.inverse (ed n))) = s • ed n) :
    ∃ L : Space n →L[ℝ] Space n, L.IsInvertible ∧ (∀ ξ η, ⟪L ξ, η⟫_ℝ = ⟪ξ, L η⟫_ℝ) ∧
      (∃ ℓ : ℝ, 0 < ℓ ∧ L (ed n) = ℓ • ed n) ∧
      M ∘L L ∘L ContinuousLinearMap.adjoint L ∘L ContinuousLinearMap.adjoint M = a₀ := by
  obtain ⟨s, hs⟩ := hblock
  set S : Space n →L[ℝ] Space n :=
    M.inverse ∘L a₀ ∘L ContinuousLinearMap.adjoint M.inverse with hSdef
  have hSapp : ∀ ξ, S ξ = M.inverse (a₀ (ContinuousLinearMap.adjoint M.inverse ξ)) := fun ξ => rfl
  have hSsymm : ∀ ξ η, ⟪S ξ, η⟫_ℝ = ⟪ξ, S η⟫_ℝ := by
    intro ξ η
    rw [hSapp, hSapp, ← ContinuousLinearMap.adjoint_inner_right, ha₀_symm,
      ContinuousLinearMap.adjoint_inner_left]
  have hSpos : ∀ ξ, ξ ≠ 0 → 0 < ⟪S ξ, ξ⟫_ℝ := by
    intro ξ hξ
    rw [hSapp, ← ContinuousLinearMap.adjoint_inner_right]
    apply ha₀_pos
    intro h0
    apply hξ
    rw [← adjoint_adjoint_inverse_apply hM ξ, h0, map_zero]
  have hSe : S (ed n) = s • ed n := hs
  obtain ⟨L, hLinv, hLsymm, hLL, hLe⟩ := exists_sqrt S hSsymm hSpos s hSe
  have hed : ⟪ed n, ed n⟫_ℝ = 1 := by
    rw [F1.inner_ed]; simp [ed]
  have hspos : 0 < s := by
    have h1 := hSpos (ed n) (by
      intro h
      have := congrArg (fun v : Space n => ⟪v, ed n⟫_ℝ) h
      simp only [inner_zero_left] at this
      rw [hed] at this
      exact one_ne_zero this)
    rw [hSe, real_inner_smul_left, hed, mul_one] at h1
    exact h1
  refine ⟨L, hLinv, hLsymm, ⟨Real.sqrt s, Real.sqrt_pos.mpr hspos, hLe⟩, ?_⟩
  have hLadj : ∀ η, ContinuousLinearMap.adjoint L η = L η := by
    intro η
    apply ext_inner_right ℝ
    intro ζ
    rw [ContinuousLinearMap.adjoint_inner_left, hLsymm]
  ext1 ξ
  simp only [ContinuousLinearMap.comp_apply]
  rw [hLadj, hLL, hSapp, adjoint_inverse_adjoint_apply hM, hM.self_apply_inverse]

/-- Sign of a function vanishing on `{t = 0}` with negative vertical derivative. -/
theorem sign_of_vertical (φ : Space n → ℝ) (hφ : ContDiff ℝ 1 φ) (r : ℝ)
    (h0 : ∀ X ∈ Metric.ball (0 : Space n) r, vcoord X = 0 → φ X = 0)
    (hd : ∀ X ∈ Metric.ball (0 : Space n) r, fderiv ℝ φ X (ed n) < 0) :
    ∀ X ∈ Metric.ball (0 : Space n) r, (0 < vcoord X → φ X < 0) ∧ (vcoord X < 0 → 0 < φ X) := by
  intro X hX
  obtain ⟨⟨y, t⟩, rfl⟩ : ∃ p : EuclideanSpace ℝ (Fin n) × ℝ, lift p.1 p.2 = X :=
    ⟨(F1.liftEquiv n).symm X, by rw [← F1.liftEquiv_apply]; simp⟩
  simp only [vcoord_lift]
  have hXn : ‖lift y t‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hX
  have hseg : ∀ s : ℝ, |s| ≤ |t| → lift y s ∈ Metric.ball (0 : Space n) r := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖lift y s‖ ^ 2 ≤ ‖lift y t‖ ^ 2 := by
      rw [norm_lift_sq, norm_lift_sq]
      have : s ^ 2 ≤ t ^ 2 := sq_le_sq.mpr hs
      linarith
    have h2 : ‖lift y s‖ ≤ ‖lift y t‖ :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp h1
    linarith
  have hψ : ∀ s : ℝ, HasDerivAt (fun s => φ (lift y s)) (fderiv ℝ φ (lift y s) (ed n)) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => lift y s) (ed n) s := by
      have hfun : (fun s : ℝ => lift y s) = fun s => F1.horiz n y + s • ed n :=
        funext fun s => F1.lift_eq y s
      rw [hfun]
      simpa using ((hasDerivAt_id s).smul_const (ed n)).const_add (F1.horiz n y)
    exact ((hφ.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt s hl
  have hψc : Continuous (fun s => φ (lift y s)) :=
    continuous_iff_continuousAt.mpr fun s => (hψ s).continuousAt
  have hψ0 : φ (lift y 0) = 0 := h0 _ (hseg 0 (by simp)) (vcoord_lift y 0)
  constructor
  · intro ht
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun s => φ (lift y s))
      (fun s => fderiv ℝ φ (lift y s) (ed n)) ht hψc.continuousOn (fun s _ => hψ s)
    have hneg := hd _ (hseg c (by rw [abs_of_pos hc.1, abs_of_pos ht]; exact hc.2.le))
    have heq : φ (lift y t) = t * fderiv ℝ φ (lift y c) (ed n) := by
      rw [hcd, hψ0]
      field_simp
      ring
    rw [heq]
    exact mul_neg_of_pos_of_neg ht hneg
  · intro ht
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun s => φ (lift y s))
      (fun s => fderiv ℝ φ (lift y s) (ed n)) ht hψc.continuousOn (fun s _ => hψ s)
    have hneg := hd _ (hseg c (by
      rw [abs_of_neg hc.2, abs_of_neg ht]; linarith [hc.1]))
    have heq : φ (lift y t) = t * fderiv ℝ φ (lift y c) (ed n) := by
      have htne : (0 : ℝ) - t ≠ 0 := by linarith
      rw [hψ0] at hcd
      field_simp at hcd
      linarith
    rw [heq]
    exact mul_pos_of_neg_of_neg ht hneg

/-- Inverse function theorem package at `0`. -/
theorem local_diffeo (F : Space n → Space n) (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hinv : (fderiv ℝ F 0).IsInvertible) :
    ∃ R > 0, ∃ κ ≥ 1, Set.InjOn F (Metric.ball 0 R) ∧
      (∀ X ∈ Metric.ball (0 : Space n) R, ‖F X‖ ≤ κ * ‖X‖ ∧ ‖X‖ ≤ κ * ‖F X‖) ∧
      (∃ ε > 0, Metric.ball 0 ε ⊆ F '' Metric.ball 0 R) := by
  obtain ⟨e, he⟩ := hinv
  have hstrict : HasStrictFDerivAt F (e : Space n →L[ℝ] Space n) 0 := by
    rw [he]
    exact hF.contDiffAt.hasStrictFDerivAt ((hF.differentiable (by simp)) 0).hasFDerivAt (by simp)
  obtain ⟨s, hs0, hso, hA⟩ := hstrict.approximates_deriv_on_open_nhds
  obtain ⟨R, hR, hRs⟩ := Metric.isOpen_iff.mp hso 0 hs0
  have hA' : ApproximatesLinearOn F (e : Space n →L[ℝ] Space n) (Metric.ball 0 R)
      (‖(e.symm : Space n →L[ℝ] Space n)‖₊⁻¹ / 2) := hA.mono_set hRs
  have hc : Subsingleton (Space n) ∨
      ‖(e.symm : Space n →L[ℝ] Space n)‖₊⁻¹ / 2 < ‖(e.symm : Space n →L[ℝ] Space n)‖₊⁻¹ := by
    rcases e.subsingleton_or_nnNorm_symm_pos with h | h
    · exact Or.inl h
    · right; exact NNReal.half_lt_self (inv_pos.mpr h).ne'
  have hanti := hA'.antilipschitzWith hc
  -- cover
  have hmap := hstrict.map_nhds_eq_of_equiv
  have hball_nhds : Metric.ball (0 : Space n) R ∈ 𝓝 (0 : Space n) := Metric.ball_mem_nhds 0 hR
  have himg : F '' Metric.ball 0 R ∈ 𝓝 (0 : Space n) := by
    have := Filter.image_mem_map (m := F) hball_nhds
    rw [hmap, hF0] at this
    exact this
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp himg
  set c : ℝ := ((‖(e.symm : Space n →L[ℝ] Space n)‖₊⁻¹ / 2 : NNReal) : ℝ) with hcdef
  set K : ℝ := (((‖(e.symm : Space n →L[ℝ] Space n)‖₊⁻¹ -
    ‖(e.symm : Space n →L[ℝ] Space n)‖₊⁻¹ / 2)⁻¹ : NNReal) : ℝ) with hKdef
  refine ⟨R, hR, max (max (‖(e : Space n →L[ℝ] Space n)‖ + c) K) 1, le_max_right _ _,
    hA'.injOn hc, fun X hX => ⟨?_, ?_⟩, ε, hε, hεsub⟩
  · have h1 := hA' X hX 0 (Metric.mem_ball_self hR)
    rw [hF0, sub_zero, sub_zero] at h1
    have h2 : ‖(e : Space n →L[ℝ] Space n) X‖ ≤ ‖(e : Space n →L[ℝ] Space n)‖ * ‖X‖ :=
      (e : Space n →L[ℝ] Space n).le_opNorm X
    have hc0 : 0 ≤ c := NNReal.coe_nonneg _
    calc ‖F X‖ = ‖(F X - (e : Space n →L[ℝ] Space n) X) + (e : Space n →L[ℝ] Space n) X‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖F X - (e : Space n →L[ℝ] Space n) X‖ + ‖(e : Space n →L[ℝ] Space n) X‖ :=
          norm_add_le _ _
      _ ≤ c * ‖X‖ + ‖(e : Space n →L[ℝ] Space n)‖ * ‖X‖ := add_le_add h1 h2
      _ = (‖(e : Space n →L[ℝ] Space n)‖ + c) * ‖X‖ := by ring
      _ ≤ max (max (‖(e : Space n →L[ℝ] Space n)‖ + c) K) 1 * ‖X‖ := by
          gcongr; exact le_max_of_le_left (le_max_left _ _)
  · have h2 := hanti.le_mul_dist ⟨X, hX⟩ ⟨0, Metric.mem_ball_self hR⟩
    rw [Subtype.dist_eq, Set.domRestrict_apply, Set.domRestrict_apply, dist_zero_right, hF0,
      dist_zero_right] at h2
    calc ‖X‖ ≤ K * ‖F X‖ := h2
      _ ≤ max (max (‖(e : Space n →L[ℝ] Space n)‖ + c) K) 1 * ‖F X‖ := by
          gcongr; exact le_max_of_le_left (le_max_right _ _)

/-- **Existence of the collar map** (Lemma `lem:coords`, geometric part). -/
theorem exists_collarMap (hn : 0 < n) (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ)
    (hΓ0 : Γ 0 = 0) (ρ : ℝ) (hρ : 0 < ρ)
    (a : Space n → Space n →L[ℝ] Space n) (ha : ContDiff ℝ ∞ a)
    (ha_symm : ∀ x ξ η, ⟪a x ξ, η⟫_ℝ = ⟪ξ, a x η⟫_ℝ)
    (ha_ell : ∃ lam > 0, ∀ x ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x ξ, ξ⟫_ℝ) :
    ∃ (F : Space n → Space n) (R₀ κ₀ : ℝ), CollarMap Γ ρ a F R₀ κ₀ := by
  obtain ⟨F₀, hF₀s, hF₀0, hF₀flat, r, hr, M, hF₀inv, hF₀tr, hF₀nor, hF₀con⟩ :=
    exists_collar0 Γ hΓ hΓ0 a ha ha_symm ha_ell
  obtain ⟨lam, hlam, hell⟩ := ha_ell
  have h0ball : (0 : Space n) ∈ Metric.ball (0 : Space n) r := Metric.mem_ball_self hr
  have hv0 : vcoord (0 : Space n) = 0 := by simp [vcoord]
  -- the linear normalization
  have hM : (fderiv ℝ F₀ 0).IsInvertible := hF₀inv 0 h0ball
  have hblock : ∃ s : ℝ, (fderiv ℝ F₀ 0).inverse
      (a 0 (ContinuousLinearMap.adjoint (fderiv ℝ F₀ 0).inverse (ed n))) = s • ed n := by
    obtain ⟨μ, -, hμ⟩ := hF₀nor 0 h0ball hv0
    obtain ⟨s, hs⟩ := hF₀con 0 h0ball hv0
    have h := tildeA_conormal Γ F₀ a hM hμ hs
    simp only [tildeA, ContinuousLinearMap.comp_apply, hF₀0] at h
    exact ⟨μ * s, h⟩
  have ha₀pos : ∀ ξ : Space n, ξ ≠ 0 → 0 < ⟪a 0 ξ, ξ⟫_ℝ := by
    intro ξ hξ
    have h1 := hell 0 ξ
    have h2 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have h3 : 0 < lam * ‖ξ‖ ^ 2 := by positivity
    linarith
  obtain ⟨L, hLinv, hLsymm, ⟨ℓ, hℓ, hLe⟩, hLa⟩ :=
    exists_normalization (fderiv ℝ F₀ 0) hM (a 0) (ha_symm 0) ha₀pos hblock
  have hvin : ∀ Y : Space n, vcoord Y = ⟪Y, ed n⟫_ℝ := fun Y => (F1.inner_ed Y).symm
  have hvL : ∀ X, vcoord (L X) = ℓ * vcoord X := by
    intro X
    rw [hvin, hvin, hLsymm, hLe, real_inner_smul_right]
  -- the collar map
  set F : Space n → Space n := fun X => F₀ (L X) with hFdef
  have hFs : ContDiff ℝ ∞ F := hF₀s.comp L.contDiff
  have hF0 : F 0 = 0 := by simp [hFdef, hF₀0]
  have hDF : ∀ X, fderiv ℝ F X = fderiv ℝ F₀ (L X) ∘L L := by
    intro X
    have h1 : DifferentiableAt ℝ F₀ (L X) := hF₀s.differentiable (by simp) _
    exact (h1.hasFDerivAt.comp X L.hasFDerivAt).fderiv
  have hDF0 : (fderiv ℝ F 0).IsInvertible := by
    rw [hDF, map_zero]
    exact hM.comp hLinv
  obtain ⟨R₁, hR₁, κ₁, hκ₁, hinj, hlip, ε, hε, hcov⟩ := local_diffeo F hFs hF0 hDF0
  -- the radius
  set R₀ : ℝ := min (min R₁ (r / (‖L‖ + 1))) (ρ / κ₁) with hR₀def
  have hκ₁pos : 0 < κ₁ := lt_of_lt_of_le one_pos hκ₁
  have hR₀pos : 0 < R₀ := lt_min (lt_min hR₁ (by positivity)) (by positivity)
  have hR₀R₁ : R₀ ≤ R₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hR₀r : R₀ ≤ r / (‖L‖ + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hR₀ρ : R₀ ≤ ρ / κ₁ := min_le_right _ _
  have hball₁ : Metric.ball (0 : Space n) R₀ ⊆ Metric.ball 0 R₁ := Metric.ball_subset_ball hR₀R₁
  have hLball : ∀ X ∈ Metric.ball (0 : Space n) R₀, L X ∈ Metric.ball (0 : Space n) r := by
    intro X hX
    rw [Metric.mem_ball, dist_zero_right] at hX ⊢
    have h1 : ‖L X‖ ≤ ‖L‖ * ‖X‖ := L.le_opNorm X
    have h2 : (‖L‖ + 1) * ‖X‖ < r := by
      have h3 : ‖X‖ < r / (‖L‖ + 1) := hX.trans_le hR₀r
      rw [lt_div_iff₀ (by positivity)] at h3
      linarith
    nlinarith [norm_nonneg X, norm_nonneg L]
  have hnormρ : ∀ X ∈ Metric.ball (0 : Space n) R₀, ‖F X‖ < ρ := by
    intro X hX
    have h1 := (hlip X (hball₁ hX)).1
    rw [Metric.mem_ball, dist_zero_right] at hX
    have h2 : κ₁ * ‖X‖ < κ₁ * (ρ / κ₁) := by gcongr; exact hX.trans_le hR₀ρ
    rw [mul_div_cancel₀ _ hκ₁pos.ne'] at h2
    linarith
  -- sign of `graphFn Γ ∘ F`
  have hsign := sign_of_vertical (fun X => graphFn Γ (F X))
    (((contDiff_graphFn hΓ).comp hFs).of_le (by simp)) R₀
    (fun X _ hX => hF₀flat (L X) (by rw [hvL, hX, mul_zero]))
    (fun X hX => by
      have hd : fderiv ℝ (fun X => graphFn Γ (F X)) X (ed n) =
          ℓ * fderiv ℝ (fun Y => graphFn Γ (F₀ Y)) (L X) (ed n) := by
        have h1 : DifferentiableAt ℝ (fun Y => graphFn Γ (F₀ Y)) (L X) :=
          ((contDiff_graphFn hΓ).comp (hF₀s.of_le (by simp))).differentiable (by simp) _
        have h2 := (h1.hasFDerivAt.comp X L.hasFDerivAt).fderiv
        have h3 : (fun X => graphFn Γ (F X)) = (fun Y => graphFn Γ (F₀ Y)) ∘ L := rfl
        rw [h3, h2, ContinuousLinearMap.comp_apply, hLe, map_smul, smul_eq_mul]
      rw [hd]
      exact mul_neg_of_pos_of_neg hℓ (hF₀tr (L X) (hLball X hX)))
  -- bound on the Jacobian
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : Space n) R₀).exists_bound_of_continuousOn
    ((ContinuousLinearMap.continuous_det.comp (hFs.continuous_fderiv (by simp))).continuousOn)
  refine ⟨F, R₀, max (max κ₁ (max D 1)) (M / ℓ), ?_⟩
  have hκD : D ≤ max (max κ₁ (max D 1)) (M / ℓ) :=
    le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have hκκ₁ : κ₁ ≤ max (max κ₁ (max D 1)) (M / ℓ) := le_max_of_le_left (le_max_left _ _)
  have hκM : M / ℓ ≤ max (max κ₁ (max D 1)) (M / ℓ) := le_max_right _ _
  have hκ1 : 1 ≤ max (max κ₁ (max D 1)) (M / ℓ) :=
    le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  refine
    { smooth := hFs
      R₀_pos := hR₀pos
      one_le_κ₀ := hκ1
      pos := ?_
      flat := ?_
      nonpos := ?_
      lip := ?_
      antilip := ?_
      cover := ?_
      injOn := hinj.mono hball₁
      invertible := ?_
      det_le := ?_
      normal := ?_
      conormal := ?_
      at_zero := ?_ }
  · intro X hX ht
    exact ⟨hnormρ X hX, (hsign X hX).1 ht⟩
  · intro X hX ht
    exact ⟨hnormρ X hX, hF₀flat (L X) (by rw [hvL, ht, mul_zero])⟩
  · intro X hX ht hdom
    rcases ht.lt_or_eq with h | h
    · exact absurd hdom.2 (not_lt.mpr ((hsign X hX).2 h).le)
    · have : graphFn Γ (F X) = 0 := hF₀flat (L X) (by rw [hvL, h, mul_zero])
      exact absurd hdom.2 (by rw [this]; exact lt_irrefl 0)
  · intro X hX
    exact (hlip X (hball₁ hX)).1.trans (by gcongr)
  · intro X hX
    exact (hlip X (hball₁ hX)).2.trans (by gcongr)
  · refine ⟨min ε (R₀ / κ₁), lt_min hε (by positivity), fun x hx => ?_⟩
    rw [Metric.mem_ball, dist_zero_right] at hx
    obtain ⟨X, hX, rfl⟩ := hcov (by
      rw [Metric.mem_ball, dist_zero_right]; exact hx.trans_le (min_le_left _ _))
    refine ⟨X, ?_, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖X‖ ≤ κ₁ * ‖F X‖ := (hlip X hX).2
      _ < κ₁ * (R₀ / κ₁) := by gcongr; exact hx.trans_le (min_le_right _ _)
      _ = R₀ := by field_simp
  · intro X hX
    rw [hDF]
    exact (hF₀inv (L X) (hLball X hX)).comp hLinv
  · intro X hX
    have := hD X (Metric.ball_subset_closedBall hX)
    rw [Real.norm_eq_abs] at this
    exact this.trans hκD
  · intro X hX ht
    obtain ⟨μ, hμle, hμ⟩ := hF₀nor (L X) (hLball X hX) (by rw [hvL, ht, mul_zero])
    refine ⟨ℓ⁻¹ * μ, ?_, fun w => ?_⟩
    · rw [abs_mul, abs_inv, abs_of_pos hℓ]
      calc ℓ⁻¹ * |μ| ≤ ℓ⁻¹ * M := by gcongr
        _ = M / ℓ := by rw [inv_mul_eq_div]
        _ ≤ _ := hκM
    · have hinvL : ∀ v, ⟪L.inverse v, ed n⟫_ℝ = ℓ⁻¹ * ⟪v, ed n⟫_ℝ := by
        intro v
        have he : ed n = ℓ⁻¹ • L (ed n) := by
          rw [hLe, smul_smul, inv_mul_cancel₀ hℓ.ne', one_smul]
        conv_lhs => rw [he]
        rw [inner_smul_right, ← hLsymm, hLinv.self_apply_inverse]
      rw [hDF, (hF₀inv (L X) (hLball X hX)).inverse_comp_apply_of_left, hinvL, hμ, mul_assoc]
  · intro X hX ht
    obtain ⟨s, hs⟩ := hF₀con (L X) (hLball X hX) (by rw [hvL, ht, mul_zero])
    refine ⟨ℓ⁻¹ * s, ?_⟩
    show a (F₀ (L X)) (outerNormal Γ (F₀ (L X))) = _
    rw [hs, hDF, ContinuousLinearMap.comp_apply, hLe, map_smul, smul_smul]
    congr 1
    field_simp
  · rw [hDF, map_zero, ContinuousLinearMap.adjoint_comp, ← hLa]
    rfl

/-! ### Part 2: the transformed equation

Write `v = u ∘ F`, `P X = DF(X)⁻¹`, `Q X = P Xᵀ` (so `∇u(F X) = Q X ∇v(X)`) and `Ã = tildeA F a`.
For a `C¹` field `A` and a `C²` function `w`,
`div (A ∇w) = tr (h ↦ DA h ∇w) + tr (A ∘ D∇w)` (`T1`). By the chain rule
`∇v = DFᵀ (∇u ∘ F)` near `X`, hence `D∇v h = D(DFᵀ) h (∇u ∘ F) + DFᵀ D∇u(F X) DF h` (`T2`), and
`tr (Ã DFᵀ D∇u DF) = tr (DF Ã DFᵀ D∇u) = tr (a D∇u)` by cyclicity of the trace (`T3`). Using the
equation for `u` at `F X` this gives `div (Ã ∇v) = firstOrderFun X (∇v) - (c ∘ F) v`
(`divergence_tildeA_eq`), where `firstOrderFun X` is the linear functional below; `tildeB` is its
Riesz representative (with a minus sign).
-/

/-- `Q X = (DF(X)⁻¹)ᵀ`, so that `∇u(F X) = Q X (∇(u ∘ F) X)`. -/
noncomputable def invAdj (F : Space n → Space n) (X : Space n) : Space n →L[ℝ] Space n :=
  ContinuousLinearMap.adjoint (fderiv ℝ F X).inverse

/-- The trace of `h ↦ T h w` for a bilinear `T`. -/
noncomputable def traceFlip (T : Space n →L[ℝ] Space n →L[ℝ] Space n) (w : Space n) : ℝ :=
  LinearMap.trace ℝ (Space n) ((T.flip w : Space n →L[ℝ] Space n) : Space n →ₗ[ℝ] Space n)

/-- The linear functional collecting the first order terms of the transformed equation. -/
noncomputable def firstOrderFun (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (b : Space n → Space n) (X w : Space n) : ℝ :=
  traceFlip (fderiv ℝ (tildeA F a) X) w
    + LinearMap.trace ℝ (Space n) ((tildeA F a X ∘L
        (fderiv ℝ (fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y)) X).flip (invAdj F X w) :
        Space n →L[ℝ] Space n) : Space n →ₗ[ℝ] Space n)
    - traceFlip (fderiv ℝ a (F X)) (invAdj F X w)
    - ⟪b (F X), invAdj F X w⟫_ℝ

/-- The transformed first order coefficient: minus the Riesz representative of
`firstOrderFun F a b X`. -/
noncomputable def tildeB (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (b : Space n → Space n) (X : Space n) : Space n :=
  -∑ j : Fin (n + 1), firstOrderFun F a b X (EuclideanSpace.single j 1) • EuclideanSpace.single j 1

theorem trace_eq_sum_basis (T : Space n →L[ℝ] Space n) :
    LinearMap.trace ℝ (Space n) (T : Space n →ₗ[ℝ] Space n) =
      ∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i,
        T (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)⟫_ℝ := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
  rfl

theorem firstOrderFun_add (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (b : Space n → Space n) (X w₁ w₂ : Space n) :
    firstOrderFun F a b X (w₁ + w₂) = firstOrderFun F a b X w₁ + firstOrderFun F a b X w₂ := by
  simp only [firstOrderFun, traceFlip, trace_eq_sum_basis, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, map_add, ContinuousLinearMap.add_apply, inner_add_right,
    Finset.sum_add_distrib]
  ring

theorem firstOrderFun_smul (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (b : Space n → Space n) (X : Space n) (r : ℝ) (w : Space n) :
    firstOrderFun F a b X (r • w) = r * firstOrderFun F a b X w := by
  simp only [firstOrderFun, traceFlip, trace_eq_sum_basis, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, map_smul, ContinuousLinearMap.smul_apply,
    real_inner_smul_right, ← Finset.mul_sum]
  ring

theorem sum_single_inner (f : Space n →ₗ[ℝ] ℝ) (w : Space n) :
    ∑ j : Fin (n + 1), f (EuclideanSpace.single j 1) * ⟪EuclideanSpace.single j 1, w⟫_ℝ =
      f w := by
  have h := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr' w
  conv_rhs => rw [← h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, EuclideanSpace.basisFun_apply]

theorem inner_tildeB (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    (b : Space n → Space n) (X w : Space n) :
    ⟪tildeB F a b X, w⟫_ℝ = -firstOrderFun F a b X w := by
  let f : Space n →ₗ[ℝ] ℝ :=
    { toFun := firstOrderFun F a b X
      map_add' := firstOrderFun_add F a b X
      map_smul' := fun r w => by rw [firstOrderFun_smul]; rfl }
  have hlin := sum_single_inner f w
  rw [tildeB, inner_neg_left, sum_inner]
  simp only [real_inner_smul_left]
  exact congrArg Neg.neg hlin

theorem continuousOn_tildeB (F : Space n → Space n) (hF : ContDiff ℝ ∞ F)
    (a : Space n → Space n →L[ℝ] Space n) (ha : ContDiff ℝ ∞ a)
    (b : Space n → Space n) (hb : Continuous b) (R₀ : ℝ)
    (hinv : ∀ X ∈ Metric.ball (0 : Space n) R₀, (fderiv ℝ F X).IsInvertible) :
    ContinuousOn (tildeB F a b) (Metric.ball 0 R₀) := by
  have hU : IsOpen (Metric.ball (0 : Space n) R₀) := Metric.isOpen_ball
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hÃ : ContDiffOn ℝ 2 (tildeA F a) (Metric.ball 0 R₀) :=
    contDiffOn_tildeA F hF a ha _ hU hinv
  have hÃc : ContinuousOn (tildeA F a) (Metric.ball 0 R₀) := hÃ.continuousOn
  have hDÃc : ContinuousOn (fun X => fderiv ℝ (tildeA F a) X) (Metric.ball 0 R₀) :=
    hÃ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD'c : Continuous
      (fun X => fderiv ℝ (fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y)) X) :=
    ((adjointCLE (n := n)).contDiff.comp hDF).continuous_fderiv (by simp)
  have hQc : ContinuousOn (invAdj F) (Metric.ball 0 R₀) := by
    intro X hX
    obtain ⟨e, he⟩ := hinv X hX
    have h1 : ContinuousAt ContinuousLinearMap.inverse (fderiv ℝ F X) := by
      rw [← he]; exact (contDiffAt_map_inverse (n := 1) e).continuousAt
    exact ((adjointCLE (n := n)).continuous.continuousAt.comp
      (h1.comp hDF.continuous.continuousAt)).continuousWithinAt
  have hDac : Continuous (fun X => fderiv ℝ a (F X)) :=
    (ha.continuous_fderiv (by simp)).comp hF.continuous
  have hbc : Continuous (fun X => b (F X)) := hb.comp hF.continuous
  have hfo : ∀ w, ContinuousOn (fun X => firstOrderFun F a b X w) (Metric.ball 0 R₀) := by
    intro w
    have heq : (fun X => firstOrderFun F a b X w) = fun X =>
        (∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i,
          fderiv ℝ (tildeA F a) X (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i) w⟫_ℝ) +
        (∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i, tildeA F a X
          (fderiv ℝ (fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y)) X
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i) (invAdj F X w))⟫_ℝ) -
        (∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i,
          fderiv ℝ a (F X) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i) (invAdj F X w)⟫_ℝ) -
        ⟪b (F X), invAdj F X w⟫_ℝ := by
      funext X
      simp only [firstOrderFun, traceFlip, trace_eq_sum_basis, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.comp_apply]
    rw [heq]
    refine (((continuousOn_finsetSum _ fun i _ => ?_).add
      (continuousOn_finsetSum _ fun i _ => ?_)).sub (continuousOn_finsetSum _ fun i _ => ?_)).sub
        ?_
    · exact continuousOn_const.inner
        ((hDÃc.clm_apply continuousOn_const).clm_apply continuousOn_const)
    · exact continuousOn_const.inner (hÃc.clm_apply
        ((hD'c.continuousOn.clm_apply continuousOn_const).clm_apply
          (hQc.clm_apply continuousOn_const)))
    · exact continuousOn_const.inner ((hDac.continuousOn.clm_apply continuousOn_const).clm_apply
        (hQc.clm_apply continuousOn_const))
    · exact hbc.continuousOn.inner (hQc.clm_apply continuousOn_const)
  have hB : tildeB F a b = fun X => -∑ j : Fin (n + 1),
      firstOrderFun F a b X (EuclideanSpace.single j 1) • EuclideanSpace.single j 1 := rfl
  rw [hB]
  exact (continuousOn_finsetSum _ fun j _ => (hfo _).smul continuousOn_const).neg

/-- `T1`: `div (A V) = tr (h ↦ DA h V) + tr (A ∘ DV)`. -/
theorem divergence_clm_apply {A : Space n → Space n →L[ℝ] Space n} {V : Space n → Space n}
    {x : Space n} (hA : DifferentiableAt ℝ A x) (hV : DifferentiableAt ℝ V x) :
    divergence (fun y => A y (V y)) x = traceFlip (fderiv ℝ A x) (V x) +
      LinearMap.trace ℝ (Space n)
        ((A x ∘L fderiv ℝ V x : Space n →L[ℝ] Space n) : Space n →ₗ[ℝ] Space n) := by
  unfold divergence traceFlip
  rw [fderiv_clm_apply hA hV]
  simp only [trace_eq_sum_basis, ContinuousLinearMap.add_apply, inner_add_right,
    Finset.sum_add_distrib]
  ring

theorem trace_comp_add (T A B : Space n →L[ℝ] Space n) :
    LinearMap.trace ℝ (Space n) ((T ∘L (A + B) : Space n →L[ℝ] Space n) : Space n →ₗ[ℝ] Space n) =
      LinearMap.trace ℝ (Space n) ((T ∘L A : Space n →L[ℝ] Space n) : Space n →ₗ[ℝ] Space n) +
      LinearMap.trace ℝ (Space n) ((T ∘L B : Space n →L[ℝ] Space n) : Space n →ₗ[ℝ] Space n) := by
  simp only [trace_eq_sum_basis, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add, inner_add_right, Finset.sum_add_distrib]

/-- `T3`: `tr (Ã DFᵀ M DF) = tr (a M)`. -/
theorem trace_tildeA_comp (F : Space n → Space n) (a : Space n → Space n →L[ℝ] Space n)
    {X : Space n} (hX : (fderiv ℝ F X).IsInvertible) (M : Space n →L[ℝ] Space n) :
    LinearMap.trace ℝ (Space n) ((tildeA F a X ∘L (ContinuousLinearMap.adjoint (fderiv ℝ F X) ∘L
      (M ∘L fderiv ℝ F X)) : Space n →L[ℝ] Space n) : Space n →ₗ[ℝ] Space n) =
      LinearMap.trace ℝ (Space n) ((a (F X) ∘L M : Space n →L[ℝ] Space n) :
        Space n →ₗ[ℝ] Space n) := by
  have h1 : tildeA F a X ∘L (ContinuousLinearMap.adjoint (fderiv ℝ F X) ∘L
      (M ∘L fderiv ℝ F X)) = ((fderiv ℝ F X).inverse ∘L (a (F X) ∘L M)) ∘L fderiv ℝ F X := by
    ext1 v
    simp only [tildeA, ContinuousLinearMap.comp_apply, adjoint_inverse_adjoint_apply hX]
  rw [h1, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
    ← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.comp_assoc,
    hX.self_comp_inverse, ContinuousLinearMap.id_comp]

/-- `T2`: the derivative of `∇(u ∘ F)`. -/
theorem fderiv_gradient_comp {u : Space n → ℝ} {F : Space n → Space n} {D U : Set (Space n)}
    (hD : IsOpen D) (hu : ContDiffOn ℝ 2 u D) (hF : ContDiff ℝ ∞ F) (hU : IsOpen U)
    (hFU : ∀ Y ∈ U, F Y ∈ D) {X : Space n} (hX : X ∈ U) :
    fderiv ℝ (gradient (fun Z => u (F Z))) X =
      ContinuousLinearMap.adjoint (fderiv ℝ F X) ∘L
          (fderiv ℝ (gradient u) (F X) ∘L fderiv ℝ F X) +
        (fderiv ℝ (fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y)) X).flip
          (gradient u (F X)) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
  have hgu : ContDiffOn ℝ 1 (gradient u) D :=
    (toDualSymmCLE (n := n)).contDiff.comp_contDiffOn (hu.fderiv_of_isOpen hD (by norm_num))
  have hev : gradient (fun Z => u (F Z)) =ᶠ[𝓝 X]
      fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y) (gradient u (F Y)) := by
    filter_upwards [hU.mem_nhds hX] with Y hY
    exact gradient_comp ((hu.differentiableOn (by norm_num)).differentiableAt
      (hD.mem_nhds (hFU Y hY))) (hF1.differentiable (by norm_num) Y)
  rw [hev.fderiv_eq]
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hadj : DifferentiableAt ℝ (fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y)) X :=
    ((adjointCLE (n := n)).contDiff.comp hDF).differentiable (by simp) X
  have hgd : HasFDerivAt (gradient u) (fderiv ℝ (gradient u) (F X)) (F X) :=
    ((hgu.differentiableOn (by norm_num)).differentiableAt (hD.mem_nhds (hFU X hX))).hasFDerivAt
  have hgF : HasFDerivAt (fun Y => gradient u (F Y))
      (fderiv ℝ (gradient u) (F X) ∘L fderiv ℝ F X) X :=
    hgd.comp X (hF1.differentiable (by norm_num) X).hasFDerivAt
  rw [fderiv_clm_apply hadj hgF.differentiableAt, hgF.fderiv]

/-- The pointwise transformation rule for the principal part (steps `T1`–`T3`). -/
theorem divergence_tildeA_eq (Γ : (Fin n → ℝ) → ℝ) (hΓ : Continuous Γ) (ρ : ℝ)
    (a : Space n → Space n →L[ℝ] Space n) (ha : ContDiff ℝ ∞ a)
    (b : Space n → Space n) (c : Space n → ℝ)
    (u : Space n → ℝ) (hu : ContDiffOn ℝ 2 u (domain Γ ρ))
    (hL : ∀ x ∈ domain Γ ρ,
      divergence (fun y => a y (gradient u y)) x + ⟪b x, gradient u x⟫_ℝ + c x * u x = 0)
    (F : Space n → Space n) (hF : ContDiff ℝ ∞ F) (R₀ : ℝ)
    (hinv : ∀ X ∈ Metric.ball (0 : Space n) R₀, (fderiv ℝ F X).IsInvertible)
    (hpos : ∀ X ∈ halfBall n R₀, F X ∈ domain Γ ρ) (X : Space n) (hX : X ∈ halfBall n R₀) :
    divergence (fun Y => tildeA F a Y (gradient (fun Z => u (F Z)) Y)) X =
      firstOrderFun F a b X (gradient (fun Z => u (F Z)) X) - c (F X) * u (F X) := by
  have hdom : IsOpen (domain Γ ρ) := isOpen_domain hΓ ρ
  have hXball : X ∈ Metric.ball (0 : Space n) R₀ := halfBall_subset_ball R₀ hX
  have hXinv := hinv X hXball
  have hFX : F X ∈ domain Γ ρ := hpos X hX
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
  have hÃd : DifferentiableAt ℝ (tildeA F a) X :=
    ((contDiffOn_tildeA F hF a ha _ Metric.isOpen_ball hinv).differentiableOn
      (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hXball)
  have hT2 := fderiv_gradient_comp hdom hu hF (isOpen_halfBall R₀) hpos hX
  have hgu : ContDiffOn ℝ 1 (gradient u) (domain Γ ρ) :=
    (toDualSymmCLE (n := n)).contDiff.comp_contDiffOn (hu.fderiv_of_isOpen hdom (by norm_num))
  have hev : gradient (fun Z => u (F Z)) =ᶠ[𝓝 X]
      fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y) (gradient u (F Y)) := by
    filter_upwards [(isOpen_halfBall R₀).mem_nhds hX] with Y hY
    exact gradient_comp ((hu.differentiableOn (by norm_num)).differentiableAt
      (hdom.mem_nhds (hpos Y hY))) (hF1.differentiable (by norm_num) Y)
  have hgvd : DifferentiableAt ℝ (gradient (fun Z => u (F Z))) X := by
    have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
    have hadj : DifferentiableAt ℝ (fun Y => ContinuousLinearMap.adjoint (fderiv ℝ F Y)) X :=
      ((adjointCLE (n := n)).contDiff.comp hDF).differentiable (by simp) X
    have hgF : DifferentiableAt ℝ (fun Y => gradient u (F Y)) X :=
      ((hgu.differentiableOn (by norm_num)).differentiableAt (hdom.mem_nhds hFX)).comp X
        (hF1.differentiable (by norm_num) X)
    exact (hadj.clm_apply hgF).congr_of_eventuallyEq hev
  have hgvX : gradient (fun Z => u (F Z)) X =
      ContinuousLinearMap.adjoint (fderiv ℝ F X) (gradient u (F X)) := hev.eq_of_nhds
  have hQ : invAdj F X (gradient (fun Z => u (F Z)) X) = gradient u (F X) := by
    rw [hgvX, invAdj, adjoint_inverse_adjoint_apply hXinv]
  have hdiv_u := divergence_clm_apply (A := a) (V := gradient u) (x := F X)
    (ha.differentiable (by simp) _)
    ((hgu.differentiableOn (by norm_num)).differentiableAt (hdom.mem_nhds hFX))
  have hLX := hL (F X) hFX
  rw [hdiv_u] at hLX
  rw [divergence_clm_apply hÃd hgvd, hT2, trace_comp_add, trace_tildeA_comp F a hXinv]
  unfold firstOrderFun
  rw [hQ]
  linarith

/-- **The transformed equation.** If `F` is smooth with invertible derivative on `B(0, R₀)` and
maps the half-ball into the domain, then `u ∘ F` solves an equation in divergence form with
principal coefficient `tildeA F a`, a continuous first order coefficient and zeroth order
coefficient `c ∘ F`. -/
theorem transformed_equation (Γ : (Fin n → ℝ) → ℝ) (hΓ : Continuous Γ) (ρ : ℝ)
    (a : Space n → Space n →L[ℝ] Space n) (ha : ContDiff ℝ ∞ a)
    (b : Space n → Space n) (hb : Continuous b) (c : Space n → ℝ)
    (u : Space n → ℝ) (hu : ContDiffOn ℝ 2 u (domain Γ ρ))
    (hL : ∀ x ∈ domain Γ ρ,
      divergence (fun y => a y (gradient u y)) x + ⟪b x, gradient u x⟫_ℝ + c x * u x = 0)
    (F : Space n → Space n) (hF : ContDiff ℝ ∞ F) (R₀ : ℝ)
    (hinv : ∀ X ∈ Metric.ball (0 : Space n) R₀, (fderiv ℝ F X).IsInvertible)
    (hpos : ∀ X ∈ halfBall n R₀, F X ∈ domain Γ ρ) :
    ∃ B : Space n → Space n, ContinuousOn B (Metric.ball 0 R₀) ∧
      ∀ X ∈ halfBall n R₀, ellOp (tildeA F a) B (fun Y => c (F Y)) (fun Y => u (F Y)) X = 0 := by
  refine ⟨tildeB F a b, continuousOn_tildeB F hF a ha b hb R₀ hinv, fun X hX => ?_⟩
  unfold ellOp
  rw [divergence_tildeA_eq Γ hΓ ρ a ha b c u hu hL F hF R₀ hinv hpos X hX, inner_tildeB]
  ring

/-! ### Part 3: globalizing the coefficients -/

section Cutoff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

theorem contDiff_smul_of_tsupport {k : ℕ∞ω} {χ : E → ℝ} {h : E → G} {U : Set E}
    (hχ : ContDiff ℝ k χ) (hh : ContDiffOn ℝ k h U) (hU : IsOpen U) (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ k (fun x => χ x • h x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hh.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h' => hx (hsupp h')
    have h0 : (fun y => χ y • h y) =ᶠ[𝓝 x] fun _ => (0 : G) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem continuous_smul_of_tsupport {χ : E → ℝ} {h : E → G} {U : Set E}
    (hχ : Continuous χ) (hh : ContinuousOn h U) (hU : IsOpen U) (hsupp : tsupport χ ⊆ U) :
    Continuous (fun x => χ x • h x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.continuousAt.smul (hh.continuousAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h' => hx (hsupp h')
    have h0 : (fun y => χ y • h y) =ᶠ[𝓝 x] fun _ => (0 : G) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
      simp [hy]
    exact continuousAt_const.congr h0.symm

theorem iteratedFDeriv_two_const_add (c : G) (g : E → G) (hg : ContDiff ℝ 2 g) (x : E) :
    iteratedFDeriv ℝ 2 (fun y => c + g y) x = iteratedFDeriv ℝ 2 g x := by
  have h := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := 2) (f := fun _ => c) (g := g) (x := x)
    contDiffAt_const hg.contDiffAt
  rw [iteratedFDeriv_const_of_ne (by norm_num), Pi.zero_apply, zero_add] at h
  exact h

theorem fderiv_eq_zero_of_eventuallyEq_zero {g : E → G} {x : E} (h : g =ᶠ[𝓝 x] fun _ => 0) :
    fderiv ℝ g x = 0 := by
  rw [h.fderiv_eq]
  exact fderiv_const_apply _

theorem smul_eventuallyEq_zero {χ : E → ℝ} {g : E → G} {x : E} {U : Set E} (hU : IsOpen U)
    (hx : x ∈ U) (hχ : ∀ y ∈ U, χ y = 0) : (fun y => χ y • g y) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hU.mem_nhds hx] with y hy
  rw [hχ y hy, zero_smul]

end Cutoff

set_option maxHeartbeats 1000000 in
theorem globalize_aux (R₀ : ℝ) (hR₀ : 0 < R₀) (A₀ : Space n → Space n →L[ℝ] Space n)
    (hA₀ : ContDiffOn ℝ 2 A₀ (Metric.ball 0 R₀))
    (hsymm : ∀ x ∈ Metric.ball (0 : Space n) R₀, ∀ ξ η, ⟪A₀ x ξ, η⟫_ℝ = ⟪ξ, A₀ x η⟫_ℝ)
    (hell : ∀ r < R₀, ∃ lam > 0, ∀ x ∈ Metric.closedBall (0 : Space n) r, ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ x ξ, ξ⟫_ℝ)
    (B₀ : Space n → Space n) (hB₀ : ContinuousOn B₀ (Metric.ball 0 R₀))
    (C₀ : Space n → ℝ) (hC₀ : ContinuousOn C₀ (Metric.ball 0 R₀))
    (χ : Space n → ℝ) (hχc : ContDiff ℝ ∞ χ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχin : ∀ x ∈ Metric.ball (0 : Space n) (R₀ / 2), χ x = 1)
    (hsuppU : tsupport χ ⊆ Metric.ball 0 R₀) (hχcs : HasCompactSupport χ)
    (hχout : ∀ x, x ∉ Metric.closedBall (0 : Space n) (3 * R₀ / 4) → χ x = 0) :
    ∃ (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n) (C : Space n → ℝ)
      (lam K : ℝ), GoodCoeffs A B C lam K ∧
      ∀ x ∈ Metric.ball (0 : Space n) (R₀ / 2), A x = A₀ x ∧ B x = B₀ x ∧ C x = C₀ x := by
  -- the coefficients
  obtain ⟨G, hGdef⟩ : ∃ G : Space n → (Space n →L[ℝ] Space n),
      G = fun x => χ x • (A₀ x - ContinuousLinearMap.id ℝ (Space n)) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Space n → (Space n →L[ℝ] Space n),
      A = fun x => ContinuousLinearMap.id ℝ (Space n) + G x := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Space n → Space n, B = fun x => χ x • B₀ x := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Space n → ℝ, C = fun x => χ x • C₀ x := ⟨_, rfl⟩
  have hGx : ∀ x, G x = χ x • (A₀ x - ContinuousLinearMap.id ℝ (Space n)) := fun x => by
    rw [hGdef]
  have hAx : ∀ x, A x = ContinuousLinearMap.id ℝ (Space n) + G x := fun x => by rw [hAdef]
  have hG : ContDiff ℝ 2 G := by
    rw [hGdef]
    exact contDiff_smul_of_tsupport (hχc.of_le (by simp)) (hA₀.sub contDiffOn_const)
      Metric.isOpen_ball hsuppU
  have hGcs : HasCompactSupport G := by
    rw [hGdef]
    exact hχcs.smul_right (f' := fun x => A₀ x - ContinuousLinearMap.id ℝ (Space n))
  have hA : ContDiff ℝ 2 A := by rw [hAdef]; exact contDiff_const.add hG
  have hBc : Continuous B := by
    rw [hBdef]; exact continuous_smul_of_tsupport hχc.continuous hB₀ Metric.isOpen_ball hsuppU
  have hCc : Continuous C := by
    rw [hCdef]; exact continuous_smul_of_tsupport hχc.continuous hC₀ Metric.isOpen_ball hsuppU
  have hBcs : HasCompactSupport B := by rw [hBdef]; exact hχcs.smul_right (f' := B₀)
  have hCcs : HasCompactSupport C := by rw [hCdef]; exact hχcs.smul_right (f' := C₀)
  -- bounds
  obtain ⟨KG, hKG⟩ := hGcs.exists_bound_of_continuous hG.continuous
  obtain ⟨KdG', hKdG'⟩ :=
    (isCompact_closedBall (0 : Space n) (3 * R₀ / 4)).exists_bound_of_continuousOn
      (hG.continuous_fderiv (by simp)).continuousOn
  have hdG0 : ∀ x, x ∉ Metric.closedBall (0 : Space n) (3 * R₀ / 4) → fderiv ℝ G x = 0 := by
    intro x hx
    rw [hGdef]
    exact fderiv_eq_zero_of_eventuallyEq_zero (smul_eventuallyEq_zero
      (g := fun y => A₀ y - ContinuousLinearMap.id ℝ (Space n))
      Metric.isClosed_closedBall.isOpen_compl hx (fun y hy => hχout y hy))
  obtain ⟨KdG, hKdG⟩ : ∃ KdG : ℝ, ∀ x, ‖fderiv ℝ G x‖ ≤ KdG := by
    refine ⟨max KdG' 0, fun x => ?_⟩
    by_cases hx : x ∈ Metric.closedBall (0 : Space n) (3 * R₀ / 4)
    · exact (hKdG' x hx).trans (le_max_left _ _)
    · rw [hdG0 x hx, ContinuousLinearMap.opNorm_zero]
      exact le_max_right _ _
  obtain ⟨Kd2G, hKd2G⟩ :=
    (hGcs.iteratedFDeriv (𝕜 := ℝ) 2).exists_bound_of_continuous
      (hG.continuous_iteratedFDeriv (by simp))
  obtain ⟨KB, hKB⟩ := hBcs.exists_bound_of_continuous hBc
  obtain ⟨KC, hKC⟩ := hCcs.exists_bound_of_continuous hCc
  obtain ⟨lam₀, hlam₀, hell₀⟩ := hell (3 * R₀ / 4) (by linarith)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max (max (1 + KG) KdG) (max Kd2G (max KB KC)) := ⟨_, rfl⟩
  have hK1 : 1 + KG ≤ K := by rw [hKdef]; exact le_max_of_le_left (le_max_left _ _)
  have hK2 : KdG ≤ K := by rw [hKdef]; exact le_max_of_le_left (le_max_right _ _)
  have hK3 : Kd2G ≤ K := by rw [hKdef]; exact le_max_of_le_right (le_max_left _ _)
  have hK4 : KB ≤ K := by
    rw [hKdef]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hK5 : KC ≤ K := by
    rw [hKdef]; exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  refine ⟨A, B, C, min lam₀ 1, K, ⟨lt_min hlam₀ one_pos, hA, ?_, ?_, ?_, ?_, ?_, hBc, hCc, ?_,
    ?_⟩, ?_⟩
  · intro x ξ η
    have hexp1 : ⟪A x ξ, η⟫_ℝ = ⟪ξ, η⟫_ℝ + χ x * (⟪A₀ x ξ, η⟫_ℝ - ⟪ξ, η⟫_ℝ) := by
      rw [hAx, hGx]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_add_left,
        real_inner_smul_left, inner_sub_left]
    have hexp2 : ⟪ξ, A x η⟫_ℝ = ⟪ξ, η⟫_ℝ + χ x * (⟪ξ, A₀ x η⟫_ℝ - ⟪ξ, η⟫_ℝ) := by
      rw [hAx, hGx]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_add_right,
        real_inner_smul_right, inner_sub_right]
    rw [hexp1, hexp2]
    by_cases hx : x ∈ Metric.ball (0 : Space n) R₀
    · rw [hsymm x hx ξ η]
    · have : χ x = 0 := hχout x (fun h => hx (Metric.closedBall_subset_ball (by linarith) h))
      rw [this, zero_mul, zero_mul]
  · intro x ξ
    have hexp : ⟪A x ξ, ξ⟫_ℝ = ‖ξ‖ ^ 2 + χ x * (⟪A₀ x ξ, ξ⟫_ℝ - ‖ξ‖ ^ 2) := by
      rw [hAx, hGx]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_add_left,
        real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]
    rw [hexp]
    have hm1 : min lam₀ 1 ≤ 1 := min_le_right _ _
    have hml : min lam₀ 1 ≤ lam₀ := min_le_left _ _
    have hξ2 : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    have ha1 : min lam₀ 1 * ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by nlinarith
    by_cases hx : x ∈ Metric.closedBall (0 : Space n) (3 * R₀ / 4)
    · have h1 := hell₀ x hx ξ
      have h0 := hχ0 x
      have h1' := hχ1 x
      have ha2 : min lam₀ 1 * ‖ξ‖ ^ 2 ≤ ⟪A₀ x ξ, ξ⟫_ℝ := by nlinarith
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr ha2),
        mul_nonneg (sub_nonneg.mpr h1') (sub_nonneg.mpr ha1)]
    · rw [hχout x hx, zero_mul, add_zero]
      exact ha1
  · intro x
    rw [hAx]
    calc ‖ContinuousLinearMap.id ℝ (Space n) + G x‖
        ≤ ‖ContinuousLinearMap.id ℝ (Space n)‖ + ‖G x‖ := norm_add_le _ _
      _ ≤ 1 + KG := add_le_add (ContinuousLinearMap.norm_id_le) (hKG x)
      _ ≤ K := hK1
  · intro x
    have : fderiv ℝ A x = fderiv ℝ G x := by rw [hAdef]; exact fderiv_const_add _
    rw [this]
    exact (hKdG x).trans hK2
  · intro x
    have : iteratedFDeriv ℝ 2 A x = iteratedFDeriv ℝ 2 G x := by
      rw [hAdef]
      exact iteratedFDeriv_two_const_add _ G hG x
    rw [this]
    exact (hKd2G x).trans hK3
  · intro x
    exact (hKB x).trans hK4
  · intro x
    rw [← Real.norm_eq_abs]
    exact (hKC x).trans hK5
  · intro x hx
    have h1 := hχin x hx
    refine ⟨?_, ?_, ?_⟩
    · rw [hAx, hGx, h1, one_smul, add_sub_cancel]
    · rw [hBdef]; simp only [h1, one_smul]
    · rw [hCdef]; simp only [h1, one_smul]

/-- **Cutoff.** Coefficients that are good on `B(0, R₀)` agree on `B(0, R₀/2)` with coefficients
satisfying `GoodCoeffs` on the whole space. -/
theorem globalize (R₀ : ℝ) (hR₀ : 0 < R₀) (A₀ : Space n → Space n →L[ℝ] Space n)
    (hA₀ : ContDiffOn ℝ 2 A₀ (Metric.ball 0 R₀))
    (hsymm : ∀ x ∈ Metric.ball (0 : Space n) R₀, ∀ ξ η, ⟪A₀ x ξ, η⟫_ℝ = ⟪ξ, A₀ x η⟫_ℝ)
    (hell : ∀ r < R₀, ∃ lam > 0, ∀ x ∈ Metric.closedBall (0 : Space n) r, ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ x ξ, ξ⟫_ℝ)
    (B₀ : Space n → Space n) (hB₀ : ContinuousOn B₀ (Metric.ball 0 R₀))
    (C₀ : Space n → ℝ) (hC₀ : ContinuousOn C₀ (Metric.ball 0 R₀)) :
    ∃ (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n) (C : Space n → ℝ)
      (lam K : ℝ), GoodCoeffs A B C lam K ∧
      ∀ x ∈ Metric.ball (0 : Space n) (R₀ / 2), A x = A₀ x ∧ B x = B₀ x ∧ C x = C₀ x := by
  classical
  -- the cutoff
  obtain ⟨χ, hχc, hχ0, hχ1, hχin, hsuppU, hχcs, hχout⟩ : ∃ χ : Space n → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧ (∀ x ∈ Metric.ball (0 : Space n) (R₀ / 2), χ x = 1) ∧
      tsupport χ ⊆ Metric.ball 0 R₀ ∧ HasCompactSupport χ ∧
      (∀ x, x ∉ Metric.closedBall (0 : Space n) (3 * R₀ / 4) → χ x = 0) := by
    let χb : ContDiffBump (0 : Space n) := ⟨R₀ / 2, 3 * R₀ / 4, by positivity, by linarith⟩
    have htsupp : tsupport χb = Metric.closedBall 0 (3 * R₀ / 4) := χb.tsupport_eq
    refine ⟨χb, χb.contDiff, fun x => χb.nonneg, fun x => χb.le_one, fun x hx =>
      χb.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), ?_, χb.hasCompactSupport, ?_⟩
    · rw [htsupp]; exact Metric.closedBall_subset_ball (by linarith)
    · intro x hx
      rw [← htsupp] at hx
      exact image_eq_zero_of_notMem_tsupport hx
  exact globalize_aux R₀ hR₀ A₀ hA₀ hsymm hell B₀ hB₀ C₀ hC₀ χ hχc hχ0 hχ1 hχin hsuppU hχcs
    hχout

/-! ### Part 4: comparison of `L²` norms -/

/-- **Change of variables.** -/
theorem l2_comparison (F : Space n → Space n) (hF : ContDiff ℝ 1 F) (R₀ κ₀ : ℝ)
    (hinj : Set.InjOn F (Metric.ball 0 R₀))
    (hdet : ∀ X ∈ Metric.ball (0 : Space n) R₀, |(fderiv ℝ F X).det| ≤ κ₀)
    (r : ℝ) (hr : r ≤ R₀) (g : Space n → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hgi : IntegrableOn (fun X => g (F X)) (halfBall n r))
    (S : Set (Space n)) (hS : S ⊆ F '' halfBall n r) :
    ∫ x in S, g x ≤ κ₀ * ∫ X in halfBall n r, g (F X) := by
  have hs : MeasurableSet (halfBall n r) := (isOpen_halfBall r).measurableSet
  have hsub : halfBall n r ⊆ Metric.ball 0 R₀ :=
    (halfBall_subset_ball r).trans (Metric.ball_subset_ball hr)
  have hf' : ∀ x ∈ halfBall n r, HasFDerivWithinAt F (fderiv ℝ F x) (halfBall n r) x :=
    fun x _ => ((hF.differentiable (by norm_num)) x).hasFDerivAt.hasFDerivWithinAt
  have hinj' : Set.InjOn F (halfBall n r) := hinj.mono hsub
  have hJcont : Continuous (fun x => |(fderiv ℝ F x).det|) :=
    (ContinuousLinearMap.continuous_det.comp (hF.continuous_fderiv (by norm_num))).abs
  have hJg : IntegrableOn (fun x => |(fderiv ℝ F x).det| • g (F x)) (halfBall n r) := by
    refine Integrable.mono' (hgi.const_mul κ₀) ?_ ?_
    · exact hJcont.aestronglyMeasurable.smul hgi.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hs] with x hx
      rw [norm_smul, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs, abs_of_nonneg (hg _)]
      exact mul_le_mul_of_nonneg_right (hdet x (hsub hx)) (hg _)
  have himg : IntegrableOn g (F '' halfBall n r) :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hf' hinj' g).mpr hJg
  calc ∫ x in S, g x ≤ ∫ x in F '' halfBall n r, g x :=
        setIntegral_mono_set himg (ae_of_all _ (fun x => hg x)) (Filter.Eventually.of_forall fun x hx => hS hx)
    _ = ∫ x in halfBall n r, |(fderiv ℝ F x).det| • g (F x) :=
        integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' hinj' g
    _ ≤ ∫ x in halfBall n r, κ₀ * g (F x) := by
        refine setIntegral_mono_on hJg (hgi.const_mul κ₀) hs (fun x hx => ?_)
        rw [smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hdet x (hsub hx)) (hg _)
    _ = κ₀ * ∫ x in halfBall n r, g (F x) := integral_const_mul κ₀ _

end PkgC

open PkgC in
/-- **Collar reduction.** The data of Theorem I yield a half-ball solution `S` and a map `F`
from the half-ball onto a neighbourhood of `0` in the domain, transporting `v` to `u`, the flat
piece to the boundary piece, and comparing conormal derivatives and `L²` norms. -/
theorem collar_reduction (hn : 0 < n) (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ) (hΓ0 : Γ 0 = 0)
    (ρ : ℝ) (hρ : 0 < ρ)
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
    :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ R₁ > 0, ∃ (S : HalfBallSolution n) (F : Space n → Space n), S.R ≤ R₁ ∧
      (∀ X ∈ halfBall n S.R, F X ∈ domain Γ ρ ∧ S.v X = u (F X)) ∧
      (∀ X ∈ flatPiece n S.R, F X ∈ boundaryPiece Γ ρ ∧ ‖F X‖ ≤ κ * ‖X‖ ∧ ‖X‖ ≤ κ * ‖F X‖ ∧
        |⟪S.A X (S.Dv X), ed n⟫_ℝ| ≤ κ * |⟪a (F X) (Du (F X)), outerNormal Γ (F X)⟫_ℝ|) ∧
      (∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → ∃ X ∈ halfBall n S.R, F X = x) ∧
      (∀ W : Set (Space n), IsOpen W → (W ∩ F '' halfBall n S.R).Nonempty →
        ∃ V : Set (Space n), IsOpen V ∧ V.Nonempty ∧ V ⊆ halfBall n S.R ∧ ∀ X ∈ V, F X ∈ W) ∧
      (∀ r ∈ Set.Ioc 0 S.R,
        ∫ x in domain Γ ρ ∩ Metric.ball 0 (r / κ), u x ^ 2 ≤ κ * ∫ X in halfBall n r, S.v X ^ 2) := by
  classical
  have hΓc : Continuous Γ := hΓ.continuous
  have hdom_open : IsOpen (domain Γ ρ) := isOpen_domain hΓc ρ
  obtain ⟨F, R₀, κ₀, hCM⟩ := exists_collarMap hn Γ hΓ hΓ0 ρ hρ a ha ha_symm ha_ell
  have hR₀ : 0 < R₀ := hCM.R₀_pos
  have hκ₀ : 1 ≤ κ₀ := hCM.one_le_κ₀
  obtain ⟨ε, hε, hcover⟩ := hCM.cover
  have hFc : Continuous F := hCM.smooth.continuous
  have hF1 : ContDiff ℝ 1 F := hCM.smooth.of_le (by exact_mod_cast le_top)
  have hDFc : Continuous (fderiv ℝ F) := hCM.smooth.continuous_fderiv (by simp)
  have hF0 : F 0 = 0 := by
    have h := hCM.lip 0 (Metric.mem_ball_self hR₀)
    rw [norm_zero, mul_zero] at h
    exact norm_le_zero_iff.mp h
  have hpos : ∀ X ∈ halfBall n R₀, F X ∈ domain Γ ρ := fun X hX =>
    hCM.pos X (halfBall_subset_ball R₀ hX) hX.2
  have hcl : ∀ X ∈ Metric.ball (0 : Space n) R₀, 0 ≤ vcoord X →
      F X ∈ domainWithBoundary Γ ρ := by
    intro X hX ht
    rcases ht.lt_or_eq with h | h
    · exact domain_subset_domainWithBoundary Γ ρ (hCM.pos X hX h)
    · exact boundaryPiece_subset_domainWithBoundary Γ ρ (hCM.flat X hX h.symm)
  -- Part 2: the transformed equation
  obtain ⟨B₀, hB₀c, hB₀eq⟩ := transformed_equation Γ hΓc ρ a ha b hb c u hu hL F hCM.smooth R₀
    hCM.invertible hpos
  -- Part 3: globalized coefficients
  obtain ⟨lam_a, hlam_a, ha_ell'⟩ := ha_ell
  have hA₀ : ContDiffOn ℝ 2 (tildeA F a) (Metric.ball 0 R₀) :=
    contDiffOn_tildeA F hCM.smooth a ha _ Metric.isOpen_ball hCM.invertible
  have hsymm : ∀ x ∈ Metric.ball (0 : Space n) R₀, ∀ ξ η,
      ⟪tildeA F a x ξ, η⟫_ℝ = ⟪ξ, tildeA F a x η⟫_ℝ :=
    fun x _ ξ η => tildeA_symm F a ha_symm x ξ η
  have hell : ∀ r < R₀, ∃ lam > 0, ∀ x ∈ Metric.closedBall (0 : Space n) r, ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ ⟪tildeA F a x ξ, ξ⟫_ℝ := by
    intro r hr
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space n) r).exists_bound_of_continuousOn
      hDFc.continuousOn
    refine ⟨lam_a / (max M 1) ^ 2, by positivity, fun x hx ξ => ?_⟩
    have hxball : x ∈ Metric.ball (0 : Space n) R₀ := Metric.closedBall_subset_ball hr hx
    exact tildeA_ell F a hlam_a (by positivity) ha_ell' (hCM.invertible x hxball)
      ((hM x hx).trans (le_max_left _ _)) ξ
  have hC₀c : ContinuousOn (fun Y => c (F Y)) (Metric.ball 0 R₀) :=
    (hc.comp hFc).continuousOn
  obtain ⟨A, B, C, lam, K, hgood, hagree⟩ := globalize R₀ hR₀ (tildeA F a) hA₀ hsymm hell
    B₀ hB₀c (fun Y => c (F Y)) hC₀c
  -- the constant
  set κ : ℝ := max κ₀ (R₀ / ε) with hκdef
  have hκκ₀ : κ₀ ≤ κ := le_max_left _ _
  have hκ1 : 1 ≤ κ := hκ₀.trans hκκ₀
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ1
  have hκ₀pos : 0 < κ₀ := lt_of_lt_of_le one_pos hκ₀
  have hκε : R₀ / ε ≤ κ := le_max_right _ _
  refine ⟨κ, hκ1, fun R₁ hR₁ => ?_⟩
  set R : ℝ := min R₁ (R₀ / 4) with hRdef
  have hRpos : 0 < R := lt_min hR₁ (by positivity)
  have hRR₁ : R ≤ R₁ := min_le_left _ _
  have hRR₀ : R ≤ R₀ / 4 := min_le_right _ _
  have hball_sub : Metric.ball (0 : Space n) R ⊆ Metric.ball 0 (R₀ / 2) :=
    Metric.ball_subset_ball (by linarith)
  have hball_sub' : Metric.ball (0 : Space n) (R₀ / 2) ⊆ Metric.ball 0 R₀ :=
    Metric.ball_subset_ball (by linarith)
  have hAeq : ∀ X ∈ Metric.ball (0 : Space n) (R₀ / 2), A =ᶠ[𝓝 X] tildeA F a := by
    intro X hX
    filter_upwards [Metric.isOpen_ball.mem_nhds hX] with Y hY
    exact (hagree Y hY).1
  -- the fields of the half-ball solution
  have hA0 : A 0 = ContinuousLinearMap.id ℝ (Space n) := by
    rw [(hagree 0 (Metric.mem_ball_self (by positivity))).1]
    exact tildeA_zero F a (hCM.invertible 0 (Metric.mem_ball_self hR₀)) hCM.at_zero hF0
  have hconormal : ∀ x ∈ flatPiece n R, ∃ c : ℝ, A x (ed n) = c • ed n := by
    intro x hx
    have hx2 := hball_sub (flatPiece_subset_ball R hx)
    have hx0 := hball_sub' hx2
    obtain ⟨μ, -, hμ⟩ := hCM.normal x hx0 hx.2
    obtain ⟨s, hs⟩ := hCM.conormal x hx0 hx.2
    refine ⟨μ * s, ?_⟩
    rw [(hagree x hx2).1]
    exact tildeA_conormal Γ F a (hCM.invertible x hx0) hμ hs
  have hv_cd : ContDiffOn ℝ 2 (fun X => u (F X)) (halfBall n R) := by
    refine hu.comp (hCM.smooth.of_le ?_).contDiffOn ?_
    · simp
    · intro X hX
      exact hpos X (halfBall_mono (by linarith) hX)
  have hchb : ∀ X ∈ closedHalfBall n R, F X ∈ domainWithBoundary Γ ρ := fun X hX =>
    hcl X (hball_sub' (hball_sub (closedHalfBall_subset_ball R hX))) hX.2
  have hv_c : ContinuousOn (fun X => u (F X)) (closedHalfBall n R) :=
    hu_cont.comp hFc.continuousOn hchb
  have hDv_c : ContinuousOn (fun X => ContinuousLinearMap.adjoint (fderiv ℝ F X) (Du (F X)))
      (closedHalfBall n R) := by
    have h1 : Continuous (fun X => ContinuousLinearMap.adjoint (fderiv ℝ F X)) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space n) (F := Space n)).continuous.comp hDFc
    exact h1.continuousOn.clm_apply (hDu_cont.comp hFc.continuousOn hchb)
  have hgrad : ∀ X ∈ halfBall n R, gradient (fun Y => u (F Y)) X =
      ContinuousLinearMap.adjoint (fderiv ℝ F X) (Du (F X)) := by
    intro X hX
    have hFX : F X ∈ domain Γ ρ := hpos X (halfBall_mono (by linarith) hX)
    have hud : DifferentiableAt ℝ u (F X) :=
      (hu.differentiableOn (by norm_num)).differentiableAt (hdom_open.mem_nhds hFX)
    rw [gradient_comp hud (hF1.differentiable (by norm_num) X), hDu (F X) hFX]
  have heqn : ∀ X ∈ halfBall n R, ellOp A B C (fun Y => u (F Y)) X = 0 := by
    intro X hX
    have hX2 : X ∈ Metric.ball (0 : Space n) (R₀ / 2) := hball_sub (halfBall_subset_ball R hX)
    rw [ellOp_congr (C' := fun Y => c (F Y)) (hAeq X hX2) (hagree X hX2).2.1 (hagree X hX2).2.2]
    exact hB₀eq X (halfBall_mono (by linarith) hX)
  have hdir : ∀ N : ℕ, ∃ Cn : ℝ, ∀ x ∈ flatPiece n R, |u (F x)| ≤ Cn * ‖x‖ ^ N := by
    intro N
    obtain ⟨C₁, hC₁⟩ := hDir N
    refine ⟨max C₁ 0 * κ₀ ^ N, fun x hx => ?_⟩
    have hx0 : x ∈ Metric.ball (0 : Space n) R₀ :=
      hball_sub' (hball_sub (flatPiece_subset_ball R hx))
    have hFx := hCM.flat x hx0 hx.2
    calc |u (F x)| ≤ C₁ * ‖F x‖ ^ N := hC₁ _ hFx
      _ ≤ max C₁ 0 * ‖F x‖ ^ N := by gcongr; exact le_max_left _ _
      _ ≤ max C₁ 0 * (κ₀ * ‖x‖) ^ N := by
          gcongr
          exact hCM.lip x hx0
      _ = max C₁ 0 * κ₀ ^ N * ‖x‖ ^ N := by rw [mul_pow]; ring
  let S : HalfBallSolution n :=
    { A := A, B := B, C := C, lam := lam, K := K, coeffs := hgood, A_zero := hA0,
      R := R, R_pos := hRpos, conormal := hconormal,
      v := fun X => u (F X),
      Dv := fun X => ContinuousLinearMap.adjoint (fderiv ℝ F X) (Du (F X)),
      v_contDiffOn := hv_cd, v_continuousOn := hv_c, Dv_continuousOn := hDv_c,
      gradient_eq := hgrad, eqn := heqn, dirichlet_flat := hdir }
  refine ⟨S, F, hRR₁, ?_, ?_, ?_, ?_, ?_⟩
  · -- clause 1
    intro X hX
    exact ⟨hpos X (halfBall_mono (by linarith) hX), rfl⟩
  · -- clause 2
    intro X hX
    have hX2 : X ∈ Metric.ball (0 : Space n) (R₀ / 2) := hball_sub (flatPiece_subset_ball R hX)
    have hx0 : X ∈ Metric.ball (0 : Space n) R₀ := hball_sub' hX2
    refine ⟨hCM.flat X hx0 hX.2, (hCM.lip X hx0).trans ?_, (hCM.antilip X hx0).trans ?_, ?_⟩
    · gcongr
    · gcongr
    · obtain ⟨μ, hμle, hμ⟩ := hCM.normal X hx0 hX.2
      show |⟪A X (ContinuousLinearMap.adjoint (fderiv ℝ F X) (Du (F X))), ed n⟫_ℝ| ≤ _
      rw [(hagree X hX2).1, tildeA_adjoint_apply F a (hCM.invertible X hx0), hμ, abs_mul]
      gcongr
      exact hμle.trans hκκ₀
  · -- clause 3
    refine ⟨min ε (R / κ₀), lt_min hε (by positivity), fun x hx hxε => ?_⟩
    have hxε' : x ∈ Metric.ball (0 : Space n) ε := by
      rw [Metric.mem_ball, dist_zero_right]; exact hxε.trans_le (min_le_left _ _)
    obtain ⟨X, hX, rfl⟩ := hcover hxε'
    refine ⟨X, ⟨?_, ?_⟩, rfl⟩
    · calc ‖X‖ ≤ κ₀ * ‖F X‖ := hCM.antilip X hX
        _ < κ₀ * (R / κ₀) := by gcongr; exact hxε.trans_le (min_le_right _ _)
        _ = R := by field_simp
    · by_contra h
      exact hCM.nonpos X hX (not_lt.mp h) hx
  · -- clause 4
    intro W hW hne
    obtain ⟨y, hyW, X, hX, rfl⟩ := hne
    exact ⟨halfBall n R ∩ F ⁻¹' W, (isOpen_halfBall R).inter (hW.preimage hFc), ⟨X, hX, hyW⟩,
      Set.inter_subset_left, fun Y hY => hY.2⟩
  · -- clause 5
    intro r hr
    obtain ⟨hr0, hrR⟩ := hr
    have hrR₀ : r ≤ R₀ / 4 := hrR.trans hRR₀
    show ∫ x in domain Γ ρ ∩ Metric.ball 0 (r / κ), u x ^ 2 ≤
      κ * ∫ X in halfBall n r, u (F X) ^ 2
    have hK : IsCompact (Metric.closedBall (0 : Space n) r ∩ {X | 0 ≤ vcoord X}) :=
      (isCompact_closedBall 0 r).inter_right (isClosed_le continuous_const continuous_vcoord')
    have hKmaps : ∀ X ∈ Metric.closedBall (0 : Space n) r ∩ {X | 0 ≤ vcoord X},
        F X ∈ domainWithBoundary Γ ρ := by
      intro X hX
      exact hcl X (Metric.closedBall_subset_ball (by linarith) hX.1) hX.2
    have hint : IntegrableOn (fun X => u (F X) ^ 2) (halfBall n r) := by
      have hcont : ContinuousOn (fun X => u (F X) ^ 2)
          (Metric.closedBall (0 : Space n) r ∩ {X | 0 ≤ vcoord X}) :=
        (hu_cont.comp hFc.continuousOn hKmaps).pow 2
      refine (hcont.integrableOn_compact hK).mono_set ?_
      intro X hX
      refine ⟨?_, hX.2.le⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hX.1.le
    have hsub : domain Γ ρ ∩ Metric.ball 0 (r / κ) ⊆ F '' halfBall n r := by
      intro x hx
      obtain ⟨hxd, hxb⟩ := hx
      rw [Metric.mem_ball, dist_zero_right] at hxb
      have hxε : x ∈ Metric.ball (0 : Space n) ε := by
        rw [Metric.mem_ball, dist_zero_right]
        refine hxb.trans_le ?_
        have h1 : R₀ ≤ ε * κ := by rw [div_le_iff₀ hε] at hκε; linarith
        have h2 : r ≤ ε * κ := by linarith
        calc r / κ ≤ ε * κ / κ := by gcongr
          _ = ε := by field_simp
      obtain ⟨X, hX, rfl⟩ := hcover hxε
      refine ⟨X, ⟨?_, ?_⟩, rfl⟩
      · calc ‖X‖ ≤ κ₀ * ‖F X‖ := hCM.antilip X hX
          _ ≤ κ * ‖F X‖ := by gcongr
          _ < κ * (r / κ) := by gcongr
          _ = r := by field_simp
      · by_contra h
        exact hCM.nonpos X hX (not_lt.mp h) hxd
    have h1 := l2_comparison F hF1 R₀ κ₀ hCM.injOn hCM.det_le r (by linarith)
      (fun x => u x ^ 2) (fun x => sq_nonneg _) hint _ hsub
    have h2 : 0 ≤ ∫ X in halfBall n r, u (F X) ^ 2 :=
      setIntegral_nonneg (isOpen_halfBall r).measurableSet (fun X _ => sq_nonneg _)
    calc ∫ x in domain Γ ρ ∩ Metric.ball 0 (r / κ), u x ^ 2
        ≤ κ₀ * ∫ X in halfBall n r, u (F X) ^ 2 := h1
      _ ≤ κ * ∫ X in halfBall n r, u (F X) ^ 2 := by gcongr

end MazyaRefinedCauchy
