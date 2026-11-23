module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F2

@[expose] public section

/-!
# Work package U

The theorems stated in this file are the frozen contract of package U (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## Plan of the proof of `weak_ucp`

Let `Z = {x | v = 0 near x}`, an open set containing `x₀`. By preconnectedness it suffices to show
that `closure Z ∩ U ⊆ Z` (`IsPreconnected.subset_of_closure_inter_subset`).

* **Touching ball.** If `xb ∈ closure Z ∩ U \ Z`, pick `y ∈ Z` close to `xb` and a point `x₁ ∉ Z`
  realizing `dist(y, Zᶜ) = r > 0`. Then `v = 0` on `B(y, r)`, `x₁ ∈ U` and `|x₁ - y| = r`.
* **Local step** (`UCP.local_step`): if `v = 0` near `x₁` inside the ball `B(y, |x₁ - y|)`, then
  `v = 0` near `x₁`. This follows from a local Carleman estimate (`UCP.carleman_local`) with
  weight `e^{τ φ}`, `φ = e^{μ ψ}`, `ψ(x) = |x₁ - y|² - |x - y|² - |x - x₁|²`, applied to `χ v`
  for a cutoff `χ` (`UCP.vanish_of_carleman`).

The coefficient `A` is only symmetric on `U`; it is replaced by the globally symmetric
`UCP.symmExt U A`, which agrees with `A` on `U`.

The Carleman estimate is proved with the identities of package F2 (density `1`):
`UCP.carlJ_lower_bound` is the pointwise positivity of the bulk term for `μ` large and a small
ball (with `φ ∈ [1/2, 2]` there), `UCP.integral_identities` integrates the pointwise identities
(`carleman_pointwise`, `carleman_gradient_pointwise`) with `integral_divergence_eq_zero`, and
`UCP.carleman_conjugated_of_bounds` combines them (gradient term with `ϱ = 1` and Young's
inequality); `UCP.carleman_local` returns from `u = e^{τφ} w` to `w`.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

namespace UCP

/-! ### The weight and the symmetric extension -/

/-- The exponent `ψ(x) = |x₁ - y|² - |x - y|² - |x - x₁|²` of the Carleman weight; `ψ(x₁) = 0`. -/
noncomputable def psi (x₁ y x : Space n) : ℝ := ‖x₁ - y‖ ^ 2 - ‖x - y‖ ^ 2 - ‖x - x₁‖ ^ 2

/-- The convexified Carleman weight `φ = e^{μ ψ}`. -/
noncomputable def phi (μ : ℝ) (x₁ y x : Space n) : ℝ := Real.exp (μ * psi x₁ y x)

/-- A globally symmetric extension of `A` from `U` (the identity outside `U`). -/
noncomputable def symmExt (U : Set (Space n)) (A : Space n → Space n →L[ℝ] Space n)
    (x : Space n) : Space n →L[ℝ] Space n := by
  classical
  exact if x ∈ U then A x else ContinuousLinearMap.id ℝ (Space n)

theorem symmExt_eq {U : Set (Space n)} {A : Space n → Space n →L[ℝ] Space n} {x : Space n}
    (hx : x ∈ U) : symmExt U A x = A x := by
  simp [symmExt, hx]

theorem symmExt_symm {U : Set (Space n)} {A : Space n → Space n →L[ℝ] Space n}
    (hsymm : ∀ x ∈ U, ∀ ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ) :
    ∀ x ξ η, ⟪symmExt U A x ξ, η⟫_ℝ = ⟪ξ, symmExt U A x η⟫_ℝ := by
  intro x ξ η
  by_cases hx : x ∈ U
  · rw [symmExt_eq hx]; exact hsymm x hx ξ η
  · simp [symmExt, hx]

theorem symmExt_eventuallyEq {U : Set (Space n)} (hU : IsOpen U)
    (A : Space n → Space n →L[ℝ] Space n) {x : Space n} (hx : x ∈ U) :
    symmExt U A =ᶠ[𝓝 x] A := by
  filter_upwards [hU.mem_nhds hx] with y hy using symmExt_eq hy

/-- `ellOp` only depends on the germ of `A`. -/
theorem ellOp_congr_A {A A' : Space n → Space n →L[ℝ] Space n} {x : Space n}
    (h : A =ᶠ[𝓝 x] A') (B : Space n → Space n) (C : Space n → ℝ) (v : Space n → ℝ) :
    ellOp A B C v x = ellOp A' B C v x := by
  unfold ellOp
  rw [F2.divergence_congr (F := fun y => A y (gradient v y)) (G := fun y => A' y (gradient v y))
    (by filter_upwards [h] with y hy; rw [hy])]

/-- `ellOp` only depends on the germ of `v`. -/
theorem ellOp_congr_v (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n)
    (C : Space n → ℝ) {v v' : Space n → ℝ} {x : Space n} (h : v =ᶠ[𝓝 x] v') :
    ellOp A B C v x = ellOp A B C v' x := by
  unfold ellOp
  have hg : gradient v =ᶠ[𝓝 x] gradient v' := h.gradient
  rw [F2.divergence_congr (F := fun y => A y (gradient v y)) (G := fun y => A y (gradient v' y))
    (by filter_upwards [hg] with y hy; rw [hy]), hg.eq_of_nhds, h.eq_of_nhds]


/-! ### Elementary facts used in the application of the Carleman estimate -/

theorem continuous_psi (x₁ y : Space n) : Continuous (psi x₁ y) := by
  unfold psi
  fun_prop

theorem continuous_phi (μ : ℝ) (x₁ y : Space n) : Continuous (phi μ x₁ y) := by
  unfold phi
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_psi x₁ y))

/-- The weight `φ = e^{μψ}` is smooth. -/
theorem contDiff_phi (μ : ℝ) (x₁ y : Space n) {k : ℕ∞} : ContDiff ℝ k (phi μ x₁ y) := by
  unfold phi psi
  refine Real.contDiff_exp.comp (contDiff_const.mul ?_)
  exact (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).sub
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

theorem ellOp_zero (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n)
    (C : Space n → ℝ) (x : Space n) : ellOp A B C (fun _ => 0) x = 0 := by
  unfold ellOp
  have h1 : (fun y => A y (gradient (fun _ : Space n => (0 : ℝ)) y)) = fun _ => 0 := by
    funext y
    rw [gradient_fun_const, map_zero]
  rw [h1, gradient_fun_const]
  simp [divergence]

theorem contDiff_gradient {w : Space n → ℝ} (hw : ContDiff ℝ 2 w) :
    ContDiff ℝ 1 (gradient w) := by
  rw [F2.gradient_eq_comp]
  exact (F2.toDualSymmCLE (n := n)).contDiff.comp (hw.fderiv_right (by norm_num))

theorem hasCompactSupport_gradient {w : Space n → ℝ} (hw : HasCompactSupport w) :
    HasCompactSupport (gradient w) := by
  rw [F2.gradient_eq_comp]
  exact (hw.fderiv ℝ).comp_left (by simp)


theorem hasCompactSupport_mul_left' {f g : Space n → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => f x * g x) := hg.mul_left

theorem hasCompactSupport_sq {g : Space n → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => g x ^ 2) := hg.comp_left (g := fun t : ℝ => t ^ 2) (by simp)

theorem hasCompactSupport_norm_sq {g : Space n → Space n} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => ‖g x‖ ^ 2) :=
  hg.comp_left (g := fun z : Space n => ‖z‖ ^ 2) (by simp)


theorem le_cube {t : ℝ} (ht : 1 ≤ t) : t ≤ t ^ 3 := by
  have h1 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  calc t = t * 1 := (mul_one t).symm
    _ ≤ t * t ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = t ^ 3 := by ring

theorem gradient_eq_zero_of_eventuallyEq {w : Space n → ℝ} {x : Space n}
    (h : w =ᶠ[𝓝 x] fun _ => 0) : gradient w x = 0 := by
  rw [h.gradient_eq, gradient_fun_const]

theorem psi_le_of_far {x₁ y x : Space n} {a : ℝ} (ha : 0 ≤ a) (h1 : dist x₁ y ≤ dist x y)
    (h2 : a ≤ dist x x₁) : psi x₁ y x ≤ -a ^ 2 := by
  unfold psi
  rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
  have h3 : dist x₁ y ^ 2 ≤ dist x y ^ 2 := pow_le_pow_left₀ dist_nonneg h1 2
  have h4 : a ^ 2 ≤ dist x x₁ ^ 2 := pow_le_pow_left₀ ha h2 2
  linarith

theorem le_psi_of_near {x₁ y x : Space n} {ε : ℝ} (_hε : 0 ≤ ε) (h : dist x x₁ ≤ ε) :
    -(2 * dist x₁ y * ε + 2 * ε ^ 2) ≤ psi x₁ y x := by
  unfold psi
  rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
  have h1 : dist x y ≤ dist x₁ y + ε := by
    calc dist x y ≤ dist x x₁ + dist x₁ y := dist_triangle _ _ _
      _ ≤ dist x₁ y + ε := by linarith
  have h3 : dist x y ^ 2 ≤ (dist x₁ y + ε) ^ 2 := pow_le_pow_left₀ dist_nonneg h1 2
  have h4 : dist x x₁ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ dist_nonneg h 2
  nlinarith

/-! ### The local Carleman estimate -/

/-! #### Pointwise identities with the trivial density -/

/-- Lemma 2.1(1) with density `1`: `e^{τφ} div(A ∇w) = S u + T u` for `u = e^{τφ} w`. -/
theorem conj_identity (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (τ : ℝ)
    (w : Space n → ℝ) (x : Space n) (hA : ContDiffAt ℝ 1 A x)
    (hsymm : ∀ ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ) (hφ : ContDiffAt ℝ 2 φ x)
    (hw : ContDiffAt ℝ 2 w x) :
    Real.exp (τ * φ x) * divergence (fun z => A z (gradient w z)) x
      = carlS (fun _ => 1) A φ τ (fun z => Real.exp (τ * φ z) * w z) x
        + carlT (fun _ => 1) A φ τ (fun z => Real.exp (τ * φ z) * w z) x := by
  have h := F2.carleman_conj_of_symm' (fun _ => (1 : ℝ)) A φ τ w x contDiffAt_const one_ne_zero
    hA hsymm hφ hw
  rwa [F2.divMu_one] at h

theorem gradient_eventually_zero {u : Space n → ℝ} {x : Space n} (h : u =ᶠ[𝓝 x] fun _ => 0) :
    gradient u =ᶠ[𝓝 x] fun _ => 0 := by
  have h2 : ∀ᶠ z in 𝓝 x, u =ᶠ[𝓝 z] fun _ => 0 := h.eventually_nhds
  filter_upwards [h2] with z hz
  exact gradient_eq_zero_of_eventuallyEq hz

theorem divergence_A_grad_eq_zero (A : Space n → Space n →L[ℝ] Space n) {u : Space n → ℝ}
    {x : Space n} (h : u =ᶠ[𝓝 x] fun _ => 0) :
    divergence (fun z => A z (gradient u z)) x = 0 := by
  have h1 : (fun z => A z (gradient u z)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [gradient_eventually_zero h] with z hz
    rw [hz, map_zero]
  rw [F2.divergence_congr h1]
  simp [divergence]

theorem carlS_eq_zero (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (τ : ℝ)
    {u : Space n → ℝ} {x : Space n} (h : u =ᶠ[𝓝 x] fun _ => 0) :
    carlS (fun _ => 1) A φ τ u x = 0 := by
  unfold carlS
  rw [F2.divMu_one, divergence_A_grad_eq_zero A h, h.eq_of_nhds]
  ring

theorem carlT_eq_zero (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (τ : ℝ)
    {u : Space n → ℝ} {x : Space n} (h : u =ᶠ[𝓝 x] fun _ => 0) :
    carlT (fun _ => 1) A φ τ u x = 0 := by
  unfold carlT
  rw [gradient_eq_zero_of_eventuallyEq h, h.eq_of_nhds]
  simp

theorem carlJ_eq_zero (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (τ : ℝ)
    {u : Space n → ℝ} {x : Space n} (h : u =ᶠ[𝓝 x] fun _ => 0) :
    carlJ (fun _ => 1) A φ τ u x = 0 := by
  unfold carlJ
  rw [gradient_eq_zero_of_eventuallyEq h, h.eq_of_nhds]
  simp

theorem carlS_one_eq (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (τ : ℝ)
    (u : Space n → ℝ) : carlS (fun _ => 1) A φ τ u
      = fun y => divergence (fun z => A z (gradient u z)) y + τ ^ 2 * carlQ A φ y * u y := by
  funext y
  simp only [carlS, F2.divMu_one]

theorem divMu_one_fun (W : Space n → Space n) :
    divMu (fun _ => (1 : ℝ)) W = fun y => divergence W y := by
  funext y
  exact F2.divMu_one W y

theorem carlT_one_eq (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (τ : ℝ)
    (u : Space n → ℝ) : carlT (fun _ => 1) A φ τ u
      = fun y => -2 * τ * ⟪carlV A φ y, gradient u y⟫_ℝ
          - τ * divergence (carlV A φ) y * u y := by
  funext y
  simp only [carlT, F2.divMu_one]

theorem carlJ_one_eq (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (τ : ℝ)
    (u : Space n → ℝ) : carlJ (fun _ => 1) A φ τ u
      = fun y => 2 * τ ^ 3 * ⟪carlV A φ y, gradient (carlQ A φ) y⟫_ℝ * u y ^ 2
        + 4 * τ * ⟪fderiv ℝ (carlV A φ) y (A y (gradient u y)), gradient u y⟫_ℝ
        - 2 * τ * ⟪fderiv ℝ A y (carlV A φ y) (gradient u y), gradient u y⟫_ℝ
        + 2 * τ * u y * ⟪A y (gradient u y),
            gradient (fun z => divergence (carlV A φ) z) y⟫_ℝ := by
  funext y
  simp only [carlJ, divMu_one_fun, one_mul]

/-! #### Calculus of the weight -/

/-- `p = ∇ψ = 2 (y - x) + 2 (x₁ - x)`. -/
noncomputable def pvec (x₁ y x : Space n) : Space n := (2 : ℝ) • (y - x) + (2 : ℝ) • (x₁ - x)

/-- `W = A p`, so that `V = A ∇φ = μ φ W`. -/
noncomputable def Wfun (A : Space n → Space n →L[ℝ] Space n) (x₁ y x : Space n) : Space n :=
  A x (pvec x₁ y x)

/-- `k = ⟪A p, p⟫`, so that `q = (μ φ)² k`. -/
noncomputable def kfun (A : Space n → Space n →L[ℝ] Space n) (x₁ y x : Space n) : ℝ :=
  ⟪A x (pvec x₁ y x), pvec x₁ y x⟫_ℝ

theorem hasFDerivAt_psi (x₁ y x : Space n) :
    HasFDerivAt (psi x₁ y) (innerSL ℝ (pvec x₁ y x)) x := by
  have h1 := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y).norm_sq
  have h2 := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₁).norm_sq
  have h := ((hasFDerivAt_const (‖x₁ - y‖ ^ 2) x).sub h1).sub h2
  refine h.congr_fderiv ?_
  ext ξ
  simp [pvec]
  ring

theorem hasFDerivAt_phi (μ : ℝ) (x₁ y x : Space n) :
    HasFDerivAt (phi μ x₁ y) ((μ * phi μ x₁ y x) • innerSL ℝ (pvec x₁ y x)) x := by
  have h := ((hasFDerivAt_psi x₁ y x).const_mul μ).exp
  refine h.congr_fderiv ?_
  rw [smul_smul, phi, mul_comm]

theorem gradient_phi (μ : ℝ) (x₁ y : Space n) :
    gradient (phi μ x₁ y) = fun x => (μ * phi μ x₁ y x) • pvec x₁ y x := by
  funext x
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, (hasFDerivAt_phi μ x₁ y x).fderiv, real_inner_smul_left]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]

theorem carlV_phi (A : Space n → Space n →L[ℝ] Space n) (μ : ℝ) (x₁ y : Space n) :
    carlV A (phi μ x₁ y) = fun x => (μ * phi μ x₁ y x) • Wfun A x₁ y x := by
  funext x
  simp only [carlV, gradient_phi, map_smul, Wfun]

theorem carlQ_phi (A : Space n → Space n →L[ℝ] Space n) (μ : ℝ) (x₁ y : Space n) :
    carlQ A (phi μ x₁ y) = fun x => (μ * phi μ x₁ y x) * (μ * phi μ x₁ y x) * kfun A x₁ y x := by
  funext x
  simp only [carlQ, gradient_phi, map_smul, real_inner_smul_left, real_inner_smul_right, kfun]
  ring

theorem contDiff_pvec (x₁ y : Space n) {k : ℕ∞} : ContDiff ℝ k (pvec x₁ y) := by
  unfold pvec
  fun_prop

theorem hasFDerivAt_muphi (μ : ℝ) (x₁ y x : Space n) :
    HasFDerivAt (fun z => μ * phi μ x₁ y z)
      (μ • ((μ * phi μ x₁ y x) • innerSL ℝ (pvec x₁ y x))) x :=
  (hasFDerivAt_phi μ x₁ y x).const_mul μ

theorem fderiv_carlV_apply (A : Space n → Space n →L[ℝ] Space n) (μ : ℝ) (x₁ y x : Space n)
    (hW : DifferentiableAt ℝ (Wfun A x₁ y) x) (ξ : Space n) :
    fderiv ℝ (carlV A (phi μ x₁ y)) x ξ
      = (μ * ((μ * phi μ x₁ y x) * ⟪pvec x₁ y x, ξ⟫_ℝ)) • Wfun A x₁ y x
        + (μ * phi μ x₁ y x) • fderiv ℝ (Wfun A x₁ y) x ξ := by
  rw [carlV_phi]
  have h := (hasFDerivAt_muphi μ x₁ y x).smul hW.hasFDerivAt
  rw [show (fun x => (μ * phi μ x₁ y x) • Wfun A x₁ y x)
      = (fun z => μ * phi μ x₁ y z) • Wfun A x₁ y from rfl, h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [add_comm]

theorem fderiv_carlQ_apply (A : Space n → Space n →L[ℝ] Space n) (μ : ℝ) (x₁ y x : Space n)
    (hk : DifferentiableAt ℝ (kfun A x₁ y) x) (ξ : Space n) :
    fderiv ℝ (carlQ A (phi μ x₁ y)) x ξ
      = 2 * (μ * phi μ x₁ y x) * (μ * ((μ * phi μ x₁ y x) * ⟪pvec x₁ y x, ξ⟫_ℝ))
          * kfun A x₁ y x
        + (μ * phi μ x₁ y x) * (μ * phi μ x₁ y x) * fderiv ℝ (kfun A x₁ y) x ξ := by
  rw [carlQ_phi]
  have h := ((hasFDerivAt_muphi μ x₁ y x).mul (hasFDerivAt_muphi μ x₁ y x)).mul hk.hasFDerivAt
  rw [show (fun x => μ * phi μ x₁ y x * (μ * phi μ x₁ y x) * kfun A x₁ y x)
      = ((fun z => μ * phi μ x₁ y z) * fun z => μ * phi μ x₁ y z) * kfun A x₁ y from rfl,
    h.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, Pi.mul_apply]
  ring

/-- `⟪V, ∇q⟫ = 2 μ (μφ)³ k² + (μφ)³ Dk(W)`. -/
theorem inner_carlV_gradient_carlQ (A : Space n → Space n →L[ℝ] Space n) (μ : ℝ)
    (x₁ y x : Space n) (hk : DifferentiableAt ℝ (kfun A x₁ y) x) :
    ⟪carlV A (phi μ x₁ y) x, gradient (carlQ A (phi μ x₁ y)) x⟫_ℝ
      = 2 * μ * (μ * phi μ x₁ y x) ^ 3 * kfun A x₁ y x ^ 2
        + (μ * phi μ x₁ y x) ^ 3 * fderiv ℝ (kfun A x₁ y) x (Wfun A x₁ y x) := by
  rw [real_inner_comm, inner_gradient_left, fderiv_carlQ_apply A μ x₁ y x hk, carlV_phi]
  simp only [map_smul, smul_eq_mul, real_inner_smul_right]
  have : ⟪pvec x₁ y x, Wfun A x₁ y x⟫_ℝ = kfun A x₁ y x := by
    rw [real_inner_comm]; rfl
  rw [this]
  ring

/-- `⟪DV(A g), g⟫ = μ (μφ) ⟪W, g⟫² + (μφ) ⟪DW(A g), g⟫` (uses the symmetry of `A x`). -/
theorem inner_fderiv_carlV (A : Space n → Space n →L[ℝ] Space n) (μ : ℝ) (x₁ y x : Space n)
    (hsymm : ∀ ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (hW : DifferentiableAt ℝ (Wfun A x₁ y) x) (g : Space n) :
    ⟪fderiv ℝ (carlV A (phi μ x₁ y)) x (A x g), g⟫_ℝ
      = μ * (μ * phi μ x₁ y x) * ⟪Wfun A x₁ y x, g⟫_ℝ ^ 2
        + (μ * phi μ x₁ y x) * ⟪fderiv ℝ (Wfun A x₁ y) x (A x g), g⟫_ℝ := by
  rw [fderiv_carlV_apply A μ x₁ y x hW, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  have : ⟪pvec x₁ y x, A x g⟫_ℝ = ⟪Wfun A x₁ y x, g⟫_ℝ := by
    rw [Wfun, hsymm]
  rw [this]
  ring

/-! #### The pointwise lower bound for the bulk term (the positivity argument) -/

theorem differentiableAt_Wfun (A : Space n → Space n →L[ℝ] Space n) (x₁ y x : Space n)
    (hA : DifferentiableAt ℝ A x) : DifferentiableAt ℝ (Wfun A x₁ y) x :=
  hA.clm_apply ((contDiff_pvec x₁ y (k := 1)).differentiable one_ne_zero x)

theorem differentiableAt_kfun (A : Space n → Space n →L[ℝ] Space n) (x₁ y x : Space n)
    (hA : DifferentiableAt ℝ A x) : DifferentiableAt ℝ (kfun A x₁ y) x :=
  (differentiableAt_Wfun A x₁ y x hA).inner ℝ
    ((contDiff_pvec x₁ y (k := 1)).differentiable one_ne_zero x)

/-- The pointwise lower bound for `carlJ` at one point, from bounds at that point. -/
theorem carlJ_pointwise (A : Space n → Space n →L[ℝ] Space n) (x₁ y : Space n) (μ : ℝ)
    (hμ : 0 < μ) (x : Space n) (hAx : DifferentiableAt ℝ A x)
    (hsymm : ∀ ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (lam Λ Λ₁ Kk KW D₃ r : ℝ) (hlam : 0 < lam) (hr : 0 < r)
    (hφlo : 1 / 2 ≤ phi μ x₁ y x) (hφhi : phi μ x₁ y x ≤ 2)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ) (hΛ : ‖A x‖ ≤ Λ) (hΛ₁ : ‖fderiv ℝ A x‖ ≤ Λ₁)
    (hKk : ‖fderiv ℝ (kfun A x₁ y) x‖ ≤ Kk) (hKW : ‖fderiv ℝ (Wfun A x₁ y) x‖ ≤ KW)
    (hD₃ : ‖gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x‖ ≤ D₃)
    (hp0 : r ≤ ‖pvec x₁ y x‖) (hp1 : ‖pvec x₁ y x‖ ≤ 3 * r)
    (hbr : 0 ≤ 2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r)))
    (τ : ℝ) (hτ : 0 ≤ τ) (u : Space n → ℝ) :
    μ ^ 3 / 4 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))) * τ ^ 3 * u x ^ 2
      - μ * (8 * (KW * Λ) + 4 * (Λ₁ * (Λ * (3 * r))) + 1) * τ * ‖gradient u x‖ ^ 2
      - Λ ^ 2 * D₃ ^ 2 / μ * τ * u x ^ 2
      ≤ carlJ (fun _ => 1) A (phi μ x₁ y) τ u x := by
  rw [carlJ_one_eq]
  dsimp only
  have hW := differentiableAt_Wfun A x₁ y x hAx
  have hk := differentiableAt_kfun A x₁ y x hAx
  rw [inner_carlV_gradient_carlQ A μ x₁ y x hk, inner_fderiv_carlV A μ x₁ y x hsymm hW]
  set g := gradient u x with hg
  set M := μ * phi μ x₁ y x with hM
  set kx := kfun A x₁ y x with hkx
  set Wx := Wfun A x₁ y x with hWx
  set px := pvec x₁ y x with hpx
  have hMlo : μ / 2 ≤ M := by
    have := mul_le_mul_of_nonneg_left hφlo hμ.le
    rw [hM]; linarith
  have hMhi : M ≤ 2 * μ := by
    have := mul_le_mul_of_nonneg_left hφhi hμ.le
    rw [hM]; linarith
  have hM0 : 0 ≤ M := by linarith
  have hΛ0 : 0 ≤ Λ := (norm_nonneg (A x)).trans hΛ
  have hΛ₁0 : 0 ≤ Λ₁ := (norm_nonneg (fderiv ℝ A x)).trans hΛ₁
  have hKk0 : 0 ≤ Kk := (norm_nonneg (fderiv ℝ (kfun A x₁ y) x)).trans hKk
  have hKW0 : 0 ≤ KW := (norm_nonneg (fderiv ℝ (Wfun A x₁ y) x)).trans hKW
  have hD₃0 : 0 ≤ D₃ := (norm_nonneg _).trans hD₃
  -- the zeroth order coefficient
  have hkx : lam * r ^ 2 ≤ kx := by
    have h1 := hell px
    have h2 : r ^ 2 ≤ ‖px‖ ^ 2 := pow_le_pow_left₀ hr.le hp0 2
    rw [hkx, kfun]
    calc lam * r ^ 2 ≤ lam * ‖px‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hlam.le
      _ ≤ _ := h1
  have hkx2 : lam ^ 2 * r ^ 4 ≤ kx ^ 2 := by
    have h0 : 0 ≤ lam * r ^ 2 := by positivity
    have := pow_le_pow_left₀ h0 hkx 2
    linarith
  have hWn : ‖Wx‖ ≤ Λ * (3 * r) := by
    calc ‖Wx‖ = ‖A x px‖ := rfl
      _ ≤ ‖A x‖ * ‖px‖ := (A x).le_opNorm px
      _ ≤ Λ * (3 * r) := mul_le_mul hΛ hp1 (norm_nonneg _) hΛ0
  have hDkW : -(Kk * (Λ * (3 * r))) ≤ fderiv ℝ (kfun A x₁ y) x Wx := by
    have h1 : |fderiv ℝ (kfun A x₁ y) x Wx| ≤ Kk * (Λ * (3 * r)) := by
      calc |fderiv ℝ (kfun A x₁ y) x Wx| = ‖fderiv ℝ (kfun A x₁ y) x Wx‖ := rfl
        _ ≤ ‖fderiv ℝ (kfun A x₁ y) x‖ * ‖Wx‖ := (fderiv ℝ (kfun A x₁ y) x).le_opNorm Wx
        _ ≤ Kk * (Λ * (3 * r)) := mul_le_mul hKk hWn (norm_nonneg _) hKk0
    linarith [neg_abs_le (fderiv ℝ (kfun A x₁ y) x Wx)]
  have hT1 : (μ / 2) ^ 3 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r)))
      ≤ 2 * μ * M ^ 3 * kx ^ 2 + M ^ 3 * fderiv ℝ (kfun A x₁ y) x Wx := by
    have h1 : 2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))
        ≤ 2 * μ * kx ^ 2 + fderiv ℝ (kfun A x₁ y) x Wx := by
      have := mul_le_mul_of_nonneg_left hkx2 (by positivity : (0:ℝ) ≤ 2 * μ)
      linarith
    have h2 : (μ / 2) ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (by positivity) hMlo 3
    calc (μ / 2) ^ 3 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r)))
        ≤ M ^ 3 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))) :=
          mul_le_mul_of_nonneg_right h2 hbr
      _ ≤ M ^ 3 * (2 * μ * kx ^ 2 + fderiv ℝ (kfun A x₁ y) x Wx) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * μ * M ^ 3 * kx ^ 2 + M ^ 3 * fderiv ℝ (kfun A x₁ y) x Wx := by ring
  -- the gradient terms
  have hAg : ‖A x g‖ ≤ Λ * ‖g‖ := ((A x).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right hΛ (norm_nonneg _))
  have hT2 : -(2 * μ * (KW * Λ) * ‖g‖ ^ 2)
      ≤ μ * M * ⟪Wx, g⟫_ℝ ^ 2 + M * ⟪fderiv ℝ (Wfun A x₁ y) x (A x g), g⟫_ℝ := by
    have h1 : |⟪fderiv ℝ (Wfun A x₁ y) x (A x g), g⟫_ℝ| ≤ KW * Λ * ‖g‖ ^ 2 := by
      calc |⟪fderiv ℝ (Wfun A x₁ y) x (A x g), g⟫_ℝ|
          ≤ ‖fderiv ℝ (Wfun A x₁ y) x (A x g)‖ * ‖g‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖fderiv ℝ (Wfun A x₁ y) x‖ * ‖A x g‖) * ‖g‖ :=
            mul_le_mul_of_nonneg_right ((fderiv ℝ (Wfun A x₁ y) x).le_opNorm _) (norm_nonneg _)
        _ ≤ (KW * (Λ * ‖g‖)) * ‖g‖ := by gcongr
        _ = KW * Λ * ‖g‖ ^ 2 := by ring
    have h2 : 0 ≤ μ * M * ⟪Wx, g⟫_ℝ ^ 2 := by positivity
    have h3 : -(KW * Λ * ‖g‖ ^ 2) ≤ ⟪fderiv ℝ (Wfun A x₁ y) x (A x g), g⟫_ℝ := by
      linarith [neg_abs_le ⟪fderiv ℝ (Wfun A x₁ y) x (A x g), g⟫_ℝ]
    have h4 : M * (-(KW * Λ * ‖g‖ ^ 2)) ≤ M * ⟪fderiv ℝ (Wfun A x₁ y) x (A x g), g⟫_ℝ :=
      mul_le_mul_of_nonneg_left h3 hM0
    have h5 : M * (KW * Λ * ‖g‖ ^ 2) ≤ 2 * μ * (KW * Λ * ‖g‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hMhi (by positivity)
    linarith
  have hV : carlV A (phi μ x₁ y) x = M • Wx := by rw [carlV_phi]
  have hT3 : ⟪fderiv ℝ A x (carlV A (phi μ x₁ y) x) g, g⟫_ℝ
      ≤ 2 * μ * (Λ₁ * (Λ * (3 * r))) * ‖g‖ ^ 2 := by
    have hVn : ‖carlV A (phi μ x₁ y) x‖ ≤ 2 * μ * (Λ * (3 * r)) := by
      rw [hV, norm_smul, Real.norm_eq_abs, abs_of_nonneg hM0]
      exact mul_le_mul hMhi hWn (norm_nonneg _) (by positivity)
    calc ⟪fderiv ℝ A x (carlV A (phi μ x₁ y) x) g, g⟫_ℝ
        ≤ |⟪fderiv ℝ A x (carlV A (phi μ x₁ y) x) g, g⟫_ℝ| := le_abs_self _
      _ ≤ ‖fderiv ℝ A x (carlV A (phi μ x₁ y) x) g‖ * ‖g‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖fderiv ℝ A x (carlV A (phi μ x₁ y) x)‖ * ‖g‖) * ‖g‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ A x (carlV A (phi μ x₁ y) x)).le_opNorm g)
            (norm_nonneg _)
      _ ≤ ((‖fderiv ℝ A x‖ * ‖carlV A (phi μ x₁ y) x‖) * ‖g‖) * ‖g‖ := by
          gcongr
          exact (fderiv ℝ A x).le_opNorm _
      _ ≤ ((Λ₁ * (2 * μ * (Λ * (3 * r)))) * ‖g‖) * ‖g‖ := by gcongr
      _ = 2 * μ * (Λ₁ * (Λ * (3 * r))) * ‖g‖ ^ 2 := by ring
  have hT4 : -(μ * ‖g‖ ^ 2 + Λ ^ 2 * D₃ ^ 2 / μ * u x ^ 2)
      ≤ 2 * u x * ⟪A x g, gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x⟫_ℝ := by
    have h1 : |⟪A x g, gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x⟫_ℝ|
        ≤ Λ * ‖g‖ * D₃ := by
      calc |⟪A x g, gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x⟫_ℝ|
          ≤ ‖A x g‖ * ‖gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (Λ * ‖g‖) * D₃ := mul_le_mul hAg hD₃ (norm_nonneg _) (by positivity)
    have h2 : |2 * u x * ⟪A x g, gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x⟫_ℝ|
        ≤ 2 * |u x| * (Λ * ‖g‖ * D₃) := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * |u x| * (Λ * ‖g‖ * D₃) ≤ μ * ‖g‖ ^ 2 + Λ ^ 2 * D₃ ^ 2 / μ * u x ^ 2 := by
      have hsq : 0 ≤ (μ * ‖g‖ - Λ * D₃ * |u x|) ^ 2 / μ := by positivity
      have heq : (μ * ‖g‖ - Λ * D₃ * |u x|) ^ 2 / μ
          = μ * ‖g‖ ^ 2 + Λ ^ 2 * D₃ ^ 2 / μ * u x ^ 2 - 2 * |u x| * (Λ * ‖g‖ * D₃) := by
        field_simp
        rw [show u x ^ 2 = |u x| ^ 2 from (sq_abs _).symm]
        ring
      linarith
    linarith [neg_abs_le (2 * u x * ⟪A x g, gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x⟫_ℝ)]
  -- combine
  have hτ3 : 0 ≤ τ ^ 3 := pow_nonneg hτ 3
  have hu2 : 0 ≤ u x ^ 2 := sq_nonneg _
  have e1 : 2 * τ ^ 3 * (2 * μ * M ^ 3 * kx ^ 2 + M ^ 3 * fderiv ℝ (kfun A x₁ y) x Wx) * u x ^ 2
      ≥ 2 * τ ^ 3 * ((μ / 2) ^ 3 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r)))) * u x ^ 2 := by
    have := mul_le_mul_of_nonneg_left hT1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hτ3)
    exact mul_le_mul_of_nonneg_right this hu2
  have e2 := mul_le_mul_of_nonneg_left hT2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hτ)
  have e3 := mul_le_mul_of_nonneg_left hT3 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hτ)
  have e4 := mul_le_mul_of_nonneg_left hT4 hτ
  have e5 : 2 * τ * u x * ⟪A x g, gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x⟫_ℝ
      = τ * (2 * u x * ⟪A x g, gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x⟫_ℝ) := by
    ring
  rw [e5]
  have e6 : 2 * τ ^ 3 * ((μ / 2) ^ 3 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r)))) * u x ^ 2
      = μ ^ 3 / 4 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))) * τ ^ 3 * u x ^ 2 := by ring
  linarith

theorem exists_ellipticity (A : Space n → Space n →L[ℝ] Space n) (x₁ : Space n)
    (hcont : ContinuousAt A x₁) (hpos : ∀ ξ, ξ ≠ 0 → 0 < ⟪A x₁ ξ, ξ⟫_ℝ) :
    ∃ lam > 0, ∃ δ > 0, ∀ x ∈ Metric.ball x₁ δ, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ := by
  obtain ⟨ξ₀, hξ₀, hmin⟩ := (isCompact_sphere (0 : Space n) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one)
    (Continuous.continuousOn (f := fun ξ => ⟪A x₁ ξ, ξ⟫_ℝ) (by fun_prop))
  have hξ₀n : ‖ξ₀‖ = 1 := by simpa using hξ₀
  have hl₀ : 0 < ⟪A x₁ ξ₀, ξ₀⟫_ℝ := hpos ξ₀ (by
    intro h
    rw [h, norm_zero] at hξ₀n
    exact zero_ne_one hξ₀n)
  set l₀ := ⟪A x₁ ξ₀, ξ₀⟫_ℝ with hl₀def
  have hcoer : ∀ ξ, l₀ * ‖ξ‖ ^ 2 ≤ ⟪A x₁ ξ, ξ⟫_ℝ := by
    intro ξ
    by_cases hξ : ξ = 0
    · simp [hξ]
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      have hmem : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : Space n) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := isMinOn_iff.mp hmin _ hmem
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
      have e : ‖ξ‖⁻¹ * (‖ξ‖⁻¹ * ⟪A x₁ ξ, ξ⟫_ℝ) = ⟪A x₁ ξ, ξ⟫_ℝ / ‖ξ‖ ^ 2 := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)] at h1
      exact h1
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont (l₀ / 2) (by positivity)
  refine ⟨l₀ / 2, by positivity, δ, hδ, fun x hx ξ => ?_⟩
  have hd : ‖A x - A x₁‖ < l₀ / 2 := by
    rw [← dist_eq_norm]; exact hball (Metric.mem_ball.mp hx)
  have h1 : |⟪(A x - A x₁) ξ, ξ⟫_ℝ| ≤ l₀ / 2 * ‖ξ‖ ^ 2 := by
    calc |⟪(A x - A x₁) ξ, ξ⟫_ℝ| ≤ ‖(A x - A x₁) ξ‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A x - A x₁‖ * ‖ξ‖) * ‖ξ‖ :=
          mul_le_mul_of_nonneg_right ((A x - A x₁).le_opNorm ξ) (norm_nonneg _)
      _ ≤ (l₀ / 2 * ‖ξ‖) * ‖ξ‖ := by gcongr
      _ = l₀ / 2 * ‖ξ‖ ^ 2 := by ring
  have h2 : ⟪A x ξ, ξ⟫_ℝ = ⟪A x₁ ξ, ξ⟫_ℝ + ⟪(A x - A x₁) ξ, ξ⟫_ℝ := by
    simp [inner_sub_left]
  linarith [hcoer ξ, neg_abs_le ⟪(A x - A x₁) ξ, ξ⟫_ℝ]

theorem psi_le_of_near {x₁ y x : Space n} {ρ : ℝ} (hρr : ρ ≤ dist x₁ y)
    (h : dist x x₁ ≤ ρ) : psi x₁ y x ≤ 2 * dist x₁ y * ρ := by
  unfold psi
  rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
  have h1 : dist x₁ y - ρ ≤ dist x y := by
    have := dist_triangle x₁ x y
    rw [dist_comm x₁ x] at this
    linarith
  have h2 : (dist x₁ y - ρ) ^ 2 ≤ dist x y ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  nlinarith [sq_nonneg (dist x x₁), sq_nonneg ρ]

theorem pvec_eq (x₁ y x : Space n) :
    pvec x₁ y x = (2 : ℝ) • (y - x₁) - (4 : ℝ) • (x - x₁) := by
  unfold pvec
  module

theorem norm_pvec_bounds {x₁ y x : Space n} {ρ : ℝ} (hρ : ρ ≤ dist x₁ y / 4)
    (h : dist x x₁ ≤ ρ) :
    dist x₁ y ≤ ‖pvec x₁ y x‖ ∧ ‖pvec x₁ y x‖ ≤ 3 * dist x₁ y := by
  rw [pvec_eq]
  have h1 : ‖(2 : ℝ) • (y - x₁)‖ = 2 * dist x₁ y := by
    rw [norm_smul, ← dist_eq_norm, dist_comm]; norm_num
  have h2 : ‖(4 : ℝ) • (x - x₁)‖ ≤ 4 * ρ := by
    rw [norm_smul, ← dist_eq_norm]; norm_num; linarith
  constructor
  · have := norm_sub_norm_le ((2 : ℝ) • (y - x₁)) ((4 : ℝ) • (x - x₁))
    linarith
  · have := norm_sub_le ((2 : ℝ) • (y - x₁)) ((4 : ℝ) • (x - x₁))
    linarith

/-- **Pointwise positivity of the bulk term** (lem:bdryCarleman (a), (b) of the note, in the
interior). For `μ` large and `ρ` small, on `closedBall x₁ ρ`:
`carlJ ≥ cJ τ³ u² - bJ τ |∇u|² - bJ' τ u²`, with `2 bJ Q ≤ cJ λ`, where `λ` is an ellipticity
constant of `A` and `Q` bounds `q = ⟪A ∇φ, ∇φ⟫`. -/
theorem carlJ_lower_bound (A : Space n → Space n →L[ℝ] Space n) (x₁ y : Space n) (hxy : x₁ ≠ y)
    (hA : ContDiffAt ℝ 2 A x₁) (hsymm : ∀ x ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (hpos : ∀ ξ, ξ ≠ 0 → 0 < ⟪A x₁ ξ, ξ⟫_ℝ) :
    ∃ μ > 0, ∃ ρ > 0, ∃ lam > 0, ∃ Q ≥ 0, ∃ cJ > 0, ∃ bJ ≥ 0, ∃ bJ' ≥ 0,
      2 * bJ * Q ≤ cJ * lam ∧
      (∀ x ∈ Metric.closedBall x₁ ρ, ContDiffAt ℝ 2 A x) ∧
      (∀ x ∈ Metric.closedBall x₁ ρ, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ) ∧
      (∀ x ∈ Metric.closedBall x₁ ρ, carlQ A (phi μ x₁ y) x ≤ Q) ∧
      (∀ x ∈ Metric.closedBall x₁ ρ, ∀ τ : ℝ, 0 ≤ τ → ∀ u : Space n → ℝ, ContDiffAt ℝ 2 u x →
        cJ * τ ^ 3 * u x ^ 2 - bJ * τ * ‖gradient u x‖ ^ 2 - bJ' * τ * u x ^ 2
          ≤ carlJ (fun _ => 1) A (phi μ x₁ y) τ u x) := by
  obtain ⟨r, hr⟩ : ∃ r, r = dist x₁ y := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact dist_pos.mpr hxy
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.eventually_nhds_iff_ball.mp (hA.eventually (by simp))
  obtain ⟨lam, hlam, δ, hδ, hell⟩ := exists_ellipticity A x₁ hA.continuousAt hpos
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = min (min (ε₁ / 2) (δ / 2)) (r / 4) := ⟨_, rfl⟩
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀]; exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hm1 := min_le_left (min (ε₁ / 2) (δ / 2)) (r / 4)
  have hm2 := min_le_right (min (ε₁ / 2) (δ / 2)) (r / 4)
  have hm3 := min_le_left (ε₁ / 2) (δ / 2)
  have hm4 := min_le_right (ε₁ / 2) (δ / 2)
  have hρ₀ε : ρ₀ < ε₁ := by rw [hρ₀]; linarith
  have hρ₀δ : ρ₀ < δ := by rw [hρ₀]; linarith
  have hρ₀r : ρ₀ ≤ r / 4 := by rw [hρ₀]; exact hm2
  have hKc : IsCompact (Metric.closedBall x₁ ρ₀) := isCompact_closedBall x₁ ρ₀
  have hAK : ∀ x ∈ Metric.closedBall x₁ ρ₀, ContDiffAt ℝ 2 A x := fun x hx =>
    hε₁sub x (Metric.closedBall_subset_ball hρ₀ε hx)
  have hellK : ∀ x ∈ Metric.closedBall x₁ ρ₀, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ := fun x hx =>
    hell x (Metric.closedBall_subset_ball hρ₀δ hx)
  have hWK : ∀ x ∈ Metric.closedBall x₁ ρ₀, ContDiffAt ℝ 2 (Wfun A x₁ y) x := fun x hx =>
    (hAK x hx).clm_apply (contDiff_pvec x₁ y).contDiffAt
  have hkK : ∀ x ∈ Metric.closedBall x₁ ρ₀, ContDiffAt ℝ 2 (kfun A x₁ y) x := fun x hx =>
    (hWK x hx).inner ℝ (contDiff_pvec x₁ y).contDiffAt
  obtain ⟨Λ₀, hΛ₀⟩ := hKc.exists_bound_of_continuousOn (f := A)
    (fun x hx => (hAK x hx).continuousAt.continuousWithinAt)
  obtain ⟨Λ₁₀, hΛ₁₀⟩ := hKc.exists_bound_of_continuousOn (f := fderiv ℝ A)
    (fun x hx => ((hAK x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  obtain ⟨Kk₀, hKk₀⟩ := hKc.exists_bound_of_continuousOn (f := fderiv ℝ (kfun A x₁ y))
    (fun x hx => ((hkK x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  obtain ⟨KW₀, hKW₀⟩ := hKc.exists_bound_of_continuousOn (f := fderiv ℝ (Wfun A x₁ y))
    (fun x hx => ((hWK x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  obtain ⟨Λ, hΛ⟩ : ∃ c : ℝ, c = max Λ₀ 0 := ⟨_, rfl⟩
  obtain ⟨Λ₁, hΛ₁⟩ : ∃ c : ℝ, c = max Λ₁₀ 0 := ⟨_, rfl⟩
  obtain ⟨Kk, hKk⟩ : ∃ c : ℝ, c = max Kk₀ 0 := ⟨_, rfl⟩
  obtain ⟨KW, hKW⟩ : ∃ c : ℝ, c = max KW₀ 0 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact le_max_right _ _
  have hΛ₁0 : 0 ≤ Λ₁ := by rw [hΛ₁]; exact le_max_right _ _
  have hKk0 : 0 ≤ Kk := by rw [hKk]; exact le_max_right _ _
  have hKW0 : 0 ≤ KW := by rw [hKW]; exact le_max_right _ _
  have hΛb : ∀ x ∈ Metric.closedBall x₁ ρ₀, ‖A x‖ ≤ Λ := fun x hx => by
    rw [hΛ]; exact (hΛ₀ x hx).trans (le_max_left _ _)
  have hΛ₁b : ∀ x ∈ Metric.closedBall x₁ ρ₀, ‖fderiv ℝ A x‖ ≤ Λ₁ := fun x hx => by
    rw [hΛ₁]; exact (hΛ₁₀ x hx).trans (le_max_left _ _)
  have hKkb : ∀ x ∈ Metric.closedBall x₁ ρ₀, ‖fderiv ℝ (kfun A x₁ y) x‖ ≤ Kk := fun x hx => by
    rw [hKk]; exact (hKk₀ x hx).trans (le_max_left _ _)
  have hKWb : ∀ x ∈ Metric.closedBall x₁ ρ₀, ‖fderiv ℝ (Wfun A x₁ y) x‖ ≤ KW := fun x hx => by
    rw [hKW]; exact (hKW₀ x hx).trans (le_max_left _ _)
  obtain ⟨β, hβ⟩ : ∃ c : ℝ, c = 8 * (KW * Λ) + 4 * (Λ₁ * (Λ * (3 * r))) + 1 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by
    rw [hβ]
    have h1 : 0 ≤ KW * Λ := mul_nonneg hKW0 hΛ0
    have h2 : 0 ≤ Λ₁ * (Λ * (3 * r)) := mul_nonneg hΛ₁0 (mul_nonneg hΛ0 (by linarith))
    linarith
  have hnum : 0 < 288 * β * Λ * r ^ 2 + Kk * (Λ * (3 * r)) * lam + 1 := by
    have h1 : 0 ≤ 288 * β * Λ * r ^ 2 := by positivity
    have h2 : 0 ≤ Kk * (Λ * (3 * r)) * lam :=
      mul_nonneg (mul_nonneg hKk0 (mul_nonneg hΛ0 (by linarith))) hlam.le
    linarith
  obtain ⟨μ, hμdef⟩ : ∃ c : ℝ,
      c = (288 * β * Λ * r ^ 2 + Kk * (Λ * (3 * r)) * lam + 1) / (2 * lam ^ 3 * r ^ 4) :=
    ⟨_, rfl⟩
  have hμ : 0 < μ := by rw [hμdef]; positivity
  have hμeq : 2 * μ * lam ^ 3 * r ^ 4 = 288 * β * Λ * r ^ 2 + Kk * (Λ * (3 * r)) * lam + 1 := by
    rw [hμdef]; field_simp
  have hBl : (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))) * lam = 288 * β * Λ * r ^ 2 + 1 := by
    linear_combination hμeq
  have hB : 0 < 2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r)) := by
    have h1 : 0 < (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))) * lam := by
      rw [hBl]; positivity
    exact pos_of_mul_pos_left h1 hlam.le
  -- the bound for `∇ div V`
  have hV2K : ∀ x ∈ Metric.closedBall x₁ ρ₀, ContDiffAt ℝ 2 (carlV A (phi μ x₁ y)) x :=
    fun x hx => (hAK x hx).clm_apply
      (F2.contDiffAt_gradient (contDiff_phi μ x₁ y (k := 3)).contDiffAt (by norm_num))
  have hdVK : ∀ x ∈ Metric.closedBall x₁ ρ₀,
      ContDiffAt ℝ 1 (fun z => divergence (carlV A (phi μ x₁ y)) z) x := fun x hx =>
    (F2.traceCLM (n := n)).contDiff.contDiffAt.comp x ((hV2K x hx).fderiv_right (m := 1) le_rfl)
  obtain ⟨D₀, hD₀⟩ := hKc.exists_bound_of_continuousOn
    (f := gradient (fun z => divergence (carlV A (phi μ x₁ y)) z))
    (fun x hx => (F2.contDiffAt_gradient (hdVK x hx) (m := 0) (by norm_num)).continuousAt
      |>.continuousWithinAt)
  obtain ⟨D₃, hD₃⟩ : ∃ c : ℝ, c = max D₀ 0 := ⟨_, rfl⟩
  have hD₃0 : 0 ≤ D₃ := by rw [hD₃]; exact le_max_right _ _
  have hD₃b : ∀ x ∈ Metric.closedBall x₁ ρ₀,
      ‖gradient (fun z => divergence (carlV A (phi μ x₁ y)) z) x‖ ≤ D₃ := fun x hx => by
    rw [hD₃]; exact (hD₀ x hx).trans (le_max_left _ _)
  -- the final radius
  obtain ⟨ρ, hρdef⟩ : ∃ c : ℝ, c = min ρ₀ (1 / (8 * μ * r)) := ⟨_, rfl⟩
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hρ₀pos (by positivity)
  have hρρ₀ : ρ ≤ ρ₀ := by rw [hρdef]; exact min_le_left _ _
  have hρμ : μ * (4 * r * ρ) ≤ 1 / 2 := by
    have h1 : ρ ≤ 1 / (8 * μ * r) := by rw [hρdef]; exact min_le_right _ _
    have h2 : ρ * (8 * μ * r) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at h1; exact h1
    linarith
  have hKρ : Metric.closedBall x₁ ρ ⊆ Metric.closedBall x₁ ρ₀ :=
    Metric.closedBall_subset_closedBall hρρ₀
  have hφb : ∀ x ∈ Metric.closedBall x₁ ρ, 1 / 2 ≤ phi μ x₁ y x ∧ phi μ x₁ y x ≤ 2 := by
    intro x hx
    have hd : dist x x₁ ≤ ρ := Metric.mem_closedBall.mp hx
    have hρr : ρ ≤ r / 4 := hρρ₀.trans hρ₀r
    have hlo := le_psi_of_near (y := y) hρpos.le hd
    have hhi := psi_le_of_near (y := y) (by rw [← hr]; linarith) hd
    rw [← hr] at hlo hhi
    have h2 : 2 * ρ ^ 2 ≤ 2 * r * ρ := by
      have := mul_le_mul_of_nonneg_left (show ρ ≤ r by linarith) hρpos.le
      linarith
    have hrρ : 0 ≤ r * ρ := by positivity
    have h3 : -(4 * r * ρ) ≤ psi x₁ y x := by linarith
    have h5 : psi x₁ y x ≤ 4 * r * ρ := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hμ.le
    have h6 := mul_le_mul_of_nonneg_left h5 hμ.le
    have hψ1 : -(1 / 2) ≤ μ * psi x₁ y x := by linarith
    have hψ2 : μ * psi x₁ y x ≤ 1 / 2 := by linarith
    have e1 : 1 / 2 ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2)); linarith
    constructor
    · exact e1.trans (Real.exp_le_exp.mpr hψ1)
    · have e2 : Real.exp (1 / 2) ≤ 2 := by
        have h3 : Real.exp (1 / 2) = (Real.exp (-(1 / 2)))⁻¹ := by
          rw [← Real.exp_neg, neg_neg]
        rw [h3, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        linarith
      exact (Real.exp_le_exp.mpr hψ2).trans e2
  refine ⟨μ, hμ, ρ, hρpos, lam, hlam, 2 * μ * (2 * μ) * (Λ * (3 * r) ^ 2), by positivity,
    μ ^ 3 / 4 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))), by positivity,
    μ * β, by positivity, Λ ^ 2 * D₃ ^ 2 / μ, by positivity, ?_,
    fun x hx => hAK x (hKρ hx), fun x hx => hellK x (hKρ hx), ?_, ?_⟩
  · -- the condition `2 bJ Q ≤ cJ λ`
    have e : μ ^ 3 / 4 * (2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))) * lam
        = μ ^ 3 / 4 * ((2 * μ * lam ^ 2 * r ^ 4 - Kk * (Λ * (3 * r))) * lam) := by ring
    rw [e, hBl]
    have h3 : 0 ≤ μ ^ 3 := by positivity
    linarith
  · -- the bound for `q`
    intro x hx
    have hxK := hKρ hx
    obtain ⟨hp0, hp1⟩ := norm_pvec_bounds (x₁ := x₁) (y := y) (x := x)
      (hρρ₀.trans (hr ▸ hρ₀r)) (Metric.mem_closedBall.mp hx)
    rw [← hr] at hp0 hp1
    rw [carlQ_phi]
    dsimp only
    have hM0 : 0 ≤ μ * phi μ x₁ y x := mul_nonneg hμ.le (Real.exp_pos _).le
    have hM2 : μ * phi μ x₁ y x ≤ 2 * μ := by
      have := mul_le_mul_of_nonneg_left (hφb x hx).2 hμ.le; linarith
    have hk0 : 0 ≤ kfun A x₁ y x := by
      have := hellK x hxK (pvec x₁ y x)
      have h0 : 0 ≤ lam * ‖pvec x₁ y x‖ ^ 2 := by positivity
      unfold kfun; linarith
    have hk1 : kfun A x₁ y x ≤ Λ * (3 * r) ^ 2 := by
      unfold kfun
      calc ⟪A x (pvec x₁ y x), pvec x₁ y x⟫_ℝ ≤ ‖A x (pvec x₁ y x)‖ * ‖pvec x₁ y x‖ :=
            real_inner_le_norm _ _
        _ ≤ (‖A x‖ * ‖pvec x₁ y x‖) * ‖pvec x₁ y x‖ :=
            mul_le_mul_of_nonneg_right ((A x).le_opNorm _) (norm_nonneg _)
        _ ≤ (Λ * (3 * r)) * (3 * r) := by
            gcongr
            exact hΛb x hxK
        _ = Λ * (3 * r) ^ 2 := by ring
    exact mul_le_mul (mul_le_mul hM2 hM2 hM0 (by positivity)) hk1 hk0 (by positivity)
  · -- the bound for `carlJ`
    intro x hx τ hτ u _
    have hxK := hKρ hx
    obtain ⟨hp0, hp1⟩ := norm_pvec_bounds (x₁ := x₁) (y := y) (x := x)
      (hρρ₀.trans (hr ▸ hρ₀r)) (Metric.mem_closedBall.mp hx)
    rw [← hr] at hp0 hp1
    have h := carlJ_pointwise A x₁ y μ hμ x ((hAK x hxK).differentiableAt (by norm_num))
      (hsymm x) lam Λ Λ₁ Kk KW D₃ r hlam hr0 (hφb x hx).1 (hφb x hx).2 (hellK x hxK)
      (hΛb x hxK) (hΛ₁b x hxK) (hKkb x hxK) (hKWb x hxK) (hD₃b x hxK) hp0 hp1 hB.le τ hτ u
    rw [hβ]
    linarith

/-! #### Integration -/

theorem continuous_of_local {E : Type*} [TopologicalSpace E] [Zero E] {u : Space n → ℝ}
    {W : Set (Space n)} (hsupp : tsupport u ⊆ W) {f : Space n → E}
    (hcont : ∀ x ∈ W, ContinuousAt f x) (hzero : ∀ x, x ∉ tsupport u → f x = 0) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ W
  · exact hcont x hx
  · have hxt : x ∉ tsupport u := fun h => hx (hsupp h)
    have h0 : (fun _ => (0 : E)) =ᶠ[𝓝 x] f := by
      filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hxt] with z hz
      exact (hzero z hz).symm
    exact continuousAt_const.congr h0

theorem hasCompactSupport_of_local {E : Type*} [Zero E] {u : Space n → ℝ}
    (hcs : HasCompactSupport u) {f : Space n → E} (hzero : ∀ x, x ∉ tsupport u → f x = 0) :
    HasCompactSupport f :=
  hcs.mono' fun x hx => by
    by_contra h
    exact hx (hzero x h)

theorem integrable_of_local {u : Space n → ℝ} (hcs : HasCompactSupport u) {W : Set (Space n)}
    (hsupp : tsupport u ⊆ W) {f : Space n → ℝ} (hcont : ∀ x ∈ W, ContinuousAt f x)
    (hzero : ∀ x, x ∉ tsupport u → f x = 0) : Integrable f :=
  (continuous_of_local hsupp hcont hzero).integrable_of_hasCompactSupport
    (hasCompactSupport_of_local hcs hzero)

theorem contDiff_of_local {u : Space n → ℝ} {W : Set (Space n)} (hsupp : tsupport u ⊆ W)
    {F : Space n → Space n} (hcd : ∀ x ∈ W, ContDiffAt ℝ 1 F x)
    (hzero : ∀ x, x ∉ tsupport u → F x = 0) : ContDiff ℝ 1 F := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ W
  · exact hcd x hx
  · have hxt : x ∉ tsupport u := fun h => hx (hsupp h)
    have h0 : F =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hxt] with z hz
      exact hzero z hz
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- If `u` vanishes outside its topological support, so does the divergence of any field that
vanishes there. -/
theorem divergence_eq_zero_of_local {u : Space n → ℝ} {F : Space n → Space n}
    (hzero : ∀ x, x ∉ tsupport u → F x = 0) {x : Space n} (hx : x ∉ tsupport u) :
    divergence F x = 0 := by
  have h0 : F =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with z hz
    exact hzero z hz
  rw [F2.divergence_congr h0]
  simp [divergence]

theorem integral_divergence_eq_zero_of_local {u : Space n → ℝ} (hcs : HasCompactSupport u)
    {W : Set (Space n)} (hsupp : tsupport u ⊆ W) {F : Space n → Space n}
    (hcd : ∀ x ∈ W, ContDiffAt ℝ 1 F x) (hzero : ∀ x, x ∉ tsupport u → F x = 0) :
    ∫ x, divergence F x = 0 :=
  integral_divergence_eq_zero F (contDiff_of_local hsupp hcd hzero)
    (hasCompactSupport_of_local hcs hzero)

theorem integrable_divergence_of_local {u : Space n → ℝ} (hcs : HasCompactSupport u)
    {W : Set (Space n)} (hsupp : tsupport u ⊆ W) {F : Space n → Space n}
    (hcd : ∀ x ∈ W, ContDiffAt ℝ 1 F x) (hzero : ∀ x, x ∉ tsupport u → F x = 0) :
    Integrable (fun x => divergence F x) := by
  have hF := contDiff_of_local hsupp hcd hzero
  have hFc : HasCompactSupport F := hasCompactSupport_of_local hcs hzero
  exact ((F2.traceCLM (n := n)).continuous.comp (hF.continuous_fderiv one_ne_zero))
    |>.integrable_of_hasCompactSupport ((hFc.fderiv ℝ).comp_left (map_zero _))

/-- The integrated identities of Lemma 2.1 (2), (3) with density `1`, for compactly supported `u`,
together with the integrability of all terms. -/
theorem integral_identities (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ) (τ : ℝ)
    (W : Set (Space n)) (_hW : IsOpen W) (hA : ∀ x ∈ W, ContDiffAt ℝ 2 A x)
    (hsymm : ∀ x ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ) (hφ : ContDiff ℝ 3 φ)
    (u : Space n → ℝ) (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) (hsupp : tsupport u ⊆ W) :
    Integrable (fun x => carlS (fun _ => 1) A φ τ u x ^ 2) ∧
    Integrable (fun x => carlT (fun _ => 1) A φ τ u x ^ 2) ∧
    Integrable (fun x => carlS (fun _ => 1) A φ τ u x * carlT (fun _ => 1) A φ τ u x) ∧
    Integrable (fun x => carlS (fun _ => 1) A φ τ u x * u x) ∧
    Integrable (carlJ (fun _ => 1) A φ τ u) ∧
    Integrable (fun x => carlQ A φ x * u x ^ 2) ∧
    Integrable (fun x => ⟪A x (gradient u x), gradient u x⟫_ℝ) ∧
    ∫ x, 2 * carlS (fun _ => 1) A φ τ u x * carlT (fun _ => 1) A φ τ u x
      = ∫ x, carlJ (fun _ => 1) A φ τ u x ∧
    ∫ x, ⟪A x (gradient u x), gradient u x⟫_ℝ
      = -(∫ x, carlS (fun _ => 1) A φ τ u x * u x) + τ ^ 2 * ∫ x, carlQ A φ x * u x ^ 2 := by
  have hu_out : ∀ x, x ∉ tsupport u → u =ᶠ[𝓝 x] fun _ => 0 := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hgu1 : ContDiff ℝ 1 (gradient u) := contDiff_gradient hu
  -- regularity at points of `W`
  have hgφ2 : ∀ x, ContDiffAt ℝ 2 (gradient φ) x := fun x =>
    F2.contDiffAt_gradient hφ.contDiffAt (by norm_num)
  have hV2 : ∀ x ∈ W, ContDiffAt ℝ 2 (carlV A φ) x := fun x hx =>
    (hA x hx).clm_apply (hgφ2 x)
  have hq2 : ∀ x ∈ W, ContDiffAt ℝ 2 (carlQ A φ) x := fun x hx =>
    ((hA x hx).clm_apply (hgφ2 x)).inner ℝ (hgφ2 x)
  have hdV1 : ∀ x ∈ W, ContDiffAt ℝ 1 (fun y => divergence (carlV A φ) y) x := fun x hx =>
    (F2.traceCLM (n := n)).contDiff.contDiffAt.comp x ((hV2 x hx).fderiv_right (m := 1) le_rfl)
  have hAgu : ∀ x ∈ W, ContDiffAt ℝ 1 (fun y => A y (gradient u y)) x := fun x hx =>
    ((hA x hx).of_le (by norm_num)).clm_apply hgu1.contDiffAt
  have hdivAgu : ∀ x ∈ W, ContinuousAt (fun y => divergence (fun z => A z (gradient u z)) y) x :=
    fun x hx => (F2.traceCLM (n := n)).continuous.continuousAt.comp
      ((hAgu x hx).continuousAt_fderiv one_ne_zero)
  -- continuity of `S`, `T`, `J`
  have hSc : ∀ x ∈ W, ContinuousAt (carlS (fun _ => 1) A φ τ u) x := by
    intro x hx
    rw [carlS_one_eq]
    exact (hdivAgu x hx).add ((continuousAt_const.mul (hq2 x hx).continuousAt).mul
      hu.continuous.continuousAt)
  have hTc : ∀ x ∈ W, ContinuousAt (carlT (fun _ => 1) A φ τ u) x := by
    intro x hx
    rw [carlT_one_eq]
    exact (continuousAt_const.mul ((hV2 x hx).continuousAt.inner hgu1.continuous.continuousAt)).sub
      ((continuousAt_const.mul (hdV1 x hx).continuousAt).mul hu.continuous.continuousAt)
  have hJc : ∀ x ∈ W, ContinuousAt (carlJ (fun _ => 1) A φ τ u) x := by
    intro x hx
    rw [carlJ_one_eq]
    have hgq : ContinuousAt (gradient (carlQ A φ)) x :=
      (F2.contDiffAt_gradient (hq2 x hx) (m := 1) (by norm_num)).continuousAt
    have hgdV : ContinuousAt (gradient (fun z => divergence (carlV A φ) z)) x :=
      (F2.contDiffAt_gradient (hdV1 x hx) (m := 0) (by norm_num)).continuousAt
    have hdV : ContinuousAt (fderiv ℝ (carlV A φ)) x :=
      (hV2 x hx).continuousAt_fderiv (by norm_num)
    have hdA : ContinuousAt (fderiv ℝ A) x := (hA x hx).continuousAt_fderiv (by norm_num)
    have hVc : ContinuousAt (carlV A φ) x := (hV2 x hx).continuousAt
    have hguc : ContinuousAt (gradient u) x := hgu1.continuous.continuousAt
    have huc : ContinuousAt u x := hu.continuous.continuousAt
    have hAguc : ContinuousAt (fun y => A y (gradient u y)) x := (hAgu x hx).continuousAt
    refine (((?_ : ContinuousAt _ x).add ?_).sub ?_).add ?_
    · exact (continuousAt_const.mul (hVc.inner hgq)).mul (huc.pow 2)
    · exact continuousAt_const.mul ((hdV.clm_apply hAguc).inner hguc)
    · exact continuousAt_const.mul (((hdA.clm_apply hVc).clm_apply hguc).inner hguc)
    · exact (continuousAt_const.mul huc).mul (hAguc.inner hgdV)
  -- vanishing outside the support
  have hS0 : ∀ x, x ∉ tsupport u → carlS (fun _ => 1) A φ τ u x = 0 := fun x hx =>
    carlS_eq_zero A φ τ (hu_out x hx)
  have hT0 : ∀ x, x ∉ tsupport u → carlT (fun _ => 1) A φ τ u x = 0 := fun x hx =>
    carlT_eq_zero A φ τ (hu_out x hx)
  have hJ0 : ∀ x, x ∉ tsupport u → carlJ (fun _ => 1) A φ τ u x = 0 := fun x hx =>
    carlJ_eq_zero A φ τ (hu_out x hx)
  have hux0 : ∀ x, x ∉ tsupport u → u x = 0 := fun x hx => (hu_out x hx).eq_of_nhds
  have hgux0 : ∀ x, x ∉ tsupport u → gradient u x = 0 := fun x hx =>
    gradient_eq_zero_of_eventuallyEq (hu_out x hx)
  -- integrability
  have iS2 : Integrable (fun x => carlS (fun _ => 1) A φ τ u x ^ 2) :=
    integrable_of_local hcs hsupp (fun x hx => (hSc x hx).pow 2)
      (fun x hx => by simp [hS0 x hx])
  have iT2 : Integrable (fun x => carlT (fun _ => 1) A φ τ u x ^ 2) :=
    integrable_of_local hcs hsupp (fun x hx => (hTc x hx).pow 2)
      (fun x hx => by simp [hT0 x hx])
  have iST : Integrable (fun x => carlS (fun _ => 1) A φ τ u x * carlT (fun _ => 1) A φ τ u x) :=
    integrable_of_local hcs hsupp (fun x hx => (hSc x hx).mul (hTc x hx))
      (fun x hx => by simp [hS0 x hx])
  have iSu : Integrable (fun x => carlS (fun _ => 1) A φ τ u x * u x) :=
    integrable_of_local hcs hsupp (fun x hx => (hSc x hx).mul hu.continuous.continuousAt)
      (fun x hx => by simp [hS0 x hx])
  have iJ : Integrable (carlJ (fun _ => 1) A φ τ u) :=
    integrable_of_local hcs hsupp hJc hJ0
  have iq : Integrable (fun x => carlQ A φ x * u x ^ 2) :=
    integrable_of_local hcs hsupp
      (fun x hx => (hq2 x hx).continuousAt.mul (hu.continuous.continuousAt.pow 2))
      (fun x hx => by simp [hux0 x hx])
  have iAg : Integrable (fun x => ⟪A x (gradient u x), gradient u x⟫_ℝ) :=
    integrable_of_local hcs hsupp
      (fun x hx => (hAgu x hx).continuousAt.inner hgu1.continuous.continuousAt)
      (fun x hx => by simp [hgux0 x hx])
  refine ⟨iS2, iT2, iST, iSu, iJ, iq, iAg, ?_, ?_⟩
  · -- `∫ 2 S T = ∫ J`
    have hflux0 : ∀ x, x ∉ tsupport u → carlFlux (fun _ => 1) A φ τ u x = 0 := by
      intro x hx
      simp only [carlFlux, hux0 x hx, hgux0 x hx]
      simp
    have hfluxC : ∀ x ∈ W, ContDiffAt ℝ 1 (carlFlux (fun _ => 1) A φ τ u) x := by
      intro x hx
      have hV1 : ContDiffAt ℝ 1 (carlV A φ) x := (hV2 x hx).of_le (by norm_num)
      have hq1 : ContDiffAt ℝ 1 (carlQ A φ) x := (hq2 x hx).of_le (by norm_num)
      have hdV : ContDiffAt ℝ 1 (divMu (fun _ => (1 : ℝ)) (carlV A φ)) x := by
        rw [divMu_one_fun]; exact hdV1 x hx
      have hu1 : ContDiffAt ℝ 1 u x := hu.contDiffAt.of_le (by norm_num)
      have hgu : ContDiffAt ℝ 1 (gradient u) x := hgu1.contDiffAt
      have hfl : carlFlux (fun _ => 1) A φ τ u = fun y =>
          (-4 * τ * ⟪carlV A φ y, gradient u y⟫_ℝ) • A y (gradient u y)
          + (2 * τ * ⟪A y (gradient u y), gradient u y⟫_ℝ) • carlV A φ y
          - (2 * τ * divMu (fun _ => (1 : ℝ)) (carlV A φ) y * u y) • A y (gradient u y)
          - (2 * τ ^ 3 * carlQ A φ y * u y ^ 2) • carlV A φ y := by
        funext y
        simp only [carlFlux, one_smul]
      rw [hfl]
      exact ((((contDiffAt_const.mul (hV1.inner ℝ hgu)).smul (hAgu x hx)).add
          ((contDiffAt_const.mul ((hAgu x hx).inner ℝ hgu)).smul hV1)).sub
          (((contDiffAt_const.mul hdV).mul hu1).smul (hAgu x hx))).sub
          (((contDiffAt_const.mul hq1).mul (hu1.pow 2)).smul hV1)
    have hpt : ∀ x, 2 * carlS (fun _ => 1) A φ τ u x * carlT (fun _ => 1) A φ τ u x
        = carlJ (fun _ => 1) A φ τ u x + divergence (carlFlux (fun _ => 1) A φ τ u) x := by
      intro x
      by_cases hx : x ∈ W
      · have h := carleman_pointwise (fun _ => (1 : ℝ)) A φ τ u x contDiffAt_const one_ne_zero
          (hA x hx) hsymm hφ.contDiffAt hu.contDiffAt
        simpa using h
      · have hxt : x ∉ tsupport u := fun h => hx (hsupp h)
        rw [hS0 x hxt, hJ0 x hxt, divergence_eq_zero_of_local hflux0 hxt]
        ring
    have idiv := integrable_divergence_of_local hcs hsupp hfluxC hflux0
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add iJ idiv,
      integral_divergence_eq_zero_of_local hcs hsupp hfluxC hflux0, add_zero]
  · -- the gradient identity
    set G : Space n → Space n := fun y => u y • A y (gradient u y) with hG
    have hG0 : ∀ x, x ∉ tsupport u → G x = 0 := by
      intro x hx
      simp [hG, hux0 x hx]
    have hGC : ∀ x ∈ W, ContDiffAt ℝ 1 G x := fun x hx =>
      (hu.contDiffAt.of_le (by norm_num)).smul (hAgu x hx)
    have hpt : ∀ x, ⟪A x (gradient u x), gradient u x⟫_ℝ
        = -(carlS (fun _ => 1) A φ τ u x * u x) + τ ^ 2 * (carlQ A φ x * u x ^ 2)
          + divergence G x := by
      intro x
      by_cases hx : x ∈ W
      · have h := carleman_gradient_pointwise (fun _ => (1 : ℝ)) A φ τ u (fun _ => (1 : ℝ)) x
          contDiffAt_const one_ne_zero ((hA x hx).of_le (by norm_num)) hu.contDiffAt
          contDiffAt_const
        have hG' : (fun y => ((fun _ => (1 : ℝ)) y * (fun _ => (1 : ℝ)) y * u y)
            • A y (gradient u y)) = G := by
          funext y
          simp [hG]
        rw [hG', gradient_fun_const] at h
        simp only [one_mul, mul_one, inner_zero_right, mul_zero, sub_zero] at h
        rw [h]
        ring
      · have hxt : x ∉ tsupport u := fun h => hx (hsupp h)
        rw [hS0 x hxt, hux0 x hxt, hgux0 x hxt, divergence_eq_zero_of_local hG0 hxt]
        simp
    have idiv := integrable_divergence_of_local hcs hsupp hGC hG0
    have i1 : Integrable (fun x => -(carlS (fun _ => 1) A φ τ u x * u x)) := iSu.neg
    have i2 : Integrable (fun x => τ ^ 2 * (carlQ A φ x * u x ^ 2)) := iq.const_mul _
    have i12 : Integrable (fun x => -(carlS (fun _ => 1) A φ τ u x * u x)
        + τ ^ 2 * (carlQ A φ x * u x ^ 2)) := i1.add i2
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add i12 idiv,
      integral_divergence_eq_zero_of_local hcs hsupp hGC hG0, add_zero, integral_add i1 i2,
      integral_neg, integral_const_mul]

/-- The Carleman estimate for the conjugated function `u = e^{τφ} w`, from the pointwise bounds. -/
theorem carleman_conjugated_of_bounds (A : Space n → Space n →L[ℝ] Space n) (φ : Space n → ℝ)
    (hφ : ContDiff ℝ 3 φ) (hsymm : ∀ x ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (x₁ : Space n) (ρ lam Q cJ bJ bJ' : ℝ) (hlam : 0 < lam) (hQ : 0 ≤ Q) (hcJ : 0 < cJ)
    (hbJ : 0 ≤ bJ) (hbJ' : 0 ≤ bJ') (hcond : 2 * bJ * Q ≤ cJ * lam)
    (hA : ∀ x ∈ Metric.closedBall x₁ ρ, ContDiffAt ℝ 2 A x)
    (hell : ∀ x ∈ Metric.closedBall x₁ ρ, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    (hq : ∀ x ∈ Metric.closedBall x₁ ρ, carlQ A φ x ≤ Q)
    (hJ : ∀ x ∈ Metric.closedBall x₁ ρ, ∀ τ : ℝ, 0 ≤ τ → ∀ u : Space n → ℝ, ContDiffAt ℝ 2 u x →
        cJ * τ ^ 3 * u x ^ 2 - bJ * τ * ‖gradient u x‖ ^ 2 - bJ' * τ * u x ^ 2
          ≤ carlJ (fun _ => 1) A φ τ u x) :
    ∃ C₁ > 0, ∃ τ₁ > 0, ∀ τ ≥ τ₁, ∀ u : Space n → ℝ, ContDiff ℝ 2 u →
      tsupport u ⊆ Metric.ball x₁ ρ →
      τ ^ 3 * (∫ x, u x ^ 2) + τ * ∫ x, ‖gradient u x‖ ^ 2
        ≤ C₁ * ∫ x, (carlS (fun _ => 1) A φ τ u x + carlT (fun _ => 1) A φ τ u x) ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = bJ * (bJ + 1) / (2 * lam ^ 2) + bJ' := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  refine ⟨4 / cJ + (1 + (2 + 4 * Q) / cJ) / lam, by positivity, max 1 (4 * k / cJ), by positivity,
    ?_⟩
  intro τ hτ u hu husupp
  have hτ1 : 1 ≤ τ := (le_max_left _ _).trans hτ
  have hτk : 4 * k / cJ ≤ τ := (le_max_right _ _).trans hτ
  have hτ0 : 0 < τ := by linarith
  have hucs : HasCompactSupport u :=
    (isCompact_closedBall x₁ ρ).of_isClosed_subset (isClosed_tsupport u)
      (husupp.trans Metric.ball_subset_closedBall)
  have hAW : ∀ x ∈ Metric.ball x₁ ρ, ContDiffAt ℝ 2 A x := fun x hx =>
    hA x (Metric.ball_subset_closedBall hx)
  obtain ⟨iS2, iT2, iST, iSu, iJ, iq, iAg, hST, hG⟩ :=
    integral_identities A φ τ (Metric.ball x₁ ρ) Metric.isOpen_ball hAW hsymm hφ u hu hucs husupp
  have hu_out : ∀ x, x ∉ Metric.closedBall x₁ ρ → u =ᶠ[𝓝 x] fun _ => 0 := by
    intro x hx
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hxt
    exact hx (Metric.ball_subset_closedBall (husupp hxt))
  have iu2 : Integrable (fun x => u x ^ 2) :=
    (hu.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hucs)
  have igu : Integrable (fun x => ‖gradient u x‖ ^ 2) :=
    ((contDiff_gradient hu).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_norm_sq (hasCompactSupport_gradient hucs))
  -- notation for the integrals
  obtain ⟨X, hX⟩ : ∃ X, X = ∫ x, u x ^ 2 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ∫ x, ‖gradient u x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = ∫ x, (carlS (fun _ => 1) A φ τ u x
      + carlT (fun _ => 1) A φ τ u x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨SS, hSS⟩ : ∃ I, I = ∫ x, carlS (fun _ => 1) A φ τ u x ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ I, I = ∫ x, carlS (fun _ => 1) A φ τ u x * u x := ⟨_, rfl⟩
  obtain ⟨Qi, hQi⟩ : ∃ I, I = ∫ x, carlQ A φ x * u x ^ 2 := ⟨_, rfl⟩
  obtain ⟨Gi, hGi⟩ : ∃ I, I = ∫ x, ⟪A x (gradient u x), gradient u x⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨JI, hJI⟩ : ∃ I, I = ∫ x, carlJ (fun _ => 1) A φ τ u x := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact integral_nonneg fun x => sq_nonneg _
  have hY0 : 0 ≤ Y := by rw [hY]; exact integral_nonneg fun x => sq_nonneg _
  have hSS0 : 0 ≤ SS := by rw [hSS]; exact integral_nonneg fun x => sq_nonneg _
  -- (1) `P ≥ SS + JI`
  have i2 : Integrable (fun x => 2 * carlS (fun _ => 1) A φ τ u x
      * carlT (fun _ => 1) A φ τ u x) := by
    have := iST.const_mul 2
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have h1 : SS + JI ≤ P := by
    have e : ∫ x, (carlS (fun _ => 1) A φ τ u x ^ 2
        + 2 * carlS (fun _ => 1) A φ τ u x * carlT (fun _ => 1) A φ τ u x) = SS + JI := by
      rw [integral_add iS2 i2, hST, hSS, hJI]
    have iP : Integrable (fun x => (carlS (fun _ => 1) A φ τ u x
        + carlT (fun _ => 1) A φ τ u x) ^ 2) := by
      have := (iS2.add (iST.const_mul 2)).add iT2
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]
      ring
    rw [← e, hP]
    refine integral_mono (iS2.add i2) iP fun x => ?_
    simp only
    linarith [sq_nonneg (carlT (fun _ => 1) A φ τ u x)]
  -- (2) the lower bound for `JI`
  have h2 : cJ * τ ^ 3 * X - bJ * τ * Y - bJ' * τ * X ≤ JI := by
    have ilow : Integrable (fun x => cJ * τ ^ 3 * u x ^ 2 - bJ * τ * ‖gradient u x‖ ^ 2
        - bJ' * τ * u x ^ 2) :=
      ((iu2.const_mul _).sub (igu.const_mul _)).sub (iu2.const_mul _)
    have e : ∫ x, (cJ * τ ^ 3 * u x ^ 2 - bJ * τ * ‖gradient u x‖ ^ 2 - bJ' * τ * u x ^ 2)
        = cJ * τ ^ 3 * X - bJ * τ * Y - bJ' * τ * X := by
      have ia : Integrable (fun x => cJ * τ ^ 3 * u x ^ 2) := iu2.const_mul _
      have ib : Integrable (fun x => bJ * τ * ‖gradient u x‖ ^ 2) := igu.const_mul _
      have ic : Integrable (fun x => bJ' * τ * u x ^ 2) := iu2.const_mul _
      have iab : Integrable (fun x => cJ * τ ^ 3 * u x ^ 2 - bJ * τ * ‖gradient u x‖ ^ 2) :=
        ia.sub ib
      rw [integral_sub iab ic, integral_sub ia ib, integral_const_mul, integral_const_mul,
        integral_const_mul, hX, hY]
    rw [← e, hJI]
    refine integral_mono ilow iJ fun x => ?_
    by_cases hx : x ∈ Metric.closedBall x₁ ρ
    · exact hJ x hx τ hτ0.le u hu.contDiffAt
    · have h0 := hu_out x hx
      simp only
      rw [carlJ_eq_zero A φ τ h0, gradient_eq_zero_of_eventuallyEq h0, h0.eq_of_nhds]
      simp
  -- (3) ellipticity
  have h3 : lam * Y ≤ Gi := by
    rw [hY, hGi, ← integral_const_mul]
    refine integral_mono (igu.const_mul lam) iAg fun x => ?_
    by_cases hx : x ∈ Metric.closedBall x₁ ρ
    · exact hell x hx (gradient u x)
    · have h0 := hu_out x hx
      simp only
      rw [gradient_eq_zero_of_eventuallyEq h0]
      simp
  -- (5) Young's inequality
  have h5 : ∀ s : ℝ, 0 < s → -Z ≤ (1 / (2 * s)) * SS + (s / 2) * X := by
    intro s hs
    have e : ∫ x, ((1 / (2 * s)) * carlS (fun _ => 1) A φ τ u x ^ 2 + (s / 2) * u x ^ 2)
        = (1 / (2 * s)) * SS + (s / 2) * X := by
      rw [integral_add (iS2.const_mul _) (iu2.const_mul _), integral_const_mul,
        integral_const_mul, hSS, hX]
    rw [← e, hZ, ← integral_neg]
    refine integral_mono iSu.neg ((iS2.const_mul _).add (iu2.const_mul _)) fun x => ?_
    simp only
    have hsq : 0 ≤ (carlS (fun _ => 1) A φ τ u x + s * u x) ^ 2 / (2 * s) := by positivity
    have heq : (carlS (fun _ => 1) A φ τ u x + s * u x) ^ 2 / (2 * s)
        = (1 / (2 * s)) * carlS (fun _ => 1) A φ τ u x ^ 2 + (s / 2) * u x ^ 2
          + carlS (fun _ => 1) A φ τ u x * u x := by
      field_simp
      ring
    linarith
  -- (6) the bound for `q`
  have h6 : Qi ≤ Q * X := by
    rw [hQi, hX, ← integral_const_mul]
    refine integral_mono iq (iu2.const_mul Q) fun x => ?_
    by_cases hx : x ∈ Metric.closedBall x₁ ρ
    · exact mul_le_mul_of_nonneg_right (hq x hx) (sq_nonneg _)
    · have h0 := hu_out x hx
      simp only
      rw [h0.eq_of_nhds]
      simp
  have hGZ : Gi = -Z + τ ^ 2 * Qi := by rw [hGi, hZ, hQi]; exact hG
  -- the gradient term with `s = (bJ + 1) τ / lam`
  have hτ2 : τ ≤ τ ^ 2 := le_self_pow₀ hτ1 (by norm_num)
  have hτ23 : τ ^ 2 ≤ τ ^ 3 := pow_le_pow_right₀ hτ1 (by norm_num)
  have h6' : τ ^ 2 * Qi ≤ τ ^ 2 * (Q * X) := mul_le_mul_of_nonneg_left h6 (sq_nonneg τ)
  have hX3 : 0 ≤ τ ^ 3 * X := mul_nonneg (by positivity) hX0
  obtain ⟨s₁, hs₁def⟩ : ∃ s : ℝ, s = (bJ + 1) * τ / lam := ⟨_, rfl⟩
  have hs₁ : 0 < s₁ := by rw [hs₁def]; positivity
  have hY1 : lam * Y ≤ (1 / (2 * s₁)) * SS + (s₁ / 2) * X + τ ^ 2 * (Q * X) := by
    have := h5 s₁ hs₁
    linarith
  have hbY : bJ * τ * Y ≤ bJ / (2 * (bJ + 1)) * SS + bJ * (bJ + 1) / (2 * lam ^ 2) * (τ ^ 2 * X)
      + bJ * Q / lam * (τ ^ 3 * X) := by
    have hm : 0 ≤ bJ * τ / lam := by positivity
    have := mul_le_mul_of_nonneg_left hY1 hm
    have e1 : bJ * τ / lam * (lam * Y) = bJ * τ * Y := by field_simp
    have e2 : bJ * τ / lam * ((1 / (2 * s₁)) * SS + (s₁ / 2) * X + τ ^ 2 * (Q * X))
        = bJ / (2 * (bJ + 1)) * SS + bJ * (bJ + 1) / (2 * lam ^ 2) * (τ ^ 2 * X)
          + bJ * Q / lam * (τ ^ 3 * X) := by
      rw [hs₁def]
      field_simp
    linarith
  have hc1 : bJ / (2 * (bJ + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hc3 : bJ * Q / lam ≤ cJ / 2 := by
    rw [div_le_div_iff₀ hlam (by norm_num)]
    linarith
  have hkτ : bJ * (bJ + 1) / (2 * lam ^ 2) * (τ ^ 2 * X) + bJ' * τ * X ≤ cJ / 4 * (τ ^ 3 * X) := by
    have hk1 : bJ * (bJ + 1) / (2 * lam ^ 2) * (τ ^ 2 * X) + bJ' * τ * X ≤ k * (τ ^ 2 * X) := by
      rw [hk]
      have : bJ' * τ * X ≤ bJ' * (τ ^ 2 * X) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hτ2 hX0) hbJ'
      have e : (bJ * (bJ + 1) / (2 * lam ^ 2) + bJ') * (τ ^ 2 * X)
          = bJ * (bJ + 1) / (2 * lam ^ 2) * (τ ^ 2 * X) + bJ' * (τ ^ 2 * X) := by ring
      linarith
    have hk2 : k ≤ cJ / 4 * τ := by
      have := hτk
      rw [div_le_iff₀ hcJ] at this
      linarith
    have hk3 : k * (τ ^ 2 * X) ≤ cJ / 4 * τ * (τ ^ 2 * X) :=
      mul_le_mul_of_nonneg_right hk2 (mul_nonneg (by positivity) hX0)
    have e : cJ / 4 * τ * (τ ^ 2 * X) = cJ / 4 * (τ ^ 3 * X) := by ring
    linarith
  have hP1 : (1 / 2) * SS + cJ / 4 * (τ ^ 3 * X) ≤ P := by
    have e : cJ * τ ^ 3 * X = cJ * (τ ^ 3 * X) := by ring
    have hc1' : bJ / (2 * (bJ + 1)) * SS ≤ 1 / 2 * SS := mul_le_mul_of_nonneg_right hc1 hSS0
    have hc3' : bJ * Q / lam * (τ ^ 3 * X) ≤ cJ / 2 * (τ ^ 3 * X) :=
      mul_le_mul_of_nonneg_right hc3 hX3
    linarith
  -- the gradient term with `s = τ`
  have hY2 : τ * (lam * Y) ≤ (1 / 2) * SS + (1 / 2 + Q) * (τ ^ 3 * X) := by
    have h := h5 τ hτ0
    have hY2' : lam * Y ≤ (1 / (2 * τ)) * SS + (τ / 2) * X + τ ^ 2 * (Q * X) := by linarith
    have := mul_le_mul_of_nonneg_left hY2' hτ0.le
    have e : τ * ((1 / (2 * τ)) * SS + (τ / 2) * X + τ ^ 2 * (Q * X))
        = (1 / 2) * SS + (1 / 2) * (τ ^ 2 * X) + Q * (τ ^ 3 * X) := by
      field_simp
    have h22 : τ ^ 2 * X ≤ τ ^ 3 * X := mul_le_mul_of_nonneg_right hτ23 hX0
    linarith
  have hX4 : τ ^ 3 * X ≤ 4 / cJ * P := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcJ]
    linarith
  have hYf : τ * Y ≤ (1 + (2 + 4 * Q) / cJ) * P / lam := by
    rw [le_div_iff₀ hlam]
    have hcX : 0 ≤ cJ / 4 * (τ ^ 3 * X) := mul_nonneg (by positivity) hX3
    have hSS2 : (1 / 2) * SS ≤ P := by linarith
    have hQX : (1 / 2 + Q) * (τ ^ 3 * X) ≤ (1 / 2 + Q) * (4 / cJ * P) :=
      mul_le_mul_of_nonneg_left hX4 (by positivity)
    have e : (1 / 2 + Q) * (4 / cJ * P) = (2 + 4 * Q) / cJ * P := by
      field_simp
      ring
    linarith
  rw [← hX, ← hY, ← hP]
  have e : (4 / cJ + (1 + (2 + 4 * Q) / cJ) / lam) * P
      = 4 / cJ * P + (1 + (2 + 4 * Q) / cJ) * P / lam := by
    field_simp
  linarith

/-- **Local Carleman estimate** near `x₁` with the weight `e^{τ φ}`, `φ = e^{μ ψ}`, for a globally
symmetric `A` that is `C²` and positive definite at `x₁`. -/
theorem carleman_local (A : Space n → Space n →L[ℝ] Space n) (x₁ y : Space n) (hxy : x₁ ≠ y)
    (hA : ContDiffAt ℝ 2 A x₁) (hsymm : ∀ x ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (hpos : ∀ ξ, ξ ≠ 0 → 0 < ⟪A x₁ ξ, ξ⟫_ℝ) :
    ∃ μ > 0, ∃ ρ > 0, ∃ Cc > 0, ∃ τ₀ > 0, ∀ τ ≥ τ₀, ∀ w : Space n → ℝ, ContDiff ℝ 2 w →
      tsupport w ⊆ Metric.ball x₁ ρ →
      τ ^ 3 * (∫ x, Real.exp (2 * τ * phi μ x₁ y x) * w x ^ 2)
        + τ * ∫ x, Real.exp (2 * τ * phi μ x₁ y x) * ‖gradient w x‖ ^ 2
        ≤ Cc * ∫ x, Real.exp (2 * τ * phi μ x₁ y x) *
            divergence (fun z => A z (gradient w z)) x ^ 2 := by
  obtain ⟨μ, hμ, ρ, hρ, lam, hlam, Q, hQ, cJ, hcJ, bJ, hbJ, bJ', hbJ', hcond, hAb, hell, hq, hJ⟩ :=
    carlJ_lower_bound A x₁ y hxy hA hsymm hpos
  have hφ3 : ContDiff ℝ 3 (phi μ x₁ y) := contDiff_phi μ x₁ y
  have hφ2 : ContDiff ℝ 2 (phi μ x₁ y) := contDiff_phi μ x₁ y
  obtain ⟨C₁, hC₁, τ₁, hτ₁, hconj⟩ := carleman_conjugated_of_bounds A (phi μ x₁ y) hφ3 hsymm x₁
    ρ lam Q cJ bJ bJ' hlam hQ hcJ hbJ hbJ' hcond hAb hell hq hJ
  have hgφc : Continuous (gradient (phi μ x₁ y)) := (contDiff_gradient hφ2).continuous
  obtain ⟨G₀, hG₀⟩ := (isCompact_closedBall x₁ ρ).exists_bound_of_continuousOn hgφc.continuousOn
  set G : ℝ := max G₀ 0 with hG
  have hG0 : 0 ≤ G := le_max_right _ _
  have hGb : ∀ x ∈ Metric.closedBall x₁ ρ, ‖gradient (phi μ x₁ y) x‖ ≤ G := fun x hx =>
    (hG₀ x hx).trans (le_max_left _ _)
  refine ⟨μ, hμ, ρ, hρ, C₁ * (2 + 2 * G ^ 2), by positivity, max τ₁ 1, by positivity, ?_⟩
  intro τ hτ w hw hwsupp
  have hτ1 : τ₁ ≤ τ := (le_max_left _ _).trans hτ
  have hτ0 : 0 ≤ τ := by linarith [le_max_right τ₁ 1]
  have hwcs : HasCompactSupport w :=
    (isCompact_closedBall x₁ ρ).of_isClosed_subset (isClosed_tsupport w)
      (hwsupp.trans Metric.ball_subset_closedBall)
  obtain ⟨u, hu_def⟩ : ∃ u : Space n → ℝ, u = fun z => Real.exp (τ * phi μ x₁ y z) * w z :=
    ⟨_, rfl⟩
  have hu : ContDiff ℝ 2 u := by
    rw [hu_def]; exact ((contDiff_const.mul hφ2).exp).mul hw
  have husupp : tsupport u ⊆ Metric.ball x₁ ρ := by
    rw [hu_def]; exact tsupport_mul_subset_right.trans hwsupp
  have hucs : HasCompactSupport u := by
    rw [hu_def]; exact hwcs.mul_left
  have key := hconj τ hτ1 u hu husupp
  have hexp2 : ∀ x, Real.exp (2 * τ * phi μ x₁ y x) = Real.exp (τ * phi μ x₁ y x) ^ 2 := by
    intro x
    rw [sq, ← Real.exp_add]
    ring_nf
  -- outside the support of `w`
  have hw_out : ∀ x, x ∉ tsupport w → w =ᶠ[𝓝 x] fun _ => 0 := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hu_out : ∀ x, x ∉ tsupport w → u =ᶠ[𝓝 x] fun _ => 0 := by
    intro x hx
    filter_upwards [hw_out x hx] with z hz
    rw [hu_def]
    simp [hz]
  -- (a) the zeroth order term
  have ha : ∫ x, u x ^ 2 = ∫ x, Real.exp (2 * τ * phi μ x₁ y x) * w x ^ 2 := by
    congr 1
    funext x
    rw [hu_def, hexp2, mul_pow]
  -- (b) the right-hand side
  have hb : ∫ x, (carlS (fun _ => 1) A (phi μ x₁ y) τ u x
        + carlT (fun _ => 1) A (phi μ x₁ y) τ u x) ^ 2
      = ∫ x, Real.exp (2 * τ * phi μ x₁ y x) * divergence (fun z => A z (gradient w z)) x ^ 2 := by
    congr 1
    funext x
    by_cases hx : x ∈ tsupport w
    · have hxb : x ∈ Metric.closedBall x₁ ρ := Metric.ball_subset_closedBall (hwsupp hx)
      have hid := conj_identity A (phi μ x₁ y) τ w x ((hAb x hxb).of_le (by norm_num))
        (hsymm x) hφ2.contDiffAt hw.contDiffAt
      rw [← hu_def] at hid
      rw [← hid, hexp2, mul_pow]
    · rw [carlS_eq_zero A _ τ (hu_out x hx), carlT_eq_zero A _ τ (hu_out x hx),
        divergence_A_grad_eq_zero A (hw_out x hx)]
      simp
  -- (c) the gradient term
  have hgrad_u : ∀ x, gradient u x = Real.exp (τ * phi μ x₁ y x) • gradient w x
      + (τ * u x) • gradient (phi μ x₁ y) x := by
    intro x
    have hφd : DifferentiableAt ℝ (phi μ x₁ y) x := hφ2.differentiable (by norm_num) x
    have hwd : DifferentiableAt ℝ w x := hw.differentiable (by norm_num) x
    have hE : HasFDerivAt (fun z => Real.exp (τ * phi μ x₁ y z))
        (Real.exp (τ * phi μ x₁ y x) • (τ • fderiv ℝ (phi μ x₁ y) x)) x :=
      (hφd.hasFDerivAt.const_mul τ).exp
    have hEw : HasFDerivAt u (Real.exp (τ * phi μ x₁ y x) • fderiv ℝ w x
        + w x • (Real.exp (τ * phi μ x₁ y x) • (τ • fderiv ℝ (phi μ x₁ y) x))) x := by
      rw [hu_def]; exact hE.mul hwd.hasFDerivAt
    refine ext_inner_right ℝ fun v => ?_
    rw [inner_gradient_left, hEw.fderiv, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, inner_gradient_left, inner_gradient_left, hu_def]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hc_pt : ∀ x, Real.exp (2 * τ * phi μ x₁ y x) * ‖gradient w x‖ ^ 2
      ≤ 2 * ‖gradient u x‖ ^ 2 + 2 * τ ^ 2 * G ^ 2 * u x ^ 2 := by
    intro x
    by_cases hx : x ∈ tsupport w
    · have hxb : x ∈ Metric.closedBall x₁ ρ := Metric.ball_subset_closedBall (hwsupp hx)
      have h1 : Real.exp (τ * phi μ x₁ y x) • gradient w x
          = gradient u x - (τ * u x) • gradient (phi μ x₁ y) x := by
        rw [hgrad_u x]; abel
      have h2 : Real.exp (2 * τ * phi μ x₁ y x) * ‖gradient w x‖ ^ 2
          = ‖gradient u x - (τ * u x) • gradient (phi μ x₁ y) x‖ ^ 2 := by
        rw [← h1, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, hexp2]
      have h3 : ‖gradient u x - (τ * u x) • gradient (phi μ x₁ y) x‖
          ≤ ‖gradient u x‖ + ‖(τ * u x) • gradient (phi μ x₁ y) x‖ := norm_sub_le _ _
      have h4 : ‖(τ * u x) • gradient (phi μ x₁ y) x‖ ^ 2 ≤ τ ^ 2 * G ^ 2 * u x ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        have h5 : ‖gradient (phi μ x₁ y) x‖ ^ 2 ≤ G ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hGb x hxb) 2
        calc (τ * u x) ^ 2 * ‖gradient (phi μ x₁ y) x‖ ^ 2 ≤ (τ * u x) ^ 2 * G ^ 2 :=
              mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
          _ = τ ^ 2 * G ^ 2 * u x ^ 2 := by ring
      rw [h2]
      have h6 : ‖gradient u x - (τ * u x) • gradient (phi μ x₁ y) x‖ ^ 2
          ≤ (‖gradient u x‖ + ‖(τ * u x) • gradient (phi μ x₁ y) x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith [sq_nonneg (‖gradient u x‖ - ‖(τ * u x) • gradient (phi μ x₁ y) x‖)]
    · rw [gradient_eq_zero_of_eventuallyEq (hw_out x hx)]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
  have hguc : Continuous (gradient u) := (contDiff_gradient hu).continuous
  have hint_gu : Integrable (fun x => ‖gradient u x‖ ^ 2) :=
    (hguc.norm.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_norm_sq (hasCompactSupport_gradient hucs))
  have hint_u : Integrable (fun x => u x ^ 2) :=
    (hu.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hucs)
  have hc : ∫ x, Real.exp (2 * τ * phi μ x₁ y x) * ‖gradient w x‖ ^ 2
      ≤ 2 * (∫ x, ‖gradient u x‖ ^ 2) + 2 * τ ^ 2 * G ^ 2 * ∫ x, u x ^ 2 := by
    have hint : Integrable (fun x => 2 * ‖gradient u x‖ ^ 2 + 2 * τ ^ 2 * G ^ 2 * u x ^ 2) :=
      (hint_gu.const_mul 2).add (hint_u.const_mul _)
    calc ∫ x, Real.exp (2 * τ * phi μ x₁ y x) * ‖gradient w x‖ ^ 2
        ≤ ∫ x, (2 * ‖gradient u x‖ ^ 2 + 2 * τ ^ 2 * G ^ 2 * u x ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x =>
            mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hint (Eventually.of_forall hc_pt)
      _ = 2 * (∫ x, ‖gradient u x‖ ^ 2) + 2 * τ ^ 2 * G ^ 2 * ∫ x, u x ^ 2 := by
          rw [integral_add (hint_gu.const_mul 2) (hint_u.const_mul _), integral_const_mul,
            integral_const_mul]
  -- combine
  have hX : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hY : 0 ≤ ∫ x, ‖gradient u x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [← ha, ← hb]
  have hG2 : 0 ≤ G ^ 2 := sq_nonneg _
  calc τ ^ 3 * (∫ x, u x ^ 2) + τ * ∫ x, Real.exp (2 * τ * phi μ x₁ y x) * ‖gradient w x‖ ^ 2
      ≤ τ ^ 3 * (∫ x, u x ^ 2)
          + τ * (2 * (∫ x, ‖gradient u x‖ ^ 2) + 2 * τ ^ 2 * G ^ 2 * ∫ x, u x ^ 2) := by
        gcongr
    _ = (1 + 2 * G ^ 2) * (τ ^ 3 * ∫ x, u x ^ 2) + 2 * (τ * ∫ x, ‖gradient u x‖ ^ 2) := by ring
    _ ≤ (2 + 2 * G ^ 2) * (τ ^ 3 * (∫ x, u x ^ 2) + τ * ∫ x, ‖gradient u x‖ ^ 2) := by
        have h1 : 0 ≤ τ ^ 3 * ∫ x, u x ^ 2 := mul_nonneg (pow_nonneg hτ0 3) hX
        have h2 : 0 ≤ τ * ∫ x, ‖gradient u x‖ ^ 2 := mul_nonneg hτ0 hY
        nlinarith
    _ ≤ (2 + 2 * G ^ 2) * (C₁ * ∫ x, (carlS (fun _ => 1) A (phi μ x₁ y) τ u x
          + carlT (fun _ => 1) A (phi μ x₁ y) τ u x) ^ 2) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = C₁ * (2 + 2 * G ^ 2) * ∫ x, (carlS (fun _ => 1) A (phi μ x₁ y) τ u x
          + carlT (fun _ => 1) A (phi μ x₁ y) τ u x) ^ 2 := by ring

/-! ### From the Carleman estimate to vanishing near `x₁` -/

/-- The application of the Carleman estimate to `χ v`. -/
theorem vanish_of_carleman {U : Set (Space n)} (hU : IsOpen U)
    (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n) (C : Space n → ℝ)
    (hA : ContDiffOn ℝ 2 A U) (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (v : Space n → ℝ) (hv : ContDiffOn ℝ 2 v U) (heq : ∀ x ∈ U, ellOp A B C v x = 0)
    (x₁ y : Space n) (hx₁ : x₁ ∈ U) (hne : x₁ ≠ y)
    (hvan : ∀ᶠ x in 𝓝 x₁, dist x y < dist x₁ y → v x = 0)
    (μ : ℝ) (hμ : 0 < μ) (ρ : ℝ) (hρ : 0 < ρ) (Cc τ₀ : ℝ)
    (hcarl : ∀ τ ≥ τ₀, ∀ w : Space n → ℝ, ContDiff ℝ 2 w → tsupport w ⊆ Metric.ball x₁ ρ →
      τ ^ 3 * (∫ x, Real.exp (2 * τ * phi μ x₁ y x) * w x ^ 2)
        + τ * ∫ x, Real.exp (2 * τ * phi μ x₁ y x) * ‖gradient w x‖ ^ 2
        ≤ Cc * ∫ x, Real.exp (2 * τ * phi μ x₁ y x) *
            divergence (fun z => A z (gradient w z)) x ^ 2) :
    ∀ᶠ x in 𝓝 x₁, v x = 0 := by
  classical
  set r := dist x₁ y with hr
  have hr0 : 0 < r := dist_pos.mpr hne
  obtain ⟨ρv, hρv, hρvsub⟩ := Metric.eventually_nhds_iff_ball.mp hvan
  obtain ⟨ρU, hρU, hρUsub⟩ := Metric.isOpen_iff.mp hU x₁ hx₁
  have hmin : 0 < min (min ρ ρv) ρU := lt_min (lt_min hρ hρv) hρU
  set R : ℝ := min (min ρ ρv) ρU / 2 with hR
  have hR0 : 0 < R := half_pos hmin
  have hm1 := min_le_left (min ρ ρv) ρU
  have hm2 := min_le_right (min ρ ρv) ρU
  have hm3 := min_le_left ρ ρv
  have hm4 := min_le_right ρ ρv
  have hRρ : R < ρ := by linarith
  have hRv : R < ρv := by linarith
  have hRU : R < ρU := by linarith
  have hcbU : Metric.closedBall x₁ R ⊆ U := fun x hx =>
    hρUsub (Metric.closedBall_subset_ball hRU hx)
  let χ : ContDiffBump x₁ := ⟨R / 2, R, by linarith, by linarith⟩
  have hχt : tsupport χ = Metric.closedBall x₁ R := χ.tsupport_eq
  set w : Space n → ℝ := fun x => χ x * v x with hw_def
  have hw_out : ∀ x, x ∉ Metric.closedBall x₁ R → w =ᶠ[𝓝 x] fun _ => 0 := by
    intro x hx
    have hxt : x ∉ tsupport χ := by rw [hχt]; exact hx
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxt] with z hz
    simp [w, hz]
  have hw_in : ∀ x ∈ Metric.ball x₁ (R / 2), w =ᶠ[𝓝 x] v := by
    intro x hx
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hx] with z hz
    simp [w, hz]
  have hwC2 : ContDiff ℝ 2 w := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.closedBall x₁ R
    · exact χ.contDiffAt.mul (hv.contDiffAt (hU.mem_nhds (hcbU hx)))
    · exact contDiffAt_const.congr_of_eventuallyEq (hw_out x hx)
  have hwsupp : tsupport w ⊆ Metric.ball x₁ ρ := by
    refine tsupport_mul_subset_left.trans ?_
    rw [hχt]
    exact Metric.closedBall_subset_ball hRρ
  have hwcs : HasCompactSupport w := χ.hasCompactSupport.mul_right
  have hw_ball : ∀ x ∈ Metric.closedBall x₁ (R / 2), w x = v x := by
    intro x hx
    rw [hw_def]
    have h1 : χ x = 1 := χ.one_of_mem_closedBall hx
    simp only [h1, one_mul]
  clear_value w
  have hgw1 : ContDiff ℝ 1 (gradient w) := contDiff_gradient hwC2
  have hgwc : Continuous (gradient w) := hgw1.continuous
  -- bounds for `B`, `C` and `ellOp A B C w` on the closed ball
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall x₁ R).exists_bound_of_continuousOn (hB.mono hcbU)
  obtain ⟨K₁, hK₁⟩ := (isCompact_closedBall x₁ R).exists_bound_of_continuousOn (hC.mono hcbU)
  set K : ℝ := max (max K₀ K₁) 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hKB : ∀ x ∈ Metric.closedBall x₁ R, ‖B x‖ ≤ K := fun x hx =>
    (hK₀ x hx).trans ((le_max_left K₀ K₁).trans (le_max_left _ _))
  have hKC : ∀ x ∈ Metric.closedBall x₁ R, |C x| ≤ K := fun x hx => by
    have := hK₁ x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right K₀ K₁).trans (le_max_left _ _))
  have hg_cont : ContinuousOn (ellOp A B C w) U := by
    have hF : ContDiffOn ℝ 1 (fun z => A z (gradient w z)) U :=
      (hA.of_le (by norm_num)).clm_apply hgw1.contDiffOn
    have hdiv : ContinuousOn (fun x => divergence (fun z => A z (gradient w z)) x) U :=
      (F2.traceCLM (n := n)).continuous.comp_continuousOn
        (hF.continuousOn_fderiv_of_isOpen hU le_rfl)
    exact (hdiv.add (hB.inner hgwc.continuousOn)).add (hC.mul hwC2.continuous.continuousOn)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₁ R).exists_bound_of_continuousOn (hg_cont.mono hcbU)
  -- where `ellOp A B C w` can be nonzero
  have hg_bad : ∀ x, ellOp A B C w x ≠ 0 → R / 2 ≤ dist x x₁ ∧ r ≤ dist x y ∧ dist x x₁ ≤ R := by
    intro x hx
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      push Not at h
      apply hx
      have hxU : x ∈ U := hcbU (Metric.mem_closedBall.mpr (by linarith))
      rw [ellOp_congr_v A B C (hw_in x (Metric.mem_ball.mpr h))]
      exact heq x hxU
    · by_contra h
      push Not at h
      apply hx
      by_cases hxR : dist x x₁ ≤ R
      · have ho : IsOpen {z : Space n | dist z x₁ < ρv ∧ dist z y < r} :=
          (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
            (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
        have hwx : w =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [ho.mem_nhds ⟨by linarith, h⟩] with z hz
          rw [hw_def]
          simp [hρvsub z (Metric.mem_ball.mpr hz.1) hz.2]
        rw [ellOp_congr_v A B C hwx, ellOp_zero]
      · rw [ellOp_congr_v A B C (hw_out x (by rw [Metric.mem_closedBall]; exact hxR)), ellOp_zero]
    · by_contra h
      push Not at h
      apply hx
      rw [ellOp_congr_v A B C (hw_out x (by rw [Metric.mem_closedBall]; push Not; exact h)),
        ellOp_zero]
  -- the good ball
  set ε : ℝ := min (R / 4) (R ^ 2 / (16 * r)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hε1 : ε ≤ R / 4 := min_le_left _ _
  have hε2 : 16 * r * ε ≤ R ^ 2 := by
    have := min_le_right (R / 4) (R ^ 2 / (16 * r))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set φb : ℝ := Real.exp (μ * (-(R / 2) ^ 2)) with hφb
  have hphi_bad : ∀ x, ellOp A B C w x ≠ 0 → phi μ x₁ y x ≤ φb := by
    intro x hx
    obtain ⟨h1, h2, -⟩ := hg_bad x hx
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (psi_le_of_far (by linarith) h2 h1) hμ.le)
  have hphi_good : ∀ x ∈ Metric.closedBall x₁ ε, φb ≤ phi μ x₁ y x := by
    intro x hx
    have h := le_psi_of_near (y := y) hε0.le (Metric.mem_closedBall.mp hx)
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hμ.le)
    have : 2 * ε ^ 2 ≤ 2 * (R / 4) * ε := by nlinarith
    nlinarith
  have hball_good : Metric.closedBall x₁ ε ⊆ Metric.ball x₁ (R / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hcbε : Metric.closedBall x₁ ε ⊆ U := fun x hx =>
    hcbU (Metric.closedBall_subset_closedBall (by linarith) hx)
  have hvcont : ContinuousOn v U := hv.continuousOn
  set D : ℝ := max Cc 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  set V : ℝ := volume.real (Metric.closedBall x₁ R) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set m : ℝ := ∫ x in Metric.ball x₁ ε, v x ^ 2 with hm
  have hvint : IntegrableOn (fun x => v x ^ 2) (Metric.ball x₁ ε) :=
    ((hvcont.mono hcbε).pow 2).integrableOn_compact (isCompact_closedBall x₁ ε)
      |>.mono_set Metric.ball_subset_closedBall
  have hkey : ∀ τ ≥ max (max τ₀ 1) (6 * D * K ^ 2 + 1), τ ^ 3 * m ≤ 6 * D * M ^ 2 * V := by
    intro τ hτ
    have hτ0 : τ ≥ τ₀ := (le_max_left _ _).trans ((le_max_left _ _).trans hτ)
    have hτ1 : 1 ≤ τ := (le_max_right _ _).trans ((le_max_left _ _).trans hτ)
    have hτ2 : 6 * D * K ^ 2 + 1 ≤ τ := (le_max_right _ _).trans hτ
    have hc := hcarl τ hτ0 w hwC2 hwsupp
    set E : Space n → ℝ := fun x => Real.exp (2 * τ * phi μ x₁ y x) with hE
    have hEc : Continuous E := Real.continuous_exp.comp
      (continuous_const.mul (continuous_phi μ x₁ y))
    have hEpos : ∀ x, 0 < E x := fun x => Real.exp_pos _
    set eb : ℝ := Real.exp (2 * τ * φb) with heb
    have heb0 : 0 < eb := Real.exp_pos _
    have hint0 : Integrable (fun x => E x * w x ^ 2) :=
      (hEc.mul (hwC2.continuous.pow 2)).integrable_of_hasCompactSupport
        (hasCompactSupport_mul_left' (hasCompactSupport_sq hwcs))
    have hint1 : Integrable (fun x => E x * ‖gradient w x‖ ^ 2) :=
      (hEc.mul (hgwc.norm.pow 2)).integrable_of_hasCompactSupport
        (hasCompactSupport_mul_left' (hasCompactSupport_norm_sq (hasCompactSupport_gradient hwcs)))
    have hintB : Integrable (Set.indicator (Metric.closedBall x₁ R) (fun _ => eb * M ^ 2)) :=
      (integrableOn_const (measure_closedBall_lt_top (x := x₁) (r := R)).ne).integrable_indicator
        Metric.isClosed_closedBall.measurableSet
    -- pointwise bound for the right-hand side of the Carleman estimate
    have hpt : ∀ x, E x * divergence (fun z => A z (gradient w z)) x ^ 2
        ≤ 3 * Set.indicator (Metric.closedBall x₁ R) (fun _ => eb * M ^ 2) x
          + 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2) + 3 * K ^ 2 * (E x * w x ^ 2) := by
      intro x
      have hsplit : divergence (fun z => A z (gradient w z)) x
          = ellOp A B C w x - ⟪B x, gradient w x⟫_ℝ - C x * w x := by
        unfold ellOp; ring
      have hEx := hEpos x
      by_cases hx : x ∈ Metric.closedBall x₁ R
      · rw [Set.indicator_of_mem hx]
        have hgE : E x * ellOp A B C w x ^ 2 ≤ eb * M ^ 2 := by
          by_cases hg0 : ellOp A B C w x = 0
          · rw [hg0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
              mul_zero]; positivity
          · have h1 : E x ≤ eb := Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left (hphi_bad x hg0) (by linarith))
            have h2 : ellOp A B C w x ^ 2 ≤ M ^ 2 := by
              have := hM x hx
              rw [Real.norm_eq_abs] at this
              have h0 : 0 ≤ |ellOp A B C w x| := abs_nonneg _
              calc ellOp A B C w x ^ 2 = |ellOp A B C w x| ^ 2 := (sq_abs _).symm
                _ ≤ M ^ 2 := pow_le_pow_left₀ h0 this 2
            exact mul_le_mul h1 h2 (sq_nonneg _) heb0.le
        have hBx : ⟪B x, gradient w x⟫_ℝ ^ 2 ≤ K ^ 2 * ‖gradient w x‖ ^ 2 := by
          have h1 : |⟪B x, gradient w x⟫_ℝ| ≤ K * ‖gradient w x‖ :=
            (abs_real_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_right (hKB x hx) (norm_nonneg _))
          calc ⟪B x, gradient w x⟫_ℝ ^ 2 = |⟪B x, gradient w x⟫_ℝ| ^ 2 := (sq_abs _).symm
            _ ≤ (K * ‖gradient w x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
            _ = K ^ 2 * ‖gradient w x‖ ^ 2 := by ring
        have hCx : (C x * w x) ^ 2 ≤ K ^ 2 * w x ^ 2 := by
          have h1 : |C x * w x| ≤ K * |w x| := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hKC x hx) (abs_nonneg _)
          calc (C x * w x) ^ 2 = |C x * w x| ^ 2 := (sq_abs _).symm
            _ ≤ (K * |w x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
            _ = K ^ 2 * w x ^ 2 := by rw [mul_pow, sq_abs]
        rw [hsplit]
        have h3 : (ellOp A B C w x - ⟪B x, gradient w x⟫_ℝ - C x * w x) ^ 2
            ≤ 3 * ellOp A B C w x ^ 2 + 3 * ⟪B x, gradient w x⟫_ℝ ^ 2 + 3 * (C x * w x) ^ 2 := by
          nlinarith [sq_nonneg (ellOp A B C w x + ⟪B x, gradient w x⟫_ℝ),
            sq_nonneg (ellOp A B C w x + C x * w x),
            sq_nonneg (⟪B x, gradient w x⟫_ℝ - C x * w x)]
        calc E x * (ellOp A B C w x - ⟪B x, gradient w x⟫_ℝ - C x * w x) ^ 2
            ≤ E x * (3 * ellOp A B C w x ^ 2 + 3 * ⟪B x, gradient w x⟫_ℝ ^ 2
                + 3 * (C x * w x) ^ 2) := mul_le_mul_of_nonneg_left h3 hEx.le
          _ = 3 * (E x * ellOp A B C w x ^ 2) + 3 * (E x * ⟪B x, gradient w x⟫_ℝ ^ 2)
                + 3 * (E x * (C x * w x) ^ 2) := by ring
          _ ≤ 3 * (eb * M ^ 2) + 3 * (E x * (K ^ 2 * ‖gradient w x‖ ^ 2))
                + 3 * (E x * (K ^ 2 * w x ^ 2)) := by
              gcongr
          _ = 3 * (eb * M ^ 2) + 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2)
                + 3 * K ^ 2 * (E x * w x ^ 2) := by ring
      · rw [Set.indicator_of_notMem hx]
        have hw0 := hw_out x hx
        have hgx : gradient w x = 0 := gradient_eq_zero_of_eventuallyEq hw0
        have hwx : w x = 0 := hw0.eq_of_nhds
        have hellx : ellOp A B C w x = 0 := by rw [ellOp_congr_v A B C hw0, ellOp_zero]
        rw [hsplit, hellx, hgx, hwx]
        simp
    -- integrate the pointwise bound
    obtain ⟨I₀, hI₀⟩ : ∃ I, I = ∫ x, E x * w x ^ 2 := ⟨_, rfl⟩
    obtain ⟨I₁, hI₁⟩ : ∃ I, I = ∫ x, E x * ‖gradient w x‖ ^ 2 := ⟨_, rfl⟩
    obtain ⟨J, hJ⟩ : ∃ I, I = ∫ x, E x * divergence (fun z => A z (gradient w z)) x ^ 2 :=
      ⟨_, rfl⟩
    have hdivint : J ≤ 3 * (V * (eb * M ^ 2)) + 3 * K ^ 2 * I₁ + 3 * K ^ 2 * I₀ := by
      have h12 : Integrable (fun x => 3 * Set.indicator (Metric.closedBall x₁ R)
          (fun _ => eb * M ^ 2) x + 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2)) :=
        (hintB.const_mul 3).add (hint1.const_mul _)
      have h3 : Integrable (fun x => 3 * K ^ 2 * (E x * w x ^ 2)) := hint0.const_mul _
      have hint : Integrable (fun x => 3 * Set.indicator (Metric.closedBall x₁ R)
          (fun _ => eb * M ^ 2) x + 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2)
          + 3 * K ^ 2 * (E x * w x ^ 2)) := h12.add h3
      have e1 : ∫ x, (3 * Set.indicator (Metric.closedBall x₁ R) (fun _ => eb * M ^ 2) x
              + 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2) + 3 * K ^ 2 * (E x * w x ^ 2))
          = (∫ x, (3 * Set.indicator (Metric.closedBall x₁ R) (fun _ => eb * M ^ 2) x
              + 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2))) + ∫ x, 3 * K ^ 2 * (E x * w x ^ 2) :=
        integral_add h12 h3
      have e2 : ∫ x, (3 * Set.indicator (Metric.closedBall x₁ R) (fun _ => eb * M ^ 2) x
              + 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2))
          = (∫ x, 3 * Set.indicator (Metric.closedBall x₁ R) (fun _ => eb * M ^ 2) x)
              + ∫ x, 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2) :=
        integral_add (hintB.const_mul 3) (hint1.const_mul _)
      have e3 : ∫ x, 3 * Set.indicator (Metric.closedBall x₁ R) (fun _ => eb * M ^ 2) x
          = 3 * (V * (eb * M ^ 2)) := by
        rw [integral_const_mul, integral_indicator_const _ Metric.isClosed_closedBall.measurableSet,
          smul_eq_mul]
      have e4 : ∫ x, 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2) = 3 * K ^ 2 * I₁ := by
        rw [integral_const_mul, hI₁]
      have e5 : ∫ x, 3 * K ^ 2 * (E x * w x ^ 2) = 3 * K ^ 2 * I₀ := by
        rw [integral_const_mul, hI₀]
      rw [hJ]
      calc ∫ x, E x * divergence (fun z => A z (gradient w z)) x ^ 2
          ≤ ∫ x, (3 * Set.indicator (Metric.closedBall x₁ R) (fun _ => eb * M ^ 2) x
              + 3 * K ^ 2 * (E x * ‖gradient w x‖ ^ 2) + 3 * K ^ 2 * (E x * w x ^ 2)) :=
            integral_mono_of_nonneg (Eventually.of_forall fun x =>
              mul_nonneg (hEpos x).le (sq_nonneg _)) hint (Eventually.of_forall hpt)
        _ = 3 * (V * (eb * M ^ 2)) + 3 * K ^ 2 * I₁ + 3 * K ^ 2 * I₀ := by
            rw [e1, e2, e3, e4, e5]
    -- lower bound for the left-hand side
    have hI0 : eb * m ≤ I₀ := by
      have h1 : ∫ x in Metric.ball x₁ ε, E x * w x ^ 2 ≤ ∫ x, E x * w x ^ 2 :=
        setIntegral_le_integral hint0 (Eventually.of_forall fun x =>
          mul_nonneg (hEpos x).le (sq_nonneg _))
      have h2 : ∫ x in Metric.ball x₁ ε, eb * v x ^ 2 ≤ ∫ x in Metric.ball x₁ ε, E x * w x ^ 2 := by
        refine setIntegral_mono_on (hvint.const_mul eb) hint0.integrableOn
          measurableSet_ball fun x hx => ?_
        have hxc : x ∈ Metric.closedBall x₁ ε := Metric.ball_subset_closedBall hx
        have hwv : w x = v x := hw_ball x (Metric.closedBall_subset_closedBall (by linarith) hxc)
        rw [hwv]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hphi_good x hxc) (by linarith))
      rw [integral_const_mul] at h2
      rw [hI₀]
      linarith
    have hI0nn : 0 ≤ I₀ := by
      rw [hI₀]; exact integral_nonneg fun x => mul_nonneg (hEpos x).le (sq_nonneg _)
    have hI1nn : 0 ≤ I₁ := by
      rw [hI₁]; exact integral_nonneg fun x => mul_nonneg (hEpos x).le (sq_nonneg _)
    have hdivnn : 0 ≤ J := by
      rw [hJ]; exact integral_nonneg fun x => mul_nonneg (hEpos x).le (sq_nonneg _)
    have hc' : τ ^ 3 * I₀ + τ * I₁ ≤ Cc * J := by
      rw [hI₀, hI₁, hJ]; exact hc
    have h1 : τ ^ 3 * I₀ + τ * I₁ ≤ D * (3 * (V * (eb * M ^ 2)) + 3 * K ^ 2 * I₁
        + 3 * K ^ 2 * I₀) :=
      hc'.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hdivnn).trans
        (mul_le_mul_of_nonneg_left hdivint hD0))
    have h1' : τ ^ 3 * I₀ + τ * I₁ ≤ 3 * (D * (V * (eb * M ^ 2))) + 3 * (D * K ^ 2) * I₁
        + 3 * (D * K ^ 2) * I₀ := by
      calc τ ^ 3 * I₀ + τ * I₁ ≤ D * (3 * (V * (eb * M ^ 2)) + 3 * K ^ 2 * I₁
            + 3 * K ^ 2 * I₀) := h1
        _ = 3 * (D * (V * (eb * M ^ 2))) + 3 * (D * K ^ 2) * I₁
            + 3 * (D * K ^ 2) * I₀ := by ring
    have hDK : 0 ≤ D * K ^ 2 := mul_nonneg hD0 (sq_nonneg _)
    have hτ3 : τ ≤ τ ^ 3 := le_cube hτ1
    have h2 : 3 * (D * K ^ 2) * I₁ ≤ τ * I₁ := mul_le_mul_of_nonneg_right (by linarith) hI1nn
    have h3 : 6 * (D * K ^ 2) * I₀ ≤ τ ^ 3 * I₀ := mul_le_mul_of_nonneg_right (by linarith) hI0nn
    have h4 : τ ^ 3 * I₀ ≤ 6 * (D * (V * (eb * M ^ 2))) := by linarith
    have h5 : τ ^ 3 * (eb * m) ≤ τ ^ 3 * I₀ :=
      mul_le_mul_of_nonneg_left hI0 (by positivity)
    have h6 : eb * (τ ^ 3 * m) ≤ eb * (6 * D * M ^ 2 * V) := by
      calc eb * (τ ^ 3 * m) = τ ^ 3 * (eb * m) := by ring
        _ ≤ 6 * (D * (V * (eb * M ^ 2))) := h5.trans h4
        _ = eb * (6 * D * M ^ 2 * V) := by ring
    exact le_of_mul_le_mul_left h6 heb0
  -- conclusion: `∫_{B(x₁, ε)} v² = 0`
  have hm_nn : 0 ≤ m := setIntegral_nonneg measurableSet_ball (fun x _ => sq_nonneg _)
  have hm0 : m = 0 := by
    by_contra hne0
    have hmpos : 0 < m := lt_of_le_of_ne hm_nn (Ne.symm hne0)
    set T := max (max (max τ₀ 1) (6 * D * K ^ 2 + 1)) (6 * D * M ^ 2 * V / m + 1) with hT
    have hT1 : 1 ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hT2 : 6 * D * M ^ 2 * V / m + 1 ≤ T := le_max_right _ _
    have h := hkey T (le_max_left _ _)
    have hT3 : T ≤ T ^ 3 := le_cube hT1
    have h7 : (6 * D * M ^ 2 * V / m + 1) * m ≤ T ^ 3 * m :=
      mul_le_mul_of_nonneg_right (hT2.trans hT3) hm_nn
    rw [add_mul, div_mul_cancel₀ _ hmpos.ne'] at h7
    linarith
  have hae : (fun x => v x ^ 2) =ᵐ[volume.restrict (Metric.ball x₁ ε)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _) hvint).mp hm0
  have heqon : Set.EqOn (fun x => v x ^ 2) 0 (Metric.ball x₁ ε) :=
    Measure.eqOn_open_of_ae_eq hae Metric.isOpen_ball
      ((hvcont.mono (Metric.ball_subset_closedBall.trans hcbε)).pow 2) continuousOn_const
  filter_upwards [Metric.ball_mem_nhds x₁ hε0] with x hx
  have := heqon hx
  simpa using this

/-- **Local step.** If `v` vanishes near `x₁` inside the ball `B(y, |x₁ - y|)`, then `v` vanishes
near `x₁`. -/
theorem local_step {U : Set (Space n)} (hU : IsOpen U)
    (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n) (C : Space n → ℝ)
    (hA : ContDiffOn ℝ 2 A U) (hsymm : ∀ x ∈ U, ∀ ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (hpos : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫_ℝ)
    (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (v : Space n → ℝ) (hv : ContDiffOn ℝ 2 v U) (heq : ∀ x ∈ U, ellOp A B C v x = 0)
    (x₁ y : Space n) (hx₁ : x₁ ∈ U) (hne : x₁ ≠ y)
    (hvan : ∀ᶠ x in 𝓝 x₁, dist x y < dist x₁ y → v x = 0) :
    ∀ᶠ x in 𝓝 x₁, v x = 0 := by
  have hA' : ContDiffAt ℝ 2 (symmExt U A) x₁ :=
    (hA.contDiffAt (hU.mem_nhds hx₁)).congr_of_eventuallyEq (symmExt_eventuallyEq hU A hx₁)
  obtain ⟨μ, hμ, ρ, hρ, Cc, -, τ₀, -, hcarl⟩ := carleman_local (symmExt U A) x₁ y hne hA'
    (symmExt_symm hsymm) (by rw [symmExt_eq hx₁]; exact hpos x₁ hx₁)
  refine vanish_of_carleman hU (symmExt U A) B C (hA.congr fun x hx => symmExt_eq hx) hB hC v hv
    (fun x hx => ?_) x₁ y hx₁ hne hvan μ hμ ρ hρ Cc τ₀ hcarl
  rw [ellOp_congr_A (symmExt_eventuallyEq hU A hx)]
  exact heq x hx

/-- **Touching ball.** Limit points of `{x | v = 0 near x}` in `U` belong to it. -/
theorem closure_inter_subset {U : Set (Space n)} (hU : IsOpen U)
    (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n) (C : Space n → ℝ)
    (hA : ContDiffOn ℝ 2 A U) (hsymm : ∀ x ∈ U, ∀ ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (hpos : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫_ℝ)
    (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (v : Space n → ℝ) (hv : ContDiffOn ℝ 2 v U) (heq : ∀ x ∈ U, ellOp A B C v x = 0) :
    closure {x | ∀ᶠ z in 𝓝 x, v z = 0} ∩ U ⊆ {x | ∀ᶠ z in 𝓝 x, v z = 0} := by
  set Z : Set (Space n) := {x | ∀ᶠ z in 𝓝 x, v z = 0} with hZ
  have hZo : IsOpen Z := isOpen_setOfPred_eventually_nhds
  rintro xb ⟨hcl, hxbU⟩
  by_contra hxbZ
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU xb hxbU
  obtain ⟨y, hyZ, hyxb⟩ : ∃ y ∈ Z, dist y xb < ρ / 2 := by
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hcl (ρ / 2) (by positivity)
    exact ⟨b, hb, by rw [dist_comm]; exact hd⟩
  have hKc : IsClosed Zᶜ := hZo.isClosed_compl
  have hKne : (Zᶜ).Nonempty := ⟨xb, hxbZ⟩
  obtain ⟨x₁, hx₁K, hd⟩ := hKc.exists_infDist_eq_dist hKne y
  have hpos' : 0 < Metric.infDist y Zᶜ :=
    (hKc.notMem_iff_infDist_pos hKne).mp (by simpa using hyZ)
  have hle : Metric.infDist y Zᶜ ≤ dist y xb := Metric.infDist_le_dist_of_mem hxbZ
  have hx₁U : x₁ ∈ U := by
    apply hball
    rw [Metric.mem_ball]
    calc dist x₁ xb ≤ dist x₁ y + dist y xb := dist_triangle _ _ _
      _ < ρ := by rw [dist_comm, ← hd]; linarith
  have hne : x₁ ≠ y := by
    intro h
    rw [h, dist_self] at hd
    linarith
  have hvan : ∀ᶠ x in 𝓝 x₁, dist x y < dist x₁ y → v x = 0 := by
    refine Eventually.of_forall fun x hx => ?_
    have hxK : x ∉ Zᶜ := Metric.notMem_of_dist_lt_infDist (x := y)
      (by rw [hd, dist_comm y x₁, dist_comm y x]; exact hx)
    have hxZ : x ∈ Z := by simpa using hxK
    exact hxZ.self_of_nhds
  exact hx₁K (local_step hU A B C hA hsymm hpos hB hC v hv heq x₁ y hx₁U hne hvan)

end UCP

/-! ## Package U: weak unique continuation -/

/-- **Weak unique continuation.** A `C²` solution of `div(A ∇v) + B · ∇v + C v = 0` on a connected
open set, with `A` symmetric, `C²` and positive definite and `B`, `C` continuous, which vanishes
near one point, vanishes everywhere. -/
theorem weak_ucp {U : Set (Space n)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n) (C : Space n → ℝ)
    (hA : ContDiffOn ℝ 2 A U) (hsymm : ∀ x ∈ U, ∀ ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ)
    (hpos : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫_ℝ)
    (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (v : Space n → ℝ) (hv : ContDiffOn ℝ 2 v U) (heq : ∀ x ∈ U, ellOp A B C v x = 0)
    (x₀ : Space n) (hx₀ : x₀ ∈ U) (hloc : ∀ᶠ x in 𝓝 x₀, v x = 0) :
    ∀ x ∈ U, v x = 0 := by
  have hsub : U ⊆ {x | ∀ᶠ z in 𝓝 x, v z = 0} :=
    hconn.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨x₀, hx₀, hloc⟩
      (UCP.closure_inter_subset hU A B C hA hsymm hpos hB hC v hv heq)
  intro x hx
  exact (hsub hx).self_of_nhds

end MazyaRefinedCauchy
