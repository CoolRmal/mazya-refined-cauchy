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


/-! ### Helper calculus for package F2

Everything below lives in the namespace `MazyaRefinedCauchy.F2`. -/

namespace F2

/-- For the real space `Space n`, `toDual.symm` as a real continuous linear equivalence. -/
noncomputable def toDualSymmCLE : StrongDual ℝ (Space n) ≃L[ℝ] Space n :=
  ((toDual ℝ (Space n)).symm : StrongDual ℝ (Space n) ≃ₗᵢ⋆[ℝ] Space n).toContinuousLinearEquiv

theorem gradient_eq_comp (u : Space n → ℝ) :
    gradient u = (toDualSymmCLE (n := n)) ∘ fderiv ℝ u := rfl

theorem contDiffAt_gradient {u : Space n → ℝ} {x : Space n} {k m : ℕ∞ω}
    (hu : ContDiffAt ℝ k u x) (hmk : m + 1 ≤ k) : ContDiffAt ℝ m (gradient u) x := by
  rw [gradient_eq_comp]
  exact (toDualSymmCLE (n := n)).contDiff.contDiffAt.comp x (hu.fderiv_right hmk)

theorem differentiableAt_gradient {u : Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u x) :
    DifferentiableAt ℝ (gradient u) x :=
  (contDiffAt_gradient hu (m := 1) (by norm_num)).differentiableAt one_ne_zero

theorem hasFDerivAt_gradient {u : Space n → ℝ} {x : Space n}
    (h : DifferentiableAt ℝ (fderiv ℝ u) x) :
    HasFDerivAt (gradient u)
      ((toDualSymmCLE (n := n) : StrongDual ℝ (Space n) →L[ℝ] Space n) ∘L
        fderiv ℝ (fderiv ℝ u) x) x := by
  rw [gradient_eq_comp]
  exact (toDualSymmCLE (n := n)).hasFDerivAt.comp x h.hasFDerivAt

theorem inner_fderiv_gradient {u : Space n → ℝ} {x : Space n}
    (h : DifferentiableAt ℝ (fderiv ℝ u) x) (v v' : Space n) :
    ⟪fderiv ℝ (gradient u) x v, v'⟫_ℝ = fderiv ℝ (fderiv ℝ u) x v v' := by
  rw [(hasFDerivAt_gradient h).fderiv]
  simp [toDualSymmCLE]

/-- Symmetry of the Hessian, in the form `⟪D∇u v, v'⟫ = ⟪D∇u v', v⟫`. -/
theorem inner_fderiv_gradient_comm {u : Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u x)
    (v v' : Space n) :
    ⟪fderiv ℝ (gradient u) x v, v'⟫_ℝ = ⟪fderiv ℝ (gradient u) x v', v⟫_ℝ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [inner_fderiv_gradient hd, inner_fderiv_gradient hd, (hu.isSymmSndFDerivAt (by simp)).eq]

/-- The trace as a continuous linear functional on `Space n →L[ℝ] Space n`. -/
noncomputable def traceCLM : (Space n →L[ℝ] Space n) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Space n)) ∘ₗ (ContinuousLinearMap.coeLM ℝ))

theorem traceCLM_apply (L : Space n →L[ℝ] Space n) :
    traceCLM L = LinearMap.trace ℝ (Space n) (L : Space n →ₗ[ℝ] Space n) := rfl

theorem divergence_eq_traceCLM (F : Space n → Space n) (x : Space n) :
    divergence F x = traceCLM (fderiv ℝ F x) := rfl

theorem differentiableAt_divergence {F : Space n → Space n} {x : Space n}
    (hF : ContDiffAt ℝ 2 F x) : DifferentiableAt ℝ (fun y => divergence F y) x := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact (traceCLM (n := n)).differentiableAt.comp x h1

theorem divergence_congr {F G : Space n → Space n} {x : Space n} (h : F =ᶠ[𝓝 x] G) :
    divergence F x = divergence G x := by
  simp only [divergence, h.fderiv_eq]

theorem divergence_add {F G : Space n → Space n} {x : Space n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y + G y) x = divergence F x + divergence G x := by
  have h : fderiv ℝ (fun y => F y + G y) x = fderiv ℝ F x + fderiv ℝ G x := fderiv_add hF hG
  rw [divergence_eq_traceCLM, divergence_eq_traceCLM, divergence_eq_traceCLM, h, map_add]

theorem divergence_sub {F G : Space n → Space n} {x : Space n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y - G y) x = divergence F x - divergence G x := by
  have h : fderiv ℝ (fun y => F y - G y) x = fderiv ℝ F x - fderiv ℝ G x := fderiv_sub hF hG
  rw [divergence_eq_traceCLM, divergence_eq_traceCLM, divergence_eq_traceCLM, h, map_sub]

/-- Product rule `div (f • F) = f div F + Df(F)`. -/
theorem divergence_smul {f : Space n → ℝ} {F : Space n → Space n} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℝ F x) :
    divergence (fun y => f y • F y) x = f x * divergence F x + fderiv ℝ f x (F x) := by
  have hfd : fderiv ℝ (fun y => f y • F y) x =
      f x • fderiv ℝ F x + (fderiv ℝ f x).smulRight (F x) := fderiv_smul hf hF
  rw [divergence_eq_traceCLM, divergence_eq_traceCLM, hfd, map_add, map_smul, smul_eq_mul]
  congr 1
  rw [traceCLM_apply]
  have := LinearMap.trace_smulRight (R := ℝ) (M := Space n)
    (fderiv ℝ f x : Space n →ₗ[ℝ] ℝ) (F x)
  convert this using 2
  ext v
  simp

theorem mul_divMu {μ : Space n → ℝ} {W : Space n → Space n} {x : Space n} (hμ0 : μ x ≠ 0) :
    μ x * divMu μ W x = divergence (fun y => μ y • W y) x := by
  rw [divMu, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]

/-- The flux of Lemma 2.1(2), regrouped as `f_W • (μ W) + f_V • (μ V)`. -/
theorem carlFlux_eq (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) :
    carlFlux μ B φ τ w = fun y =>
      (-4 * τ * ⟪carlV B φ y, gradient w y⟫_ℝ - 2 * τ * divMu μ (carlV B φ) y * w y)
          • (μ y • B y (gradient w y))
        + (2 * τ * ⟪B y (gradient w y), gradient w y⟫_ℝ - 2 * τ ^ 3 * carlQ B φ y * w y ^ 2)
          • (μ y • carlV B φ y) := by
  funext y
  simp only [carlFlux]
  module

/-- Lemma 2.1(1) without the symmetry of `B`: the defect is
`τ (⟪B∇φ, ∇w⟫ - ⟪∇φ, B∇w⟫)`. -/
theorem carleman_conj_general (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 1 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 1 B x)
    (hφ : ContDiffAt ℝ 2 φ x) (hw : ContDiffAt ℝ 2 w x) :
    Real.exp (τ * φ x)
        * divMu μ (fun y => B y (gradient (fun z => Real.exp (-τ * φ z) * w z) y)) x
      = carlS μ B φ τ w x + carlT μ B φ τ w x
        + τ * (⟪B x (gradient φ x), gradient w x⟫_ℝ - ⟪gradient φ x, B x (gradient w x)⟫_ℝ) := by
  -- differentiability at `x`
  have hμd : DifferentiableAt ℝ μ x := hμ.differentiableAt one_ne_zero
  have hBd : DifferentiableAt ℝ B x := hB.differentiableAt one_ne_zero
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hwd : DifferentiableAt ℝ w x := hw.differentiableAt (by simp)
  have hgφ : DifferentiableAt ℝ (gradient φ) x := differentiableAt_gradient hφ
  have hgw : DifferentiableAt ℝ (gradient w) x := differentiableAt_gradient hw
  have hWd : DifferentiableAt ℝ (fun y => B y (gradient w y)) x := hBd.clm_apply hgw
  have hVd : DifferentiableAt ℝ (fun y => B y (gradient φ y)) x := hBd.clm_apply hgφ
  have hμWd : DifferentiableAt ℝ (fun y => μ y • B y (gradient w y)) x := hμd.smul hWd
  have hμVd : DifferentiableAt ℝ (fun y => μ y • B y (gradient φ y)) x := hμd.smul hVd
  have hτwd : DifferentiableAt ℝ (fun y => τ * w y) x := hwd.const_mul τ
  have h2d : DifferentiableAt ℝ (fun y => (τ * w y) • (μ y • B y (gradient φ y))) x :=
    hτwd.smul hμVd
  have hFd : DifferentiableAt ℝ
      (fun y => μ y • B y (gradient w y) - (τ * w y) • (μ y • B y (gradient φ y))) x :=
    hμWd.sub h2d
  have hE : HasFDerivAt (fun z => Real.exp (-τ * φ z))
      (Real.exp (-τ * φ x) • ((-τ) • fderiv ℝ φ x)) x :=
    (hφd.hasFDerivAt.const_mul (-τ)).exp
  -- the gradient of the conjugated function near `x`
  have hev : ∀ᶠ y in 𝓝 x, gradient (fun z => Real.exp (-τ * φ z) * w z) y
      = Real.exp (-τ * φ y) • (gradient w y - (τ * w y) • gradient φ y) := by
    filter_upwards [hφ.eventually (by simp), hw.eventually (by simp)] with y hφy hwy
    have hφd' : DifferentiableAt ℝ φ y := hφy.differentiableAt (by simp)
    have hwd' : DifferentiableAt ℝ w y := hwy.differentiableAt (by simp)
    have hE' : HasFDerivAt (fun z => Real.exp (-τ * φ z))
        (Real.exp (-τ * φ y) • ((-τ) • fderiv ℝ φ y)) y :=
      (hφd'.hasFDerivAt.const_mul (-τ)).exp
    have hEw : HasFDerivAt (fun z => Real.exp (-τ * φ z) * w z) _ y := hE'.mul hwd'.hasFDerivAt
    refine ext_inner_right ℝ fun v => ?_
    rw [inner_gradient_left, hEw.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, real_inner_smul_left, inner_sub_left,
      inner_gradient_left]
    ring
  have hev2 : (fun y => μ y • B y (gradient (fun z => Real.exp (-τ * φ z) * w z) y)) =ᶠ[𝓝 x]
      fun y => Real.exp (-τ * φ y) •
        (μ y • B y (gradient w y) - (τ * w y) • (μ y • B y (gradient φ y))) := by
    filter_upwards [hev] with y hy
    rw [hy, map_smul, map_sub, map_smul]
    module
  have hτw : fderiv ℝ (fun y => τ * w y) x = τ • fderiv ℝ w x := fderiv_const_mul hwd τ
  have hdiv : divergence (fun y => μ y • B y (gradient (fun z => Real.exp (-τ * φ z) * w z) y)) x
      = Real.exp (-τ * φ x) * (divergence (fun y => μ y • B y (gradient w y)) x
          - (τ * w x * divergence (fun y => μ y • B y (gradient φ y)) x
            + τ * fderiv ℝ w x (μ x • B x (gradient φ x))))
        + Real.exp (-τ * φ x) * (-τ * fderiv ℝ φ x
            (μ x • B x (gradient w x) - (τ * w x) • (μ x • B x (gradient φ x)))) := by
    rw [divergence_congr hev2, divergence_smul hE.differentiableAt hFd, divergence_sub hμWd h2d,
      divergence_smul hτwd hμVd, hE.fderiv, hτw]
    simp only [smul_apply, smul_eq_mul]
  have hA : fderiv ℝ w x (μ x • B x (gradient φ x))
      = μ x * ⟪B x (gradient φ x), gradient w x⟫_ℝ := by
    rw [← inner_gradient_left, real_inner_smul_right,
      real_inner_comm (B x (gradient φ x)) (gradient w x)]
  have hP : fderiv ℝ φ x (μ x • B x (gradient w x) - (τ * w x) • (μ x • B x (gradient φ x)))
      = μ x * ⟪gradient φ x, B x (gradient w x)⟫_ℝ
        - τ * w x * (μ x * ⟪B x (gradient φ x), gradient φ x⟫_ℝ) := by
    rw [← inner_gradient_left, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_comm (B x (gradient φ x)) (gradient φ x)]
  have hexp : Real.exp (-τ * φ x) = (Real.exp (τ * φ x))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  have hpos : Real.exp (τ * φ x) ≠ 0 := (Real.exp_pos _).ne'
  simp only [carlS, carlT, carlV, carlQ, divMu]
  rw [hdiv, hA, hP, hexp]
  field_simp
  ring

/-- Lemma 2.1(1) (conjugation) for symmetric `B`. -/
theorem carleman_conj_of_symm (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 1 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 1 B x)
    (hsymm : ∀ ξ η, ⟪B x ξ, η⟫_ℝ = ⟪ξ, B x η⟫_ℝ)
    (hφ : ContDiffAt ℝ 2 φ x) (hw : ContDiffAt ℝ 2 w x) :
    Real.exp (τ * φ x)
        * divMu μ (fun y => B y (gradient (fun z => Real.exp (-τ * φ z) * w z) y)) x
      = carlS μ B φ τ w x + carlT μ B φ τ w x := by
  rw [carleman_conj_general μ B φ τ w x hμ hμ0 hB hφ hw, hsymm, sub_self, mul_zero, add_zero]

/-- Lemma 2.1(1) for symmetric `B`, stated for `v` and its conjugate `w = e^{τφ} v`:
`e^{τφ} div_μ(B ∇v) = S w + T w`. -/
theorem carleman_conj_of_symm' (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (v : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 1 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 1 B x)
    (hsymm : ∀ ξ η, ⟪B x ξ, η⟫_ℝ = ⟪ξ, B x η⟫_ℝ)
    (hφ : ContDiffAt ℝ 2 φ x) (hv : ContDiffAt ℝ 2 v x) :
    Real.exp (τ * φ x) * divMu μ (fun y => B y (gradient v y)) x
      = carlS μ B φ τ (fun z => Real.exp (τ * φ z) * v z) x
        + carlT μ B φ τ (fun z => Real.exp (τ * φ z) * v z) x := by
  have hv' : v = fun z => Real.exp (-τ * φ z) * (Real.exp (τ * φ z) * v z) := by
    funext z
    rw [← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]
  have hw : ContDiffAt ℝ 2 (fun z => Real.exp (τ * φ z) * v z) x :=
    ((contDiffAt_const.mul hφ).exp).mul hv
  have key := carleman_conj_of_symm μ B φ τ (fun z => Real.exp (τ * φ z) * v z) x hμ hμ0 hB
    hsymm hφ hw
  rw [← hv'] at key
  exact key

/-- With the trivial density, `div_μ` is the divergence. -/
theorem divMu_one (W : Space n → Space n) (x : Space n) :
    divMu (fun _ => (1 : ℝ)) W x = divergence W x := by
  simp only [divMu, inv_one, one_mul, one_smul]

/-- The gradient of the linear function `⟪a, ·⟫` is `a`. -/
theorem gradient_inner_const (a y : Space n) : gradient (fun z => ⟪a, z⟫_ℝ) y = a := by
  refine ext_inner_right ℝ fun v => ?_
  have hd : HasFDerivAt (fun z => ⟪a, z⟫_ℝ) (innerSL ℝ a) y := (innerSL ℝ a).hasFDerivAt
  rw [inner_gradient_left, hd.fderiv, innerSL_apply_apply]

/-- The statement of the contract theorem `carleman_conj` in dimension `n + 1`, as a proposition
(used only to record exactly when it holds). -/
def CarlemanConjStatement (n : ℕ) : Prop :=
  ∀ (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n),
    ContDiffAt ℝ 1 μ x → μ x ≠ 0 → ContDiffAt ℝ 1 B x → ContDiffAt ℝ 2 φ x →
    ContDiffAt ℝ 2 w x →
    Real.exp (τ * φ x)
        * divMu μ (fun y => B y (gradient (fun z => Real.exp (-τ * φ z) * w z) y)) x
      = carlS μ B φ τ w x + carlT μ B φ τ w x

/-- **The contract statement `carleman_conj` is false without the symmetry of `B`.**
For any orthonormal pair `e₀, e₁`, take `μ = 1`, `B = e₁ ⊗ e₀` (constant, `B ξ = ⟪e₀, ξ⟫ e₁`),
`φ = ⟪e₀, ·⟫`, `w = ⟪e₁, ·⟫`, `τ = 1`, `x = 0`. Then the left side equals
`carlS + carlT + 1`, by `carleman_conj_general`. -/
theorem not_carleman_conj_of_orthonormal {e0 e1 : Space n} (h00 : ⟪e0, e0⟫_ℝ = 1)
    (h01 : ⟪e0, e1⟫_ℝ = 0) (h11 : ⟪e1, e1⟫_ℝ = 1) : ¬ CarlemanConjStatement n := by
  intro h
  have hlin : ∀ a : Space n, ContDiffAt ℝ 2 (fun z : Space n => ⟪a, z⟫_ℝ) 0 :=
    fun a => (innerSL ℝ a).contDiff.contDiffAt
  set B0 : Space n →L[ℝ] Space n := (innerSL ℝ e0).smulRight e1 with hB0
  have key := h (fun _ => 1) (fun _ => B0) (fun z => ⟪e0, z⟫_ℝ) 1 (fun z => ⟪e1, z⟫_ℝ) 0
    contDiffAt_const one_ne_zero contDiffAt_const (hlin e0) (hlin e1)
  have gen := carleman_conj_general (fun _ => 1) (fun _ => B0) (fun z => ⟪e0, z⟫_ℝ) 1
    (fun z => ⟪e1, z⟫_ℝ) 0 contDiffAt_const one_ne_zero contDiffAt_const (hlin e0) (hlin e1)
  rw [key, gradient_inner_const, gradient_inner_const] at gen
  have hc : ⟪B0 e0, e1⟫_ℝ - ⟪e0, B0 e1⟫_ℝ = 1 := by
    simp only [hB0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, h00, h01, one_smul,
      zero_smul, inner_zero_right, h11, sub_zero]
  rw [hc] at gen
  linarith

/-- The contract statement `carleman_conj` fails in every dimension `n + 1 ≥ 2`. -/
theorem not_carleman_conj_of_pos (hn : 0 < n) : ¬ CarlemanConjStatement n := by
  refine not_carleman_conj_of_orthonormal (e0 := EuclideanSpace.single 0 1)
    (e1 := EuclideanSpace.single ⟨1, by omega⟩ 1) (by simp) ?_ (by simp)
  rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
  simp [Fin.ext_iff]

/-- Counterexample to `carleman_conj` in `Space 1 = ℝ²`. -/
theorem not_carleman_conj : ¬ CarlemanConjStatement 1 :=
  not_carleman_conj_of_pos one_pos

/-- In `Space 0 = ℝ¹` every vector is a multiple of the unit vector. -/
theorem space_zero_eq_smul (v : Space 0) : v = v 0 • EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i
  simp

/-- In `Space 0 = ℝ¹` every linear operator is symmetric. -/
theorem symm_of_space_zero (L : Space 0 →L[ℝ] Space 0) (ξ η : Space 0) :
    ⟪L ξ, η⟫_ℝ = ⟪ξ, L η⟫_ℝ := by
  rw [space_zero_eq_smul ξ, space_zero_eq_smul η]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (L (EuclideanSpace.single 0 1))]

/-- The contract statement `carleman_conj` holds in dimension one (`n = 0`), where every `B x`
is symmetric. -/
theorem carleman_conj_zero : CarlemanConjStatement 0 :=
  fun μ B φ τ w x hμ hμ0 hB hφ hw =>
    carleman_conj_of_symm μ B φ τ w x hμ hμ0 hB (symm_of_space_zero (B x)) hφ hw

/-- **Exactly when the contract statement `carleman_conj` holds**: only for `n = 0`. -/
theorem carlemanConjStatement_iff : CarlemanConjStatement n ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    exact not_carleman_conj_of_pos (Nat.pos_of_ne_zero hn) h
  · rintro rfl
    exact carleman_conj_zero

end F2

/-- Lemma 2.1(1): conjugation. -/
theorem carleman_conj (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 1 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 1 B x)
    (hφ : ContDiffAt ℝ 2 φ x) (hw : ContDiffAt ℝ 2 w x) :
    Real.exp (τ * φ x)
        * divMu μ (fun y => B y (gradient (fun z => Real.exp (-τ * φ z) * w z) y)) x
      = carlS μ B φ τ w x + carlT μ B φ τ w x := by
  -- This statement is FALSE as stated: it lacks the symmetry hypothesis on `B` (the note assumes
  -- `A` symmetric throughout). `F2.carlemanConjStatement_iff` proves that it holds iff `n = 0`
  -- (`F2.not_carleman_conj_of_pos`: counterexample in every dimension `≥ 2`;
  -- `F2.carleman_conj_zero`: true in dimension one). `F2.carleman_conj_general` gives the exact
  -- defect `τ (⟪B∇φ, ∇w⟫ - ⟪∇φ, B∇w⟫)`. With the extra hypothesis
  -- `(hsymm : ∀ ξ η, ⟪B x ξ, η⟫_ℝ = ⟪ξ, B x η⟫_ℝ)` the proof is
  -- `F2.carleman_conj_of_symm μ B φ τ w x hμ hμ0 hB hsymm hφ hw`.
  sorry

/-- Lemma 2.1(2), pointwise: `2 (S w)(T w) μ = J + div(flux)`. Requires `B` symmetric. -/
theorem carleman_pointwise (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 2 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 2 B x)
    (hsymm : ∀ y ξ η, ⟪B y ξ, η⟫_ℝ = ⟪ξ, B y η⟫_ℝ)
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
  have hsx := hsymm x
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
  have hμd : DifferentiableAt ℝ μ x := hμ.differentiableAt one_ne_zero
  have hBd : DifferentiableAt ℝ B x := hB.differentiableAt one_ne_zero
  have hϱd : DifferentiableAt ℝ ϱ x := hϱ.differentiableAt one_ne_zero
  have hwd : DifferentiableAt ℝ w x := hw.differentiableAt (by simp)
  have hgw : DifferentiableAt ℝ (gradient w) x := F2.differentiableAt_gradient hw
  have hWd : DifferentiableAt ℝ (fun y => B y (gradient w y)) x := hBd.clm_apply hgw
  have hμWd : DifferentiableAt ℝ (fun y => μ y • B y (gradient w y)) x := hμd.smul hWd
  have hϱwd : DifferentiableAt ℝ (fun y => ϱ y * w y) x := hϱd.mul hwd
  have heq : (fun y => (μ y * ϱ y * w y) • B y (gradient w y))
      = fun y => (ϱ y * w y) • (μ y • B y (gradient w y)) := by
    funext y
    rw [smul_smul]
    ring_nf
  have hfd : fderiv ℝ (fun y => ϱ y * w y) x = ϱ x • fderiv ℝ w x + w x • fderiv ℝ ϱ x :=
    fderiv_mul hϱd hwd
  rw [heq, F2.divergence_smul hϱwd hμWd, hfd, ← F2.mul_divMu hμ0]
  simp only [carlS, add_apply, smul_apply, map_smul, smul_eq_mul, ← inner_gradient_left]
  rw [real_inner_comm (B x (gradient w x)) (gradient w x),
    real_inner_comm (B x (gradient w x)) (gradient ϱ x)]
  field_simp
  ring

end MazyaRefinedCauchy
