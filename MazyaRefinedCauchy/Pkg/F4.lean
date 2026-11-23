module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F4

The theorems stated in this file are the frozen contract of package F4 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## Proof of the sup bound

We use a mean value property with a radial mollifier instead of spherical means. Let
`prof t = -S(1 - 4t)` with `S` the smooth transition function, `Φ(z) = prof(‖z‖²)` and
`φ(z) = 2 prof'(‖z‖²)`, so that `∇Φ(z) = φ(z) z`, `φ ≥ 0`, and both vanish for `‖z‖ > 1/2`.
For `u` harmonic in `B(x, r)`, the function `m(s) = ∫ u(x + s z) φ(z) dz` satisfies
`m'(s) = ∫ ∇u(x + s z) · ∇Φ(z) dz = -s ∫ Δu(x + s z) Φ(z) dz = 0` for `|s| < 2r`
(integration by parts in each coordinate direction). Hence `u(x) ∫ φ = m(0) = m(r)`, and after
rescaling and Cauchy–Schwarz, `|u(x)| ≤ (∫ φ)⁻¹ ‖φ‖₂ r^{-d/2} ‖u‖_{L²(B(x,r))}`.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

namespace F4

open Metric Set Laplacian

/-! ### The radial profile -/

/-- The radial profile `t ↦ -S(1 - 4t)`, where `S` is the smooth transition function. It is
nondecreasing, equals `-1` for `t ≤ 0` and `0` for `t ≥ 1/4`. -/
noncomputable def prof (t : ℝ) : ℝ := -Real.smoothTransition (1 - 4 * t)

lemma prof_contDiff : ContDiff ℝ 2 prof := by
  unfold prof
  have h : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff (n := 2)
  exact (h.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))).neg

lemma prof_eq_zero {t : ℝ} (ht : 1 / 4 ≤ t) : prof t = 0 := by
  unfold prof
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), neg_zero]

lemma prof_monotone : Monotone prof := by
  intro s t hst
  unfold prof
  have := Real.smoothTransition.monotone (show 1 - 4 * t ≤ 1 - 4 * s by linarith)
  linarith

lemma deriv_prof_nonneg (t : ℝ) : 0 ≤ deriv prof t :=
  prof_monotone.deriv_nonneg

lemma deriv_prof_eq_zero {t : ℝ} (ht : 1 / 4 < t) : deriv prof t = 0 := by
  have h : prof =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact prof_eq_zero (le_of_lt hs)
  rw [h.deriv_eq, deriv_const]

lemma exists_deriv_prof_pos : ∃ t, 0 < t ∧ 0 < deriv prof t := by
  have hd : Differentiable ℝ prof := prof_contDiff.differentiable (by norm_num)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope prof (show (0 : ℝ) < 1 / 4 by norm_num)
    hd.continuous.continuousOn hd.differentiableOn
  refine ⟨c, hc.1, ?_⟩
  rw [hc', prof_eq_zero le_rfl]
  have h0 : prof 0 = -1 := by
    unfold prof
    simp [Real.smoothTransition.one_of_one_le]
  rw [h0]
  norm_num

/-! ### The test functions `Φ` and `φ` -/

/-- `Φ(z) = prof(‖z‖²)`. -/
noncomputable def Phi (z : Space n) : ℝ := prof (‖z‖ ^ 2)

/-- `φ(z) = 2 prof'(‖z‖²)`, so that `∇Φ(z) = φ(z) z`. -/
noncomputable def phi (z : Space n) : ℝ := 2 * deriv prof (‖z‖ ^ 2)

lemma hasFDerivAt_Phi (z : Space n) :
    HasFDerivAt (Phi (n := n)) (phi z • innerSL ℝ z) z := by
  have hd : Differentiable ℝ prof := prof_contDiff.differentiable (by norm_num)
  have h : HasFDerivAt (Phi (n := n)) (deriv prof (‖z‖ ^ 2) • (2 • innerSL ℝ z)) z :=
    (hd (‖z‖ ^ 2)).hasDerivAt.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  refine h.congr_fderiv ?_
  ext v
  simp [phi]
  ring

lemma fderiv_Phi_apply (z v : Space n) : fderiv ℝ (Phi (n := n)) z v = phi z * ⟪z, v⟫ := by
  rw [(hasFDerivAt_Phi z).fderiv]
  simp

lemma differentiable_Phi : Differentiable ℝ (Phi (n := n)) :=
  fun z => (hasFDerivAt_Phi z).differentiableAt

lemma continuous_Phi : Continuous (Phi (n := n)) :=
  differentiable_Phi.continuous

lemma continuous_phi : Continuous (phi (n := n)) := by
  unfold phi
  exact continuous_const.mul ((prof_contDiff.continuous_deriv (by norm_num)).comp
    (continuous_norm.pow 2))

lemma phi_nonneg (z : Space n) : 0 ≤ phi z :=
  mul_nonneg zero_le_two (deriv_prof_nonneg _)

lemma Phi_eq_zero {z : Space n} (hz : 1 / 2 ≤ ‖z‖) : Phi z = 0 := by
  unfold Phi
  apply prof_eq_zero
  nlinarith

lemma phi_eq_zero {z : Space n} (hz : 1 / 2 < ‖z‖) : phi z = 0 := by
  unfold phi
  rw [deriv_prof_eq_zero (by nlinarith), mul_zero]

lemma tsupport_Phi_subset : tsupport (Phi (n := n)) ⊆ closedBall 0 (1 / 2) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  rw [mem_closedBall_zero_iff]
  by_contra h
  exact hz (Phi_eq_zero (le_of_lt (not_le.mp h)))

lemma tsupport_phi_subset : tsupport (phi (n := n)) ⊆ closedBall 0 (1 / 2) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  rw [mem_closedBall_zero_iff]
  by_contra h
  exact hz (phi_eq_zero (not_le.mp h))

lemma hasCompactSupport_phi : HasCompactSupport (phi (n := n)) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) tsupport_phi_subset

lemma integrable_phi : Integrable (phi (n := n)) :=
  continuous_phi.integrable_of_hasCompactSupport hasCompactSupport_phi

lemma integral_phi_pos : 0 < ∫ z, phi (n := n) z := by
  rw [integral_pos_iff_support_of_nonneg (fun z => phi_nonneg z) integrable_phi]
  obtain ⟨t, ht, ht'⟩ := exists_deriv_prof_pos
  obtain ⟨z, hz⟩ := exists_norm_eq (Space n) (Real.sqrt_nonneg t)
  have hz' : phi z ≠ 0 := by
    unfold phi
    rw [hz, Real.sq_sqrt ht.le]
    positivity
  exact continuous_phi.isOpen_support.measure_pos volume ⟨z, hz'⟩

/-! ### Integrability of localized products -/

/-- A product `g * h` is integrable when `g` is continuous on an open set `U` and `h` is
continuous with topological support in a compact subset of `U`. -/
lemma integrable_mul_of_continuousOn {U K : Set (Space n)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {g h : Space n → ℝ} (hg : ContinuousOn g U) (hh : Continuous h)
    (hsupp : tsupport h ⊆ K) : Integrable (fun z => g z * h z) := by
  have hc : Continuous (fun z => g z * h z) :=
    (hg.mul hh.continuousOn).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_right.trans (hsupp.trans hKU))
  exact hc.integrable_of_hasCompactSupport
    (hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_mul_subset_right.trans hsupp))

/-! ### The mean value property for the mollifier `φ` -/

/-- The key identity: `∫ ∇u(x + s z) · z φ(z) dz = 0` for `|s| < 2r`. -/
lemma integral_fderiv_mul_phi_eq_zero {u : Space n → ℝ} {x : Space n} {r : ℝ} (_hr : 0 < r)
    (hu : HarmonicOnNhd u (ball x r)) {s : ℝ} (hs : |s| < 2 * r) :
    ∫ z, fderiv ℝ u (x + s • z) z * phi z = 0 := by
  set b := stdOrthonormalBasis ℝ (Space n) with hb
  set A : Space n → Space n := fun z => x + s • z with hA
  set U : Set (Space n) := A ⁻¹' ball x r with hUdef
  have hAc : ContDiff ℝ 1 A := by
    rw [hA]; fun_prop
  have hUo : IsOpen U := isOpen_ball.preimage hAc.continuous
  have hKU : closedBall (0 : Space n) (1 / 2) ⊆ U := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    show x + s • z ∈ ball x r
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖z‖ ≤ |s| * (1 / 2) := by gcongr
      _ < r := by linarith
  have hK : IsCompact (closedBall (0 : Space n) (1 / 2)) := isCompact_closedBall _ _
  have hu2 : ContDiffOn ℝ 2 u (ball x r) := hu.contDiffOn
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) (ball x r) :=
    hu2.fderiv_of_isOpen isOpen_ball (by norm_num)
  -- partial derivatives along the basis, composed with `A`
  set f : _ → Space n → ℝ := fun i z => fderiv ℝ u (A z) (b i) with hf
  have hfC : ∀ i, ContDiffOn ℝ 1 (f i) U := by
    intro i
    have hG : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y (b i)) (ball x r) :=
      hDu.clm_apply contDiffOn_const
    exact hG.comp hAc.contDiffOn (mapsTo_preimage _ _)
  have hfD : ∀ i, ∀ z ∈ U,
      fderiv ℝ (f i) z (b i) = s * fderiv ℝ (fderiv ℝ u) (A z) (b i) (b i) := by
    intro i z hz
    have hz' : A z ∈ ball x r := hz
    have hD : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) (A z)) (A z) :=
      ((hDu.differentiableOn one_ne_zero _ hz').differentiableAt
        (isOpen_ball.mem_nhds hz')).hasFDerivAt
    have hG : HasFDerivAt (fun y => fderiv ℝ u y (b i))
        ((ContinuousLinearMap.apply ℝ ℝ (b i)).comp (fderiv ℝ (fderiv ℝ u) (A z))) (A z) :=
      (ContinuousLinearMap.apply ℝ ℝ (b i)).hasFDerivAt.comp (A z) hD
    have hAd : HasFDerivAt A (s • ContinuousLinearMap.id ℝ (Space n) : Space n →L[ℝ] Space n) z := by
      exact ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul s).const_add x
    have hcomp : f i = (fun y => fderiv ℝ u y (b i)) ∘ A := rfl
    rw [hcomp, (hG.comp z hAd).fderiv]
    simp
  have hfDiff : ∀ i, ∀ z ∈ U, DifferentiableAt ℝ (f i) z := fun i z hz =>
    ((hfC i).differentiableOn one_ne_zero z hz).differentiableAt (hUo.mem_nhds hz)
  have hfc : ∀ i, ContinuousOn (f i) U := fun i => (hfC i).continuousOn
  have hf'c : ∀ i, ContinuousOn (fun z => fderiv ℝ (f i) z (b i)) U := fun i =>
    ((hfC i).continuousOn_fderiv_of_isOpen hUo le_rfl).clm_apply continuousOn_const
  -- the derivatives of `Φ`
  have hPhi' : ∀ i, (fun z => fderiv ℝ (Phi (n := n)) z (b i)) = fun z => phi z * ⟪z, b i⟫ :=
    fun i => funext fun z => fderiv_Phi_apply z (b i)
  have hPhi'c : ∀ i, Continuous (fun z => fderiv ℝ (Phi (n := n)) z (b i)) := by
    intro i
    rw [hPhi' i]
    exact continuous_phi.mul (continuous_id.inner continuous_const)
  have hPhi's : ∀ i,
      tsupport (fun z => fderiv ℝ (Phi (n := n)) z (b i)) ⊆ closedBall 0 (1 / 2) := by
    intro i
    rw [hPhi' i]
    exact tsupport_mul_subset_left.trans tsupport_phi_subset
  -- integration by parts in each direction
  have hibp : ∀ i, ∫ z, f i z * fderiv ℝ Phi z (b i) =
      -∫ z, fderiv ℝ (f i) z (b i) * Phi z := by
    intro i
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
    · exact integrable_mul_of_continuousOn hUo hK hKU (hf'c i) continuous_Phi tsupport_Phi_subset
    · exact integrable_mul_of_continuousOn hUo hK hKU (hfc i) (hPhi'c i) (hPhi's i)
    · exact integrable_mul_of_continuousOn hUo hK hKU (hfc i) continuous_Phi tsupport_Phi_subset
    · exact fun z hz => hfDiff i z (hKU (tsupport_Phi_subset hz))
    · exact fun z _ => differentiable_Phi z
  -- pointwise identities
  have hpt1 : ∀ z, fderiv ℝ u (A z) z * phi z = ∑ i, f i z * fderiv ℝ Phi z (b i) := by
    intro z
    have hz : fderiv ℝ u (A z) z = ∑ i, ⟪b i, z⟫ * fderiv ℝ u (A z) (b i) := by
      calc fderiv ℝ u (A z) z = fderiv ℝ u (A z) (∑ i, ⟪b i, z⟫ • b i) := by
            rw [b.sum_repr' z]
        _ = _ := by simp [map_sum, map_smul]
    rw [hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_Phi_apply, real_inner_comm]
    simp only [hf]
    ring
  have hpt2 : ∀ z, ∑ i, fderiv ℝ (f i) z (b i) * Phi z = 0 := by
    intro z
    by_cases hz : Phi z = 0
    · simp [hz]
    · have hzK : z ∈ closedBall (0 : Space n) (1 / 2) := by
        rw [mem_closedBall_zero_iff]
        by_contra h
        exact hz (Phi_eq_zero (not_le.mp h).le)
      have hzU := hKU hzK
      have hAz : A z ∈ ball x r := hzU
      have hlap : ∑ i, fderiv ℝ (fderiv ℝ u) (A z) (b i) (b i) = 0 := by
        have h1 := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis u b) (A z)
        have h2 : Δ u (A z) = 0 := (hu (A z) hAz).2.eq_of_nhds
        rw [h2] at h1
        simp only [iteratedFDeriv_two_apply] at h1
        simpa using h1.symm
      rw [← Finset.sum_mul]
      rw [Finset.sum_congr rfl fun i _ => hfD i z hzU, ← Finset.mul_sum, hlap]
      simp
  have hI1 : ∀ i, Integrable (fun z => f i z * fderiv ℝ (Phi (n := n)) z (b i)) := fun i =>
    integrable_mul_of_continuousOn hUo hK hKU (hfc i) (hPhi'c i) (hPhi's i)
  have hI2 : ∀ i, Integrable (fun z => fderiv ℝ (f i) z (b i) * Phi z) := fun i =>
    integrable_mul_of_continuousOn hUo hK hKU (hf'c i) continuous_Phi tsupport_Phi_subset
  -- conclusion
  calc ∫ z, fderiv ℝ u (x + s • z) z * phi z = ∫ z, ∑ i, f i z * fderiv ℝ Phi z (b i) := by
        congr 1
        funext z
        exact hpt1 z
    _ = ∑ i, ∫ z, f i z * fderiv ℝ Phi z (b i) := integral_finsetSum _ (fun i _ => hI1 i)
    _ = ∑ i, -∫ z, fderiv ℝ (f i) z (b i) * Phi z := Finset.sum_congr rfl fun i _ => hibp i
    _ = -∫ z, ∑ i, fderiv ℝ (f i) z (b i) * Phi z := by
        rw [integral_finsetSum _ (fun i _ => hI2 i), Finset.sum_neg_distrib]
    _ = 0 := by simp [hpt2]

/-- Differentiation of the mollified values `m(s) = ∫ u(x + s z) φ(z) dz` under the integral. -/
lemma hasDerivAt_mollified {u : Space n → ℝ} {x : Space n} {r : ℝ} (hr : 0 < r)
    (hu : HarmonicOnNhd u (ball x r)) {s₀ : ℝ} (hs₀ : |s₀| < 2 * r) :
    HasDerivAt (fun s => ∫ z, u (x + s • z) * phi z)
      (∫ z, fderiv ℝ u (x + s₀ • z) z * phi z) s₀ := by
  set ρ := (|s₀| + 2 * r) / 2 with hρ
  have hρ1 : |s₀| < ρ := by rw [hρ]; linarith
  have hρ2 : ρ < 2 * r := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt (abs_nonneg _) hρ1
  have hu1 : ContDiffOn ℝ 2 u (ball x r) := hu.contDiffOn
  have hDcont : ContinuousOn (fderiv ℝ u) (ball x r) :=
    hu1.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (ρ / 2)).exists_bound_of_continuousOn
    (hDcont.mono (closedBall_subset_ball (by linarith)))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self (by linarith)))
  -- membership facts
  have hmem : ∀ s z, |s| < 2 * r → ‖z‖ ≤ 1 / 2 → x + s • z ∈ ball x r := by
    intro s z hs hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖z‖ ≤ |s| * (1 / 2) := by gcongr
      _ < r := by linarith
  have hmem' : ∀ s z, |s| ≤ ρ → ‖z‖ ≤ 1 / 2 → x + s • z ∈ closedBall x (ρ / 2) := by
    intro s z hs hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖z‖ ≤ ρ * (1 / 2) := by gcongr
      _ = ρ / 2 := by ring
  have hsupp : ∀ z : Space n, phi z ≠ 0 → ‖z‖ ≤ 1 / 2 := by
    intro z hz
    by_contra h
    exact hz (phi_eq_zero (not_le.mp h))
  -- the open sets where the integrands are continuous
  have hU : ∀ s : ℝ, IsOpen ((fun z : Space n => x + s • z) ⁻¹' ball x r) := fun s =>
    isOpen_ball.preimage (by fun_prop)
  have hKU : ∀ s, |s| < 2 * r →
      closedBall (0 : Space n) (1 / 2) ⊆ (fun z : Space n => x + s • z) ⁻¹' ball x r := by
    intro s hs z hz
    exact hmem s z hs (by simpa using hz)
  have hint : ∀ s, |s| < 2 * r → Integrable (fun z => u (x + s • z) * phi z) := by
    intro s hs
    refine integrable_mul_of_continuousOn (hU s) (isCompact_closedBall 0 (1 / 2)) (hKU s hs)
      ?_ continuous_phi tsupport_phi_subset
    exact hu.continuousOn.comp (by fun_prop) (mapsTo_preimage _ _)
  have hint' : Integrable (fun z => fderiv ℝ u (x + s₀ • z) z * phi z) := by
    refine integrable_mul_of_continuousOn (hU s₀) (isCompact_closedBall 0 (1 / 2)) (hKU s₀ hs₀)
      ?_ continuous_phi tsupport_phi_subset
    exact (hDcont.comp (by fun_prop) (mapsTo_preimage _ _)).clm_apply continuousOn_id
  have hnhds : Ioo (-ρ) ρ ∈ 𝓝 s₀ :=
    Ioo_mem_nhds (by linarith [neg_abs_le s₀]) (lt_of_le_of_lt (le_abs_self _) hρ1)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s z => u (x + s • z) * phi z)
    (F' := fun s z => fderiv ℝ u (x + s • z) z * phi z)
    (bound := fun z => M * |phi z|) hnhds ?_ (hint s₀ hs₀) hint'.aestronglyMeasurable ?_
    (integrable_phi.abs.const_mul M) ?_).2
  · filter_upwards [hnhds] with s hs
    exact (hint s (abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)).aestronglyMeasurable
  · refine ae_of_all _ fun z s hs => ?_
    by_cases hz : phi z = 0
    · simp [hz]
    · have hz' := hsupp z hz
      have hs' : |s| ≤ ρ := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
      rw [norm_mul, Real.norm_eq_abs (phi z)]
      gcongr
      calc ‖fderiv ℝ u (x + s • z) z‖ ≤ ‖fderiv ℝ u (x + s • z)‖ * ‖z‖ :=
            (fderiv ℝ u _).le_opNorm z
        _ ≤ M * 1 := by
            gcongr
            · exact hM _ (hmem' s z hs' hz')
            · linarith
        _ = M := mul_one M
  · refine ae_of_all _ fun z s hs => ?_
    by_cases hz : phi z = 0
    · simp only [hz, mul_zero]
      exact hasDerivAt_const s 0
    · have hz' := hsupp z hz
      have hs' : |s| < 2 * r := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hxs := hmem s z hs' hz'
      have hd : HasFDerivAt u (fderiv ℝ u (x + s • z)) (x + s • z) :=
        ((hu1.differentiableOn (by norm_num) _ hxs).differentiableAt
          (isOpen_ball.mem_nhds hxs)).hasFDerivAt
      have hA : HasDerivAt (fun s : ℝ => x + s • z) z s := by
        simpa using ((hasDerivAt_id s).smul_const z).const_add x
      exact (hd.comp_hasDerivAt s hA).mul_const (phi z)

/-- The mean value property with the mollifier `φ`. -/
lemma mean_value_phi {u : Space n → ℝ} {x : Space n} {r : ℝ} (hr : 0 < r)
    (hu : HarmonicOnNhd u (ball x r)) :
    u x * ∫ z, phi (n := n) z = ∫ z, u (x + r • z) * phi z := by
  set m : ℝ → ℝ := fun s => ∫ z, u (x + s • z) * phi z with hm
  have hderiv : ∀ s ∈ Icc (0 : ℝ) r, HasDerivAt m 0 s := by
    intro s hs
    have hs' : |s| < 2 * r := by rw [abs_of_nonneg hs.1]; linarith [hs.2]
    have := hasDerivAt_mollified hr hu hs'
    rwa [integral_fderiv_mul_phi_eq_zero hr hu hs'] at this
  obtain ⟨c, -, hc'⟩ := exists_hasDerivAt_eq_slope m (fun _ => (0 : ℝ)) hr
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => hderiv s (Ioo_subset_Icc_self hs))
  have hmr : m r = m 0 := by
    have h := hc'.symm
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · linarith
    · rw [sub_zero] at h; exact absurd h hr.ne'
  have hm0 : m 0 = u x * ∫ z, phi (n := n) z := by
    simp only [hm, zero_smul, add_zero]
    exact integral_const_mul (u x) _
  rw [← hm0, ← hmr]

/-! ### Rescaling and Cauchy–Schwarz -/

/-- Change of variables `y = x + r z`. -/
lemma integral_rescale (u : Space n → ℝ) (x : Space n) {r : ℝ} (hr : 0 < r) :
    ∫ z, u (x + r • z) * phi z = (r ^ (n + 1))⁻¹ * ∫ y, u y * phi (r⁻¹ • (y - x)) := by
  have h1 : (fun z : Space n => u (x + r • z) * phi z) =
      fun z => (fun w => u (x + w) * phi (r⁻¹ • w)) (r • z) := by
    funext z
    simp [smul_smul, inv_mul_cancel₀ hr.ne']
  rw [h1, Measure.integral_comp_smul volume (fun w => u (x + w) * phi (r⁻¹ • w)) r]
  have h2 : ∫ w, u (x + w) * phi (r⁻¹ • w) = ∫ y, u y * phi (r⁻¹ • (y - x)) := by
    have := integral_add_left_eq_self (μ := (volume : Measure (Space n)))
      (fun y => u y * phi (r⁻¹ • (y - x))) x
    simpa only [add_sub_cancel_left] using this
  rw [h2, finrank_euclideanSpace_fin, smul_eq_mul, abs_of_pos (inv_pos.mpr (pow_pos hr _))]

lemma integral_phi_rescale_sq (x : Space n) {r : ℝ} (hr : 0 < r) :
    ∫ y, phi (r⁻¹ • (y - x)) ^ 2 = r ^ (n + 1) * ∫ z, phi (n := n) z ^ 2 := by
  have h1 := integral_sub_right_eq_self (μ := (volume : Measure (Space n)))
    (fun w => phi (r⁻¹ • w) ^ 2) x
  rw [h1, Measure.integral_comp_smul volume (fun w => phi w ^ 2) r⁻¹, finrank_euclideanSpace_fin,
    smul_eq_mul, inv_pow, inv_inv, abs_of_pos (pow_pos hr _)]

/-- Cauchy–Schwarz on the ball. -/
lemma abs_integral_le_sqrt {u : Space n → ℝ} {x : Space n} {r : ℝ} (hr : 0 < r)
    (hu : ContinuousOn u (closedBall x r)) :
    |∫ y, u y * phi (r⁻¹ • (y - x))| ≤
      Real.sqrt (∫ y in ball x r, u y ^ 2) * Real.sqrt (∫ y, phi (r⁻¹ • (y - x)) ^ 2) := by
  set ψ : Space n → ℝ := fun y => phi (r⁻¹ • (y - x)) with hψ
  have hψ0 : ∀ y, y ∉ ball x r → ψ y = 0 := by
    intro y hy
    apply phi_eq_zero
    rw [mem_ball, dist_eq_norm, not_lt] at hy
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    calc (1 : ℝ) / 2 < 1 := by norm_num
      _ = r⁻¹ * r := (inv_mul_cancel₀ hr.ne').symm
      _ ≤ r⁻¹ * ‖y - x‖ := by gcongr
  have hψc : Continuous ψ := continuous_phi.comp (by fun_prop)
  have hψs : HasCompactSupport ψ :=
    HasCompactSupport.intro (isCompact_closedBall x r)
      (fun y hy => hψ0 y (fun h => hy (ball_subset_closedBall h)))
  have e1 : ∫ y in ball x r, u y * ψ y = ∫ y, u y * ψ y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by simp [hψ0 y hy])
  have e2 : ∫ y in ball x r, ψ y ^ 2 = ∫ y, ψ y ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by simp [hψ0 y hy])
  rw [← e1, ← e2]
  have hmeas : AEStronglyMeasurable u (volume.restrict (ball x r)) :=
    (hu.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hu2 : MemLp u (ENNReal.ofReal 2) (volume.restrict (ball x r)) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
    exact ((hu.pow 2).integrableOn_compact (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
  have hψ2 : MemLp ψ (ENNReal.ofReal 2) (volume.restrict (ball x r)) :=
    (hψc.memLp_of_hasCompactSupport hψs).restrict _
  calc |∫ y in ball x r, u y * ψ y| ≤ ∫ y in ball x r, ‖u y‖ * ‖ψ y‖ := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        simp only [norm_mul]
    _ ≤ (∫ y in ball x r, ‖u y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ y in ball x r, ‖ψ y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hu2 hψ2
    _ = _ := by
        simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]

end F4

/-! ## Package F4: harmonic functions: a sup bound from `L²` -/

/-- A harmonic function is bounded at the centre of a ball by its `L²` norm on the ball. -/
theorem harmonic_abs_le_L2 (n : ℕ) : ∃ Cn : ℝ, ∀ (u : Space n → ℝ) (x : Space n) (r : ℝ),
    0 < r → HarmonicOnNhd u (Metric.closedBall x r) →
      |u x| ≤ Cn * r ^ (-((n + 1 : ℝ) / 2)) * Real.sqrt (∫ y in Metric.ball x r, u y ^ 2) := by
  set I := ∫ z, F4.phi (n := n) z with hI
  set J := ∫ z, F4.phi (n := n) z ^ 2 with hJ
  have hIpos : 0 < I := F4.integral_phi_pos
  refine ⟨I⁻¹ * Real.sqrt J, fun u x r hr hu => ?_⟩
  have hu' : HarmonicOnNhd u (Metric.ball x r) := hu.mono Metric.ball_subset_closedBall
  have hmv := F4.mean_value_phi hr hu'
  rw [F4.integral_rescale u x hr] at hmv
  have hcs := F4.abs_integral_le_sqrt hr hu.continuousOn
  rw [F4.integral_phi_rescale_sq x hr] at hcs
  set A := ∫ y in Metric.ball x r, u y ^ 2 with hA
  have hrpow : 0 < r ^ (n + 1) := pow_pos hr _
  have key : |u x| * I ≤ (r ^ (n + 1))⁻¹ * (Real.sqrt A * Real.sqrt (r ^ (n + 1) * J)) := by
    have h1 : |u x * I| = (r ^ (n + 1))⁻¹ * |∫ y, u y * F4.phi (r⁻¹ • (y - x))| := by
      rw [← hI] at hmv
      rw [hmv, abs_mul, abs_of_pos (inv_pos.mpr hrpow)]
    rw [← abs_of_pos hIpos, ← abs_mul, h1]
    exact mul_le_mul_of_nonneg_left hcs (inv_pos.mpr hrpow).le
  have hsqrt : Real.sqrt (r ^ (n + 1) * J) = Real.sqrt (r ^ (n + 1)) * Real.sqrt J :=
    Real.sqrt_mul hrpow.le J
  have hrr : (r ^ (n + 1))⁻¹ * Real.sqrt (r ^ (n + 1)) = r ^ (-((n + 1 : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_neg_one,
      ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  calc |u x| = (|u x| * I) * I⁻¹ := by field_simp
    _ ≤ ((r ^ (n + 1))⁻¹ * (Real.sqrt A * Real.sqrt (r ^ (n + 1) * J))) * I⁻¹ := by
        gcongr
    _ = I⁻¹ * Real.sqrt J * ((r ^ (n + 1))⁻¹ * Real.sqrt (r ^ (n + 1))) * Real.sqrt A := by
        rw [hsqrt]; ring
    _ = I⁻¹ * Real.sqrt J * r ^ (-((n + 1 : ℝ) / 2)) * Real.sqrt A := by rw [hrr]

end MazyaRefinedCauchy
