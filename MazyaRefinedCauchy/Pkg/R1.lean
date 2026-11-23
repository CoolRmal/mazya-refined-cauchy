module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F3
public import MazyaRefinedCauchy.Pkg.F4
public import MazyaRefinedCauchy.Pkg.U
public import MazyaRefinedCauchy.Pkg.G

@[expose] public section

/-!
# Work package R1

The theorems stated in this file are the frozen contract of package R1 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## Plan of the proof (dimension `d = n + 1 ≥ 2`)

Write `E(r) = ∫_{B_r⁺} v²`.

1. `neumann_flat`: by continuity the conormal datum is also `O(|x|^N)` at the point `0`
   (this uses `n ≥ 1`: `0` is a limit of other points of the flat piece).
2. `exists_doubling_scale`, `exists_scales`: if `E(r) = O(r^M)` fails, there are scales
   `s_j → 0` with `E(2 s_j) ≤ 2^{3M} E(s_j)` and `E(s_j) > s_j^{2M}`.
3. The blow-ups `w_j(X) = √(s_j^d / E(s_j)) v(s_j X)` have `∫_{B_1⁺} w_j² = 1`, bounded `L²` norm
   on `B_2⁺` and (Caccioppoli up to the flat boundary) bounded Dirichlet energy on `B_{3/2}⁺`.
4. `exists_L2_subseq_halfBall` (F3 applied to the cut-off even reflections): a subsequence
   converges in `L²(B_{5/4}⁺)` to some `g`.
5. `tendsto_integral_w_lap` (Green's formula, `A(0) = I`, flat Cauchy data):
   `∫_{t>0} w_j Δψ → 0` for every `C²` test function `ψ` supported in `B_{3/2}`.
6. Hence the zero extension `U` of `g|_{B_{5/4}⁺}` is weakly harmonic in `B_{5/4}` and vanishes on
   `{t ≤ 0}`; by mollification and weak unique continuation (package U) it vanishes a.e. on
   `B_1` (`ae_eq_zero_of_weakly_harmonic`).
7. This contradicts `∫_{B_1⁺} w_j² = 1`.

## Status

Everything is proved except
* `R1Aux.integral_sub_translate_sq_le` (the `L²` translation bound, a generic real-analysis
  lemma) and `R1Aux.exists_L2_subseq_halfBall` (Step 4; a plan is in its docstring);
* the case `n = 0` of the contract, which is false (see below).
Step 6 uses the contract `weak_ucp` of package U.

## The case `n = 0`

For `n = 0` (dimension one) the contract is false: the flat piece is `{0}`, so the Neumann
hypothesis `hneu` is vacuous, and `v(x) = x₀` (with `A = id`, `B = 0`, `C = 0`, `Dv = e_d`)
satisfies all hypotheses while `∫_{B_r⁺} v² = r³/3` is not `O(r⁴)`.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

namespace R1Aux

open Metric Set
open scoped Pointwise

/-! ### Basic objects -/

/-- The Laplacian `Δψ = div ∇ψ`. -/
noncomputable def lap (ψ : Space n → ℝ) (x : Space n) : ℝ := divergence (gradient ψ) x

/-- The squared `L²` norm of `v` on the half-ball of radius `r`. -/
noncomputable def E (S : HalfBallSolution n) (r : ℝ) : ℝ := ∫ x in halfBall n r, S.v x ^ 2

/-- The normalizing constant `√(s^d / E(s))` of the blow-up. -/
noncomputable def cst (S : HalfBallSolution n) (s : ℝ) : ℝ := Real.sqrt (s ^ (n + 1) / E S s)

/-- The blow-up `w_s(X) = √(s^d / E(s)) v(sX)`. -/
noncomputable def w (S : HalfBallSolution n) (s : ℝ) (X : Space n) : ℝ := cst S s * S.v (s • X)

/-- Its gradient `∇w_s(X) = s √(s^d / E(s)) Dv(sX)`. -/
noncomputable def Dw (S : HalfBallSolution n) (s : ℝ) (X : Space n) : Space n :=
  (cst S s * s) • S.Dv (s • X)

lemma halfBall_subset_closedHalfBall (r : ℝ) : halfBall n r ⊆ closedHalfBall n r :=
  fun _ hx => ⟨hx.1, hx.2.le⟩

lemma halfBall_mono {r r' : ℝ} (h : r ≤ r') : halfBall n r ⊆ halfBall n r' :=
  fun _ hx => ⟨lt_of_lt_of_le hx.1 h, hx.2⟩

lemma closedHalfBall_mono {r r' : ℝ} (h : r ≤ r') : closedHalfBall n r ⊆ closedHalfBall n r' :=
  fun _ hx => ⟨lt_of_lt_of_le hx.1 h, hx.2⟩

lemma measurableSet_halfBall (r : ℝ) : MeasurableSet (halfBall n r) := by
  have h1 : MeasurableSet {x : Space n | ‖x‖ < r} :=
    measurableSet_lt measurable_norm measurable_const
  have h2 : MeasurableSet {x : Space n | 0 < vcoord x} := F1.measurableSet_halfSpace 0
  exact h1.inter h2

lemma vcoord_smul (s : ℝ) (x : Space n) : vcoord (s • x) = s * vcoord x := by
  simp [vcoord]

lemma isCompact_halfBallLe (r : ℝ) : IsCompact {x : Space n | ‖x‖ ≤ r ∧ 0 ≤ vcoord x} := by
  apply (isCompact_closedBall (0 : Space n) r).of_isClosed_subset
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const F1.continuous_vcoord)
  · intro x hx
    simpa using hx.1

/-- A function continuous on `closedHalfBall n R` is integrable on every smaller half-ball. -/
lemma integrableOn_halfBall_of_continuousOn {F : Type*} [NormedAddCommGroup F]
    {f : Space n → F} {r R : ℝ} (hr : r < R)
    (hf : ContinuousOn f (closedHalfBall n R)) : IntegrableOn f (halfBall n r) := by
  have hK := isCompact_halfBallLe (n := n) r
  have hsub : {x : Space n | ‖x‖ ≤ r ∧ 0 ≤ vcoord x} ⊆ closedHalfBall n R :=
    fun x hx => ⟨lt_of_le_of_lt hx.1 hr, hx.2⟩
  exact ((hf.mono hsub).integrableOn_compact hK).mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)

lemma volume_halfBall_lt_top (r : ℝ) : volume (halfBall n r) < ⊤ :=
  (measure_mono (fun x (hx : x ∈ halfBall n r) =>
    (mem_ball_zero_iff.mpr hx.1 : x ∈ ball (0 : Space n) r))).trans_lt
    measure_ball_lt_top

lemma isFiniteMeasure_halfBall (r : ℝ) : IsFiniteMeasure (volume.restrict (halfBall n r)) :=
  isFiniteMeasure_restrict.mpr (volume_halfBall_lt_top r).ne

lemma E_nonneg (S : HalfBallSolution n) (r : ℝ) : 0 ≤ E S r :=
  setIntegral_nonneg (measurableSet_halfBall r) (fun _ _ => sq_nonneg _)

lemma E_mono (S : HalfBallSolution n) {a b : ℝ} (hab : a ≤ b) (hb : b < S.R) :
    E S a ≤ E S b := by
  unfold E
  apply setIntegral_mono_set
  · exact integrableOn_halfBall_of_continuousOn hb (S.v_continuousOn.pow 2)
  · exact Eventually.of_forall (fun x => sq_nonneg _)
  · exact ae_of_all _ (halfBall_mono hab)

lemma contDiff_gradient {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) : ContDiff ℝ 1 (gradient ψ) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  have h2 : gradient ψ = fun x => (InnerProductSpace.toDual ℝ (Space n)).symm (fderiv ℝ ψ x) := by
    funext x; rfl
  rw [h2]
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.contDiff.comp h1

lemma divergence_eq_sum_inner (F : Space n → Space n) (x : Space n) :
    divergence F x = ∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i,
      fderiv ℝ F x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)⟫_ℝ := by
  unfold divergence
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
  rfl

lemma lap_eq_sum (ψ : Space n → ℝ) (x : Space n) :
    lap ψ x = ∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i,
      fderiv ℝ (gradient ψ) x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)⟫_ℝ := by
  unfold lap divergence
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
  rfl

lemma continuous_lap {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) : Continuous (lap ψ) := by
  have h := (contDiff_gradient hψ).continuous_fderiv (by norm_num)
  have e : lap ψ = fun x => ∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i,
      fderiv ℝ (gradient ψ) x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)⟫_ℝ := by
    funext x; exact lap_eq_sum ψ x
  rw [e]
  exact continuous_finsetSum _ fun i _ => continuous_const.inner (h.clm_apply continuous_const)

lemma lap_eq_zero_of_eventuallyEq {ψ : Space n → ℝ} {x : Space n}
    (h : ψ =ᶠ[𝓝 x] fun _ => 0) : lap ψ x = 0 := by
  have h1 : gradient ψ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [h.eventually_nhds] with y hy
    have hy' : ψ =ᶠ[𝓝 y] fun _ => 0 := hy
    unfold gradient
    rw [hy'.fderiv_eq]
    simp
  unfold lap divergence
  rw [h1.fderiv_eq]
  simp

lemma lap_eq_zero_of_norm_gt {ψ : Space n → ℝ} {ρ : ℝ} (hψs : ∀ x, ρ ≤ ‖x‖ → ψ x = 0)
    {x : Space n} (hx : ρ < ‖x‖) : lap ψ x = 0 := by
  apply lap_eq_zero_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact hψs y (le_of_lt hy)

lemma hasCompactSupport_lap {ψ : Space n → ℝ} {ρ : ℝ} (hψs : ∀ x, ρ ≤ ‖x‖ → ψ x = 0) :
    HasCompactSupport (lap ψ) :=
  F3.hasCompactSupport_of_eq_zero (S := ρ + 1) fun y hy =>
    lap_eq_zero_of_norm_gt hψs (by linarith)

/-- The gradient of a dilation. -/
lemma gradient_comp_smul {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (s : ℝ) (x : Space n) :
    gradient (fun y => ψ (s⁻¹ • y)) x = s⁻¹ • gradient ψ (s⁻¹ • x) := by
  have hd : HasGradientAt ψ (gradient ψ (s⁻¹ • x)) (s⁻¹ • x) :=
    ((hψ.differentiable one_ne_zero) _).hasGradientAt
  rw [hasGradientAt_iff_hasFDerivAt] at hd
  have h1 : HasFDerivAt (fun y : Space n => s⁻¹ • y) (s⁻¹ • ContinuousLinearMap.id ℝ (Space n)) x :=
    (hasFDerivAt_id x).const_smul s⁻¹
  have h2 : HasGradientAt (fun y => ψ (s⁻¹ • y)) (s⁻¹ • gradient ψ (s⁻¹ • x)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (hd.comp x h1).congr_fderiv (by ext w; simp)
  exact h2.gradient

/-- The Laplacian of a dilation. -/
lemma lap_comp_smul {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (s : ℝ)
    (x : Space n) : lap (fun y => ψ (s⁻¹ • y)) x = (s⁻¹) ^ 2 * lap ψ (s⁻¹ • x) := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hg : gradient (fun y => ψ (s⁻¹ • y)) = fun y => s⁻¹ • gradient ψ (s⁻¹ • y) :=
    funext (gradient_comp_smul hψ1 s)
  have hG : Differentiable ℝ (gradient ψ) := (contDiff_gradient hψ).differentiable (by norm_num)
  have h1 : HasFDerivAt (fun y : Space n => s⁻¹ • y) (s⁻¹ • ContinuousLinearMap.id ℝ (Space n)) x :=
    (hasFDerivAt_id x).const_smul s⁻¹
  have h2 : HasFDerivAt (fun y => s⁻¹ • gradient ψ (s⁻¹ • y))
      (s⁻¹ • (fderiv ℝ (gradient ψ) (s⁻¹ • x)).comp (s⁻¹ • ContinuousLinearMap.id ℝ (Space n))) x :=
    ((hG _).hasFDerivAt.comp x h1).const_smul s⁻¹
  unfold lap
  rw [hg, divergence_eq_sum_inner, h2.fderiv, divergence_eq_sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, real_inner_smul_right]
  ring

/-! ### Step 1: the conormal datum is flat also at `0` -/

lemma neumann_flat (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) (hn : 0 < n) :
    ∀ N : ℕ, ∃ Cn : ℝ, ∀ x ∈ flatPiece n S.R, |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ Cn * ‖x‖ ^ N := by
  intro N
  obtain ⟨C1, hC1⟩ := hg 1
  obtain ⟨Cg, hCg⟩ := hg N
  set F : Space n → ℝ := fun x => ⟪S.A x (S.Dv x), ed n⟫_ℝ with hF
  -- the conormal datum vanishes at `0`, by continuity along a horizontal line
  have hval0 : F 0 = 0 := by
    set e : Space n := EuclideanSpace.single (Fin.castSucc ⟨0, hn⟩) 1 with he_def
    have he : ‖e‖ = 1 := by simp [e]
    have hev : vcoord e = 0 := by
      exact PiLp.single_eq_of_ne' (p := 2) (Fin.castSucc_ne_last _) _
    have hFc : ContinuousOn F (closedHalfBall n S.R) :=
      ((S.coeffs.contDiff_A.continuous.continuousOn).clm_apply S.Dv_continuousOn).inner
        continuousOn_const
    have h0mem : (0 : Space n) ∈ closedHalfBall n S.R := ⟨by simp [S.R_pos], by simp [vcoord]⟩
    have hlim : Tendsto (fun t : ℝ => t • e) (𝓝[>] 0) (𝓝[closedHalfBall n S.R] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => t • e) (𝓝 0) (𝓝 ((0 : ℝ) • e)) :=
          (continuous_id.smul continuous_const).tendsto 0
        rw [zero_smul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT S.R_pos] with t ht
        refine ⟨?_, ?_⟩
        · rw [norm_smul, he, mul_one, Real.norm_of_nonneg ht.1.le]
          exact ht.2
        · rw [vcoord_smul, hev, mul_zero]
    have hFt : Tendsto (fun t : ℝ => F (t • e)) (𝓝[>] 0) (𝓝 (F 0)) :=
      (hFc 0 h0mem).tendsto.comp hlim
    have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), |F (t • e)| ≤ C1 * t := by
      filter_upwards [Ioo_mem_nhdsGT S.R_pos] with t ht
      have hnorm : ‖t • e‖ = t := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg ht.1.le]
      have hmem : t • e ∈ flatPiece n S.R := by
        refine ⟨by rw [hnorm]; exact ht.2, ?_⟩
        rw [vcoord_smul, hev, mul_zero]
      have hne : t • e ≠ 0 := by
        intro h0
        have := congrArg norm h0
        rw [hnorm, norm_zero] at this
        linarith [ht.1]
      have h1 := hneu _ hmem hne
      rw [hnorm] at h1
      have h2 := hC1 t ht
      rw [pow_one] at h2
      exact h1.trans h2
    have hlim2 : Tendsto (fun t : ℝ => C1 * t) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => C1 * t) (𝓝 0) (𝓝 (C1 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := le_of_tendsto_of_tendsto hFt.abs hlim2 hbound
    exact abs_nonpos_iff.mp this
  refine ⟨max Cg 0, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · subst hx0
    change |F 0| ≤ _
    rw [hval0, abs_zero]
    positivity
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have h1 := hneu x hx hx0
    have h2 := hCg ‖x‖ ⟨hxpos, hx.1⟩
    have h3 : Cg * ‖x‖ ^ N ≤ max Cg 0 * ‖x‖ ^ N :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    exact h1.trans (h2.trans h3)

/-! ### Step 2: choice of the scales -/

/-- Doubling selection: if `f(r) > r^M` along a sequence `r → 0`, then there are arbitrarily
small scales at which `f` doubles in a controlled way and is not too small. -/
lemma exists_doubling_scale (f : ℝ → ℝ) (r₀ B : ℝ) (M : ℕ) (hM : 1 ≤ M) (hr₀ : 0 < r₀)
    (hr₀1 : r₀ ≤ 1) (hmono : ∀ a b, 0 < a → a ≤ b → b ≤ r₀ → f a ≤ f b) (hB : f r₀ ≤ B)
    (hfail : ∀ ε > 0, ∃ r ∈ Ioo 0 ε, r ^ M < f r) :
    ∃ s ∈ Ioc 0 (r₀ / 2), f (2 * s) ≤ 2 ^ (3 * M) * f s ∧ s ^ (2 * M) < f s := by
  by_contra hcon
  have hstep : ∀ t, 0 < t → t ≤ r₀ / 2 → t ^ (2 * M) < f t → 2 ^ (3 * M) * f t < f (2 * t) := by
    intro t ht1 ht2 hft
    by_contra h
    exact hcon ⟨t, ⟨ht1, ht2⟩, not_lt.mp h, hft⟩
  have hB1 : 0 < |B| + 1 := by positivity
  have hq : 0 < (r₀ / 2) ^ (3 * M) := by positivity
  set ε := min r₀ ((r₀ / 2) ^ (3 * M) / (|B| + 1)) with hε
  have hεpos : 0 < ε := lt_min hr₀ (div_pos hq hB1)
  obtain ⟨r, ⟨hr0, hrε⟩, hfr⟩ := hfail ε hεpos
  have hrr₀ : r < r₀ := lt_of_lt_of_le hrε (min_le_left _ _)
  have hr1 : r ≤ 1 := by linarith
  have hrB : r * (|B| + 1) < (r₀ / 2) ^ (3 * M) := by
    have := lt_of_lt_of_le hrε (min_le_right _ _)
    rwa [lt_div_iff₀ hB1] at this
  -- growth along the dyadic scales `2^k r`
  have hP : ∀ k : ℕ, (2 : ℝ) ^ k * r ≤ r₀ → ((2 : ℝ) ^ k) ^ (3 * M) * r ^ M < f (2 ^ k * r) := by
    intro k
    induction k with
    | zero => intro _; simpa using hfr
    | succ k ih =>
      intro hk
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have htle : (2 : ℝ) ^ k * r ≤ r₀ / 2 := by rw [pow_succ] at hk; linarith
      have ih' := ih (by linarith)
      have htpos : 0 < (2 : ℝ) ^ k * r := by positivity
      have hlow : ((2 : ℝ) ^ k * r) ^ (2 * M) < f (2 ^ k * r) := by
        refine lt_of_le_of_lt ?_ ih'
        rw [mul_pow]
        apply mul_le_mul
        · exact pow_le_pow_right₀ h2k (by omega)
        · exact pow_le_pow_of_le_one hr0.le hr1 (by omega)
        · positivity
        · positivity
      have h := hstep _ htpos htle hlow
      have e1 : (2 : ℝ) * (2 ^ k * r) = 2 ^ (k + 1) * r := by rw [pow_succ]; ring
      have e2 : ((2 : ℝ) ^ (k + 1)) ^ (3 * M) = 2 ^ (3 * M) * ((2 : ℝ) ^ k) ^ (3 * M) := by
        rw [pow_succ, mul_pow, mul_comm]
      rw [e1] at h
      rw [e2]
      have h2M : (0 : ℝ) < 2 ^ (3 * M) := by positivity
      calc 2 ^ (3 * M) * ((2 : ℝ) ^ k) ^ (3 * M) * r ^ M
          = 2 ^ (3 * M) * (((2 : ℝ) ^ k) ^ (3 * M) * r ^ M) := by ring
        _ < 2 ^ (3 * M) * f (2 ^ k * r) := mul_lt_mul_of_pos_left ih' h2M
        _ < f (2 ^ (k + 1) * r) := h
  -- the last dyadic scale below `r₀`
  have hex : ∃ k : ℕ, r₀ < (2 : ℝ) ^ k * r := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (r₀ / r) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, by rwa [div_lt_iff₀ hr0] at hk⟩
  classical
  set k₁ := Nat.find hex with hk₁
  have hk₁spec : r₀ < (2 : ℝ) ^ k₁ * r := Nat.find_spec hex
  have hk₁0 : k₁ ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hk₁spec
    linarith
  obtain ⟨k, hk⟩ : ∃ k, k₁ = k + 1 := Nat.exists_eq_succ_of_ne_zero hk₁0
  have hkle : (2 : ℝ) ^ k * r ≤ r₀ := by
    have := Nat.find_min hex (show k < k₁ by omega)
    exact not_lt.mp this
  have hklt : r₀ < 2 * ((2 : ℝ) ^ k * r) := by
    rw [hk, pow_succ] at hk₁spec
    linarith
  have hfk := hP k hkle
  have hfmono : f (2 ^ k * r) ≤ f r₀ := hmono _ _ (by positivity) hkle le_rfl
  -- comparison of the two bounds
  set a : ℝ := (2 : ℝ) ^ k with ha
  have ha0 : 0 < a := by positivity
  have h1 : (r₀ / 2) ^ (3 * M) < (a * r) ^ (3 * M) :=
    pow_lt_pow_left₀ (by linarith) (by positivity) (by omega)
  have h2 : (a * r) ^ (3 * M) = a ^ (3 * M) * r ^ M * r ^ (2 * M) := by
    rw [mul_pow, mul_assoc, ← pow_add]
    congr 2
    omega
  have h3 : r ^ (2 * M) ≤ r := pow_le_of_le_one hr0.le hr1 (by omega)
  have h4 : a ^ (3 * M) * r ^ M * r ^ (2 * M) ≤ a ^ (3 * M) * r ^ M * r :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : a ^ (3 * M) * r ^ M * r < f r₀ * r :=
    mul_lt_mul_of_pos_right (lt_of_lt_of_le hfk hfmono) hr0
  have h6 : f r₀ * r ≤ |B| * r := mul_le_mul_of_nonneg_right (hB.trans (le_abs_self B)) hr0.le
  nlinarith

lemma exists_scales (S : HalfBallSolution n) (M : ℕ) (hM : 1 ≤ M)
    (hfail : ∀ ε > 0, ∃ r ∈ Ioo 0 ε, r ^ M < E S r) :
    ∃ s : ℕ → ℝ, (∀ j, 0 < s j) ∧ (∀ j, 4 * s j ≤ S.R) ∧ (∀ j, s j ≤ 1) ∧
      Tendsto s atTop (𝓝 0) ∧ (∀ j, E S (2 * s j) ≤ 2 ^ (3 * M) * E S (s j)) ∧
      (∀ j, s j ^ (2 * M) < E S (s j)) := by
  have key : ∀ j : ℕ, ∃ t ∈ Ioc 0 (min (1 / ((j : ℝ) + 1)) (min 1 (S.R / 4)) / 2),
      E S (2 * t) ≤ 2 ^ (3 * M) * E S t ∧ t ^ (2 * M) < E S t := by
    intro j
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hR4 : 0 < S.R / 4 := by linarith [S.R_pos]
    set r₀ := min (1 / ((j : ℝ) + 1)) (min 1 (S.R / 4)) with hr₀
    have hr₀pos : 0 < r₀ := lt_min hj (lt_min one_pos hR4)
    have hr₀1 : r₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hr₀R : r₀ ≤ S.R / 4 := (min_le_right _ _).trans (min_le_right _ _)
    refine exists_doubling_scale (E S) r₀ (E S r₀) M hM hr₀pos hr₀1 ?_ le_rfl hfail
    intro a b _ hab hb
    exact E_mono S hab (by linarith [S.R_pos])
  choose s hs hdoub hlow using key
  refine ⟨s, fun j => (hs j).1, fun j => ?_, fun j => ?_, ?_, hdoub, hlow⟩
  · have h1 := (hs j).2
    have h2 : min (1 / ((j : ℝ) + 1)) (min 1 (S.R / 4)) ≤ S.R / 4 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith [S.R_pos]
  · have h1 := (hs j).2
    have h2 : min (1 / ((j : ℝ) + 1)) (min 1 (S.R / 4)) ≤ 1 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  · have hle : ∀ j, s j ≤ 1 / ((j : ℝ) + 1) := by
      intro j
      have h1 := (hs j).2
      have h2 : min (1 / ((j : ℝ) + 1)) (min 1 (S.R / 4)) ≤ 1 / ((j : ℝ) + 1) := min_le_left _ _
      have h3 : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    exact squeeze_zero (fun j => (hs j).1.le) hle tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### Step 3: the blow-up sequence -/

lemma isOpen_halfBall (r : ℝ) : IsOpen (halfBall n r) :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const F1.continuous_vcoord)

lemma smul_mem_closedHalfBall {s r : ℝ} (hs : 0 < s) {X : Space n}
    (hX : X ∈ closedHalfBall n r) : s • X ∈ closedHalfBall n (s * r) := by
  refine ⟨?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hs.le]
    exact mul_lt_mul_of_pos_left hX.1 hs
  · rw [vcoord_smul]
    exact mul_nonneg hs.le hX.2

lemma smul_mem_halfBall {s r : ℝ} (hs : 0 < s) {X : Space n}
    (hX : X ∈ halfBall n r) : s • X ∈ halfBall n (s * r) := by
  refine ⟨?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hs.le]
    exact mul_lt_mul_of_pos_left hX.1 hs
  · rw [vcoord_smul]
    exact mul_pos hs hX.2

lemma smul_halfBall {s : ℝ} (hs : 0 < s) (r : ℝ) : s • halfBall n r = halfBall n (s * r) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hs.ne']
  constructor
  · intro hx
    have := smul_mem_halfBall hs hx
    rwa [smul_inv_smul₀ hs.ne'] at this
  · intro hx
    have := smul_mem_halfBall (inv_pos.mpr hs) hx
    rwa [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul] at this

lemma finrank_space : Module.finrank ℝ (Space n) = n + 1 := finrank_euclideanSpace_fin

/-- Change of variables `x = sX` on half-balls. -/
lemma setIntegral_halfBall_comp_smul (f : Space n → ℝ) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    ∫ x in halfBall n r, f (s • x) = (s ^ (n + 1))⁻¹ * ∫ x in halfBall n (s * r), f x := by
  rw [Measure.setIntegral_comp_smul_of_pos _ f _ hs, smul_halfBall hs, finrank_space,
    smul_eq_mul]

lemma cst_sq (S : HalfBallSolution n) {s : ℝ} (hs : 0 < s) (hE : 0 < E S s) :
    cst S s ^ 2 = s ^ (n + 1) / E S s := by
  unfold cst
  rw [Real.sq_sqrt (div_nonneg (pow_nonneg hs.le _) hE.le)]

lemma integral_w_sq_eq (S : HalfBallSolution n) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hE : 0 < E S s) :
    ∫ x in halfBall n r, w S s x ^ 2 = E S (s * r) / E S s := by
  have h : ∀ x, w S s x ^ 2 = cst S s ^ 2 * S.v (s • x) ^ 2 := fun x => by
    unfold w; ring
  simp_rw [h]
  rw [integral_const_mul, setIntegral_halfBall_comp_smul (fun y => S.v y ^ 2) hs r, cst_sq S hs hE]
  unfold E
  have hsn : (0 : ℝ) < s ^ (n + 1) := pow_pos hs _
  field_simp

lemma continuousOn_w (S : HalfBallSolution n) {s : ℝ} (hs : 0 < s) (hsR : 2 * s ≤ S.R) :
    ContinuousOn (w S s) (closedHalfBall n 2) := by
  have hmaps : MapsTo (fun X : Space n => s • X) (closedHalfBall n 2) (closedHalfBall n S.R) :=
    fun X hX => closedHalfBall_mono (by linarith) (smul_mem_closedHalfBall hs hX)
  exact continuousOn_const.mul
    (S.v_continuousOn.comp
      (continuous_const_smul s : Continuous fun X : Space n => s • X).continuousOn hmaps)

lemma continuousOn_Dw (S : HalfBallSolution n) {s : ℝ} (hs : 0 < s) (hsR : 2 * s ≤ S.R) :
    ContinuousOn (Dw S s) (closedHalfBall n 2) := by
  have hmaps : MapsTo (fun X : Space n => s • X) (closedHalfBall n 2) (closedHalfBall n S.R) :=
    fun X hX => closedHalfBall_mono (by linarith) (smul_mem_closedHalfBall hs hX)
  exact (S.Dv_continuousOn.comp
    (continuous_const_smul s : Continuous fun X : Space n => s • X).continuousOn hmaps).const_smul
    (cst S s * s)

/-- In the open half-ball, `v` has gradient `Dv`. -/
lemma hasGradientAt_v (S : HalfBallSolution n) {x : Space n} (hx : x ∈ halfBall n S.R) :
    HasGradientAt S.v (S.Dv x) x := by
  have hd : DifferentiableAt ℝ S.v x :=
    (S.v_contDiffOn.differentiableOn (by norm_num)).differentiableAt
      ((isOpen_halfBall _).mem_nhds hx)
  rw [← S.gradient_eq _ hx]
  exact hd.hasGradientAt

lemma hasGradientAt_w (S : HalfBallSolution n) {s : ℝ} (hs : 0 < s) (hsR : 2 * s ≤ S.R) :
    ∀ x ∈ halfBall n 2, HasGradientAt (w S s) (Dw S s x) x := by
  intro x hx
  have hmem : s • x ∈ halfBall n S.R := halfBall_mono (by linarith) (smul_mem_halfBall hs hx)
  have hg := hasGradientAt_v S hmem
  rw [hasGradientAt_iff_hasFDerivAt] at hg ⊢
  have h1 : HasFDerivAt (fun X : Space n => s • X) (s • ContinuousLinearMap.id ℝ (Space n)) x :=
    (hasFDerivAt_id x).const_smul s
  have h2 := (hg.comp x h1).const_mul (cst S s)
  have heq : cst S s • ((InnerProductSpace.toDual ℝ (Space n)) (S.Dv (s • x))).comp
      (s • ContinuousLinearMap.id ℝ (Space n)) = InnerProductSpace.toDual ℝ (Space n) (Dw S s x) := by
    ext y
    simp [Dw]
    ring
  exact h2.congr_fderiv heq

/-! ### Green's formula on the half-space -/

lemma divergence_smul_field {f : Space n → ℝ} {V : Space n → Space n} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hV : DifferentiableAt ℝ V x) :
    divergence (fun y => f y • V y) x = ⟪gradient f x, V x⟫_ℝ + f x * divergence V x := by
  set b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ with hb
  have hd : HasFDerivAt (fun y => f y • V y)
      (f x • fderiv ℝ V x + (fderiv ℝ f x).smulRight (V x)) x :=
    hf.hasFDerivAt.smul hV.hasFDerivAt
  rw [divergence_eq_sum_inner, divergence_eq_sum_inner, ← hb, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_right, real_inner_smul_right,
    Finset.sum_add_distrib, Finset.mul_sum]
  have h : ∑ i, fderiv ℝ f x (b i) * ⟪b i, V x⟫_ℝ = ⟪gradient f x, V x⟫_ℝ := by
    have e : ∀ i, fderiv ℝ f x (b i) = ⟪gradient f x, b i⟫_ℝ := fun i => by
      show fderiv ℝ f x (b i) = ⟪(InnerProductSpace.toDual ℝ (Space n)).symm (fderiv ℝ f x), b i⟫_ℝ
      rw [InnerProductSpace.toDual_symm_apply]
    simp_rw [e]
    exact b.sum_inner_mul_inner _ _
  rw [← h]
  ring

lemma continuousAt_divergence {F : Space n → Space n} {x : Space n} (hF : ContDiffAt ℝ 1 F x) :
    ContinuousAt (divergence F) x := by
  have h1 : ContinuousAt (fderiv ℝ F) x := (hF.fderiv_right (m := 0) le_rfl).continuousAt
  have e : divergence F = fun y => ∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i,
      fderiv ℝ F y (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)⟫_ℝ :=
    funext (divergence_eq_sum_inner F)
  rw [e]
  exact tendsto_finsetSum _ fun i _ =>
    continuousAt_const.inner (h1.clm_apply continuousAt_const)

lemma measurable_divergence (F : Space n → Space n) : Measurable (divergence F) := by
  have e : divergence F = fun y => ∑ i, ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i,
      fderiv ℝ F y (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)⟫_ℝ :=
    funext (divergence_eq_sum_inner F)
  rw [e]
  refine Finset.measurable_sum _ fun i _ => ?_
  have hc : Continuous fun L : Space n →L[ℝ] Space n =>
      ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ i, L (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)⟫_ℝ :=
    continuous_const.inner (continuous_id.clm_apply continuous_const)
  exact hc.measurable.comp (measurable_fderiv ℝ F)

/-- Green's formula on `{t > 0}` for a field supported in `B_ρ`, `ρ < R`, which is `C¹` in the open
half-ball, continuous up to the flat boundary and has bounded divergence. -/
lemma green_halfSpace {R : ℝ} (F : Space n → Space n) {ρ : ℝ} (hρ : ρ < R)
    (hFs : ∀ x, ρ ≤ ‖x‖ → F x = 0) (hFc : ContinuousOn F (closedHalfBall n R))
    (hFd : ∀ x ∈ halfBall n R, ContDiffAt ℝ 1 F x)
    (M : ℝ) (hdivb : ∀ x ∈ halfBall n R, |divergence F x| ≤ M) :
    ∫ x in {x : Space n | 0 < vcoord x}, divergence F x = -∫ y, ⟪F (lift y 0), ed n⟫_ℝ := by
  have hloc0 : ∀ x : Space n, ρ < ‖x‖ → F =ᶠ[𝓝 x] fun _ => 0 := by
    intro x hx
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact hFs y (le_of_lt hy)
  have hF : ∀ x, 0 < vcoord x → ContDiffAt ℝ 1 F x := by
    intro x hx
    by_cases hxR : ‖x‖ < R
    · exact hFd x ⟨hxR, hx⟩
    · exact contDiffAt_const.congr_of_eventuallyEq (hloc0 x (by push Not at hxR; linarith))
  have hFc' : ContinuousOn F {x | 0 ≤ vcoord x} := by
    intro x hx
    by_cases hxR : ‖x‖ < R
    · have h1 : ContinuousWithinAt F (closedHalfBall n R) x := hFc x ⟨hxR, hx⟩
      have h2 : closedHalfBall n R = {x : Space n | 0 ≤ vcoord x} ∩ ball 0 R := by
        ext y
        simp only [closedHalfBall, Set.mem_ofPred_eq, Set.mem_inter_iff, mem_ball_zero_iff]
        tauto
      rw [h2] at h1
      exact (continuousWithinAt_inter (isOpen_ball.mem_nhds (by simpa using hxR))).mp h1
    · exact (continuousAt_const.congr
        (hloc0 x (by push Not at hxR; linarith)).symm).continuousWithinAt
  have hsupp : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space n) ρ) fun y hy => hFs y (by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      exact hy.le)
  have hdiv0 : ∀ x : Space n, ρ < ‖x‖ → divergence F x = 0 := by
    intro x hx
    unfold divergence
    rw [(hloc0 x hx).fderiv_eq]
    simp
  have hint : IntegrableOn (divergence F) {x | 0 < vcoord x} := by
    set s := {x : Space n | 0 < vcoord x} ∩ closedBall 0 ρ with hs_def
    have hsm : MeasurableSet s := (F1.measurableSet_halfSpace 0).inter measurableSet_closedBall
    have hs : volume s ≠ ⊤ :=
      ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
    have h1 : IntegrableOn (divergence F) s := by
      refine Measure.integrableOn_of_bounded hs (measurable_divergence F).aestronglyMeasurable
        (M := M) ?_
      rw [ae_restrict_iff' hsm]
      refine Eventually.of_forall fun x hx => ?_
      have hxn : ‖x‖ ≤ ρ := by simpa using hx.2
      rw [Real.norm_eq_abs]
      exact hdivb x ⟨by linarith, hx.1⟩
    refine h1.of_forall_sdiff_eq_zero (F1.measurableSet_halfSpace 0) fun x hx => ?_
    apply hdiv0
    by_contra h
    push Not at h
    exact hx.2 ⟨hx.1, by simpa using h⟩
  exact integral_divergence_halfSpace_of_continuousOn F hF hFc' hsupp hint

/-- The equation in divergence form. -/
lemma divergence_A_grad (S : HalfBallSolution n) {x : Space n} (hx : x ∈ halfBall n S.R) :
    divergence (fun y => S.A y (gradient S.v y)) x = -(⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) := by
  have h := S.eqn x hx
  unfold ellOp at h
  rw [S.gradient_eq x hx] at h
  linarith

/-! ### The two Green identities for the solution -/

lemma inner_gradient_eq_fderiv (g : Space n → ℝ) (x w : Space n) :
    ⟪gradient g x, w⟫_ℝ = fderiv ℝ g x w := by
  show ⟪(InnerProductSpace.toDual ℝ (Space n)).symm (fderiv ℝ g x), w⟫_ℝ = _
  exact InnerProductSpace.toDual_symm_apply

lemma inner_gradient_sq_mul {ζ f : Space n → ℝ} {x : Space n} (hζ : DifferentiableAt ℝ ζ x)
    (hf : DifferentiableAt ℝ f x) (W : Space n) :
    ⟪gradient (fun y => ζ y ^ 2 * f y) x, W⟫_ℝ =
      ζ x ^ 2 * ⟪gradient f x, W⟫_ℝ + 2 * ζ x * f x * ⟪gradient ζ x, W⟫_ℝ := by
  have h1 : HasFDerivAt (fun y => ζ y ^ 2) (((2 : ℕ) • ζ x ^ (2 - 1)) • fderiv ℝ ζ x) x :=
    hζ.hasFDerivAt.pow 2
  have h2 : HasFDerivAt (fun y => ζ y ^ 2 * f y)
      ((ζ x ^ 2) • fderiv ℝ f x + f x • (((2 : ℕ) • ζ x ^ (2 - 1)) • fderiv ℝ ζ x)) x :=
    h1.mul hf.hasFDerivAt
  rw [inner_gradient_eq_fderiv, inner_gradient_eq_fderiv, inner_gradient_eq_fderiv, h2.fderiv]
  simp
  ring

lemma contDiffAt_v (S : HalfBallSolution n) {x : Space n} (hx : x ∈ halfBall n S.R) :
    ContDiffAt ℝ 2 S.v x :=
  S.v_contDiffOn.contDiffAt ((isOpen_halfBall _).mem_nhds hx)

lemma contDiffAt_gradient_v (S : HalfBallSolution n) {x : Space n} (hx : x ∈ halfBall n S.R) :
    ContDiffAt ℝ 1 (gradient S.v) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ S.v) x := (contDiffAt_v S hx).fderiv_right (by norm_num)
  have h2 : gradient S.v = fun y => (InnerProductSpace.toDual ℝ (Space n)).symm (fderiv ℝ S.v y) := by
    funext y; rfl
  rw [h2]
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.contDiff.contDiffAt.comp x h1

lemma exists_bound_halfBall {f : Space n → ℝ} {ρ R : ℝ} (hρ : ρ < R)
    (hf : ContinuousOn f (closedHalfBall n R)) (hz : ∀ x, ρ < ‖x‖ → f x = 0) :
    ∃ M, ∀ x ∈ halfBall n R, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_halfBallLe (n := n) ρ).exists_bound_of_continuousOn
    (hf.mono (fun x hx => ⟨lt_of_le_of_lt hx.1 hρ, hx.2⟩))
  refine ⟨max M 0, fun x hx => ?_⟩
  by_cases h : ‖x‖ ≤ ρ
  · rw [← Real.norm_eq_abs]
    exact (hM x ⟨h, hx.2.le⟩).trans (le_max_left _ _)
  · rw [hz x (lt_of_not_ge h), abs_zero]
    exact le_max_right _ _

/-- The Caccioppoli identity: Green's formula for the field `ζ² v A Dv`. -/
lemma caccioppoli_identity (S : HalfBallSolution n) (ζ : Space n → ℝ) (hζ : ContDiff ℝ 2 ζ)
    {ρ : ℝ} (hρ : ρ < S.R) (hζs : ∀ x, ρ ≤ ‖x‖ → ζ x = 0) :
    ∫ x in {x : Space n | 0 < vcoord x}, (ζ x ^ 2 * ⟪S.A x (S.Dv x), S.Dv x⟫_ℝ
        + 2 * ζ x * S.v x * ⟪S.A x (S.Dv x), gradient ζ x⟫_ℝ
        - ζ x ^ 2 * S.v x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x))
      = -∫ y, ζ (lift y 0) ^ 2 * S.v (lift y 0) *
          ⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ := by
  set F : Space n → Space n := fun x => (ζ x ^ 2 * S.v x) • S.A x (S.Dv x) with hF
  set G : Space n → ℝ := fun x => ζ x ^ 2 * ⟪S.A x (S.Dv x), S.Dv x⟫_ℝ
        + 2 * ζ x * S.v x * ⟪S.A x (S.Dv x), gradient ζ x⟫_ℝ
        - ζ x ^ 2 * S.v x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) with hG
  have hζc : Continuous ζ := hζ.continuous
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by norm_num)
  have hζg : Continuous (gradient ζ) := (contDiff_gradient hζ).continuous
  have hAc : Continuous S.A := S.coeffs.contDiff_A.continuous
  have hFs : ∀ x, ρ ≤ ‖x‖ → F x = 0 := fun x hx => by simp [hF, hζs x hx]
  have hFc : ContinuousOn F (closedHalfBall n S.R) :=
    ((hζc.continuousOn.pow 2).mul S.v_continuousOn).smul
      (hAc.continuousOn.clm_apply S.Dv_continuousOn)
  have hloc : ∀ x ∈ halfBall n S.R,
      F =ᶠ[𝓝 x] fun y => (ζ y ^ 2 * S.v y) • S.A y (gradient S.v y) := by
    intro x hx
    filter_upwards [(isOpen_halfBall S.R).mem_nhds hx] with y hy
    simp only [hF, S.gradient_eq y hy]
  have hFd : ∀ x ∈ halfBall n S.R, ContDiffAt ℝ 1 F x := by
    intro x hx
    refine ContDiffAt.congr_of_eventuallyEq ?_ (hloc x hx)
    have hv1 : ContDiffAt ℝ 1 S.v x := (contDiffAt_v S hx).of_le (by norm_num)
    exact ((hζ1.contDiffAt.pow 2).mul hv1).smul
      ((S.coeffs.contDiff_A.contDiffAt.of_le (by norm_num)).clm_apply (contDiffAt_gradient_v S hx))
  have hdivF : ∀ x ∈ halfBall n S.R, divergence F x = G x := by
    intro x hx
    have e1 : divergence F x =
        divergence (fun y => (ζ y ^ 2 * S.v y) • S.A y (gradient S.v y)) x := by
      unfold divergence
      rw [(hloc x hx).fderiv_eq]
    have hvd : DifferentiableAt ℝ S.v x :=
      (contDiffAt_v S hx).differentiableAt (by norm_num)
    have hζd : DifferentiableAt ℝ ζ x := hζ1.differentiable one_ne_zero x
    have hd1 : DifferentiableAt ℝ (fun y => ζ y ^ 2 * S.v y) x := (hζd.pow 2).mul hvd
    have hd2 : DifferentiableAt ℝ (fun y => S.A y (gradient S.v y)) x :=
      ((S.coeffs.contDiff_A.differentiable (by norm_num)) x).clm_apply
        ((contDiffAt_gradient_v S hx).differentiableAt one_ne_zero)
    rw [e1, divergence_smul_field hd1 hd2, divergence_A_grad S hx,
      inner_gradient_sq_mul hζd hvd, S.gradient_eq x hx, hG]
    simp only
    rw [real_inner_comm (S.A x (S.Dv x)) (S.Dv x),
      real_inner_comm (S.A x (S.Dv x)) (gradient ζ x)]
    ring
  have hGc : ContinuousOn G (closedHalfBall n S.R) := by
    have hADv : ContinuousOn (fun x => S.A x (S.Dv x)) (closedHalfBall n S.R) :=
      hAc.continuousOn.clm_apply S.Dv_continuousOn
    exact (((hζc.continuousOn.pow 2).mul (hADv.inner S.Dv_continuousOn)).add
      (((continuousOn_const.mul hζc.continuousOn).mul S.v_continuousOn).mul
        (hADv.inner hζg.continuousOn))).sub
      (((hζc.continuousOn.pow 2).mul S.v_continuousOn).mul
        ((S.coeffs.cont_B.continuousOn.inner S.Dv_continuousOn).add
          (S.coeffs.cont_C.continuousOn.mul S.v_continuousOn)))
  have hGz : ∀ x, ρ < ‖x‖ → G x = 0 := fun x hx => by simp [hG, hζs x hx.le]
  obtain ⟨M, hM⟩ := exists_bound_halfBall hρ hGc hGz
  have hgreen := green_halfSpace F hρ hFs hFc hFd M (fun x hx => by rw [hdivF x hx]; exact hM x hx)
  have hcongr : ∫ x in {x : Space n | 0 < vcoord x}, G x =
      ∫ x in {x : Space n | 0 < vcoord x}, divergence F x := by
    refine setIntegral_congr_fun (F1.measurableSet_halfSpace 0) fun x hx => ?_
    by_cases hxR : ‖x‖ < S.R
    · exact (hdivF x ⟨hxR, hx⟩).symm
    · push Not at hxR
      have hxρ : ρ < ‖x‖ := by linarith
      have h0 : F =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxρ] with y hy
        exact hFs y hy.le
      have hdiv0 : divergence F x = 0 := by
        unfold divergence
        rw [h0.fderiv_eq]
        simp
      rw [hdiv0, hGz x hxρ]
  change ∫ x in {x : Space n | 0 < vcoord x}, G x = _
  rw [hcongr, hgreen]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hF, real_inner_smul_left]

lemma divergence_sub_field {V W : Space n → Space n} {x : Space n}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    divergence (fun y => V y - W y) x = divergence V x - divergence W x := by
  rw [divergence_eq_sum_inner, divergence_eq_sum_inner, divergence_eq_sum_inner,
    fderiv_fun_sub hV hW, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.sub_apply, inner_sub_right]

lemma gradient_eq_zero_of_norm_gt {ψ : Space n → ℝ} {ρ : ℝ} (hψs : ∀ x, ρ ≤ ‖x‖ → ψ x = 0)
    {x : Space n} (hx : ρ < ‖x‖) : gradient ψ x = 0 := by
  have h : ψ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact hψs y hy.le
  unfold gradient
  rw [h.fderiv_eq]
  simp

/-- Green's formula for the field `ψ A Dv - v ∇ψ`. -/
lemma green_lap_identity (S : HalfBallSolution n) (ψ : Space n → ℝ) (hψ : ContDiff ℝ 2 ψ)
    {ρ : ℝ} (hρ : ρ < S.R) (hψs : ∀ x, ρ ≤ ‖x‖ → ψ x = 0) :
    ∫ x in {x : Space n | 0 < vcoord x}, (⟪S.A x (S.Dv x), gradient ψ x⟫_ℝ
        - ψ x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) - ⟪S.Dv x, gradient ψ x⟫_ℝ
        - S.v x * lap ψ x)
      = -∫ y, (ψ (lift y 0) * ⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ
          - S.v (lift y 0) * ⟪gradient ψ (lift y 0), ed n⟫_ℝ) := by
  set ρ' := (ρ + S.R) / 2 with hρ'
  have hρρ' : ρ < ρ' := by rw [hρ']; linarith
  have hρ'R : ρ' < S.R := by rw [hρ']; linarith
  set F : Space n → Space n := fun x => ψ x • S.A x (S.Dv x) - S.v x • gradient ψ x with hF
  set G : Space n → ℝ := fun x => ⟪S.A x (S.Dv x), gradient ψ x⟫_ℝ
        - ψ x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) - ⟪S.Dv x, gradient ψ x⟫_ℝ
        - S.v x * lap ψ x with hG
  have hψc : Continuous ψ := hψ.continuous
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψg : ContDiff ℝ 1 (gradient ψ) := contDiff_gradient hψ
  have hAc : Continuous S.A := S.coeffs.contDiff_A.continuous
  have hFs : ∀ x, ρ' ≤ ‖x‖ → F x = 0 := fun x hx => by
    simp [hF, hψs x (by linarith), gradient_eq_zero_of_norm_gt hψs (by linarith : ρ < ‖x‖)]
  have hFc : ContinuousOn F (closedHalfBall n S.R) :=
    (hψc.continuousOn.smul (hAc.continuousOn.clm_apply S.Dv_continuousOn)).sub
      (S.v_continuousOn.smul hψg.continuous.continuousOn)
  have hloc : ∀ x ∈ halfBall n S.R,
      F =ᶠ[𝓝 x] fun y => ψ y • S.A y (gradient S.v y) - S.v y • gradient ψ y := by
    intro x hx
    filter_upwards [(isOpen_halfBall S.R).mem_nhds hx] with y hy
    simp only [hF, S.gradient_eq y hy]
  have hFd : ∀ x ∈ halfBall n S.R, ContDiffAt ℝ 1 F x := by
    intro x hx
    refine ContDiffAt.congr_of_eventuallyEq ?_ (hloc x hx)
    have hv1 : ContDiffAt ℝ 1 S.v x := (contDiffAt_v S hx).of_le (by norm_num)
    exact (hψ1.contDiffAt.smul
      ((S.coeffs.contDiff_A.contDiffAt.of_le (by norm_num)).clm_apply
        (contDiffAt_gradient_v S hx))).sub (hv1.smul hψg.contDiffAt)
  have hdivF : ∀ x ∈ halfBall n S.R, divergence F x = G x := by
    intro x hx
    have e1 : divergence F x =
        divergence (fun y => ψ y • S.A y (gradient S.v y) - S.v y • gradient ψ y) x := by
      unfold divergence
      rw [(hloc x hx).fderiv_eq]
    have hvd : DifferentiableAt ℝ S.v x :=
      (contDiffAt_v S hx).differentiableAt (by norm_num)
    have hψd : DifferentiableAt ℝ ψ x := hψ1.differentiable one_ne_zero x
    have hgψd : DifferentiableAt ℝ (gradient ψ) x := hψg.differentiable one_ne_zero x
    have hd2 : DifferentiableAt ℝ (fun y => S.A y (gradient S.v y)) x :=
      ((S.coeffs.contDiff_A.differentiable (by norm_num)) x).clm_apply
        ((contDiffAt_gradient_v S hx).differentiableAt one_ne_zero)
    rw [e1, divergence_sub_field (V := fun y => ψ y • S.A y (gradient S.v y))
      (W := fun y => S.v y • gradient ψ y) (hψd.smul hd2) (hvd.smul hgψd),
      divergence_smul_field hψd hd2, divergence_smul_field hvd hgψd, divergence_A_grad S hx,
      S.gradient_eq x hx, hG]
    simp only [lap]
    rw [real_inner_comm (S.A x (S.Dv x)) (gradient ψ x)]
    ring
  have hGc : ContinuousOn G (closedHalfBall n S.R) := by
    have hADv : ContinuousOn (fun x => S.A x (S.Dv x)) (closedHalfBall n S.R) :=
      hAc.continuousOn.clm_apply S.Dv_continuousOn
    exact (((hADv.inner hψg.continuous.continuousOn).sub
      (hψc.continuousOn.mul ((S.coeffs.cont_B.continuousOn.inner S.Dv_continuousOn).add
          (S.coeffs.cont_C.continuousOn.mul S.v_continuousOn)))).sub
      (S.Dv_continuousOn.inner hψg.continuous.continuousOn)).sub
      (S.v_continuousOn.mul (continuous_lap hψ).continuousOn)
  have hGz : ∀ x, ρ' < ‖x‖ → G x = 0 := fun x hx => by
    have h1 := gradient_eq_zero_of_norm_gt hψs (by linarith : ρ < ‖x‖)
    have h2 := lap_eq_zero_of_norm_gt hψs (by linarith : ρ < ‖x‖)
    have h3 := hψs x (by linarith)
    simp only [hG, h1, h2, h3, inner_zero_right, zero_mul, mul_zero, sub_zero]
  obtain ⟨M, hM⟩ := exists_bound_halfBall hρ'R hGc hGz
  have hgreen := green_halfSpace F hρ'R hFs hFc hFd M
    (fun x hx => by rw [hdivF x hx]; exact hM x hx)
  have hcongr : ∫ x in {x : Space n | 0 < vcoord x}, G x =
      ∫ x in {x : Space n | 0 < vcoord x}, divergence F x := by
    refine setIntegral_congr_fun (F1.measurableSet_halfSpace 0) fun x hx => ?_
    by_cases hxR : ‖x‖ < S.R
    · exact (hdivF x ⟨hxR, hx⟩).symm
    · push Not at hxR
      have hxρ : ρ' < ‖x‖ := by linarith
      have h0 : F =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxρ] with y hy
        exact hFs y hy.le
      have hdiv0 : divergence F x = 0 := by
        unfold divergence
        rw [h0.fderiv_eq]
        simp
      rw [hdiv0, hGz x hxρ]
  change ∫ x in {x : Space n | 0 < vcoord x}, G x = _
  rw [hcongr, hgreen]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hF, inner_sub_left, real_inner_smul_left]

lemma integrableOn_halfSpace_of_continuousOn {f : Space n → ℝ} {ρ R : ℝ} (hρ : ρ < R)
    (hf : ContinuousOn f (closedHalfBall n R)) (hz : ∀ x, ρ < ‖x‖ → f x = 0) :
    IntegrableOn f {x : Space n | 0 < vcoord x} := by
  have h1 : IntegrableOn f (halfBall n ((ρ + R) / 2)) :=
    integrableOn_halfBall_of_continuousOn (by linarith) hf
  refine h1.of_forall_sdiff_eq_zero (F1.measurableSet_halfSpace 0) fun x hx => hz x ?_
  by_contra h
  push Not at h
  exact hx.2 ⟨by linarith, hx.1⟩

/-- The flat boundary integral of a function bounded by `Bd` on `flatPiece n ρ` and vanishing
outside it is at most `ω ρⁿ Bd`, with `ω` the volume of the unit ball of `ℝⁿ`. -/
lemma abs_integral_flat_le {f : Space n → ℝ} {ρ Bd : ℝ} (hρ : 0 < ρ)
    (hbd : ∀ x ∈ flatPiece n ρ, |f x| ≤ Bd) (hz : ∀ x, ρ ≤ ‖x‖ → f x = 0) :
    |∫ y : EuclideanSpace ℝ (Fin n), f (lift y 0)| ≤
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * ρ ^ n * Bd := by
  have hint : Integrable ((ball (0 : EuclideanSpace ℝ (Fin n)) ρ).indicator fun _ => Bd) :=
    (integrableOn_const (measure_ball_lt_top).ne).integrable_indicator measurableSet_ball
  have hle : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖f (lift y 0)‖ ≤ (ball (0 : EuclideanSpace ℝ (Fin n)) ρ).indicator (fun _ => Bd) y := by
    intro y
    have hnorm : ‖lift y 0‖ = ‖y‖ := by
      have h := norm_lift_sq y 0
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero] at h
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
    by_cases hy : ‖y‖ < ρ
    · rw [Set.indicator_of_mem (by simpa using hy), Real.norm_eq_abs]
      exact hbd _ ⟨by rw [hnorm]; exact hy, by rw [vcoord_lift]⟩
    · rw [Set.indicator_of_notMem (by simpa using hy), hz _ (by rw [hnorm]; linarith), norm_zero]
  have h1 := norm_integral_le_of_norm_le hint (Eventually.of_forall hle)
  rw [integral_indicator_const _ measurableSet_ball, smul_eq_mul, Real.norm_eq_abs] at h1
  have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) ρ) =
      ρ ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    simp only [measureReal_def]
    rw [Measure.addHaar_ball_of_pos _ _ hρ, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ.le _)]
  rw [hvol] at h1
  linarith

/-- Caccioppoli's inequality up to the flat boundary, for a general cut-off. -/
lemma caccioppoli_ineq (S : HalfBallSolution n) : ∃ Cc : ℝ, 0 < Cc ∧
    ∀ (ζ : Space n → ℝ) (ρ₁ ρ L Bd : ℝ), ContDiff ℝ 2 ζ → 0 < ρ → ρ₁ < ρ → ρ < S.R →
      (∀ x, ρ₁ ≤ ‖x‖ → ζ x = 0) → (∀ x, |ζ x| ≤ 1) → (∀ x, ‖gradient ζ x‖ ≤ L) →
      (∀ x ∈ flatPiece n ρ, |S.v x * ⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ Bd) →
      ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * ‖S.Dv x‖ ^ 2 ≤
        Cc * ((L ^ 2 + 1) * E S ρ + ρ ^ n * Bd) := by
  set lam := S.lam with hlam_def
  set K := S.K with hK_def
  have hlam : 0 < lam := S.coeffs.lam_pos
  have hK : 0 ≤ K := (norm_nonneg _).trans (S.coeffs.bound_A 0)
  set w1 : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hw1_def
  have hw1 : 0 ≤ w1 := measureReal_nonneg
  set c₁ := 4 * K ^ 2 / lam with hc₁
  set c₂ := K ^ 2 / lam + K with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨2 / lam * (c₁ + c₂ + w1 + 1), by positivity, ?_⟩
  intro ζ ρ₁ ρ L Bd hζ hρ hρ₁ hρR hζs hζ1 hζL hBd
  have hBd0 : 0 ≤ Bd := by
    have h0 : (0 : Space n) ∈ flatPiece n ρ := ⟨by simpa using hρ, by simp [vcoord]⟩
    exact (abs_nonneg _).trans (hBd 0 h0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hζL 0)
  have hζc : Continuous ζ := hζ.continuous
  have hζg : Continuous (gradient ζ) := (contDiff_gradient hζ).continuous
  have hgz : ∀ x, ρ₁ < ‖x‖ → gradient ζ x = 0 := fun x hx => gradient_eq_zero_of_norm_gt hζs hx
  set P : Space n → ℝ := fun x => ζ x ^ 2 * ⟪S.A x (S.Dv x), S.Dv x⟫_ℝ
        + 2 * ζ x * S.v x * ⟪S.A x (S.Dv x), gradient ζ x⟫_ℝ
        - ζ x ^ 2 * S.v x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) with hP
  -- the pointwise inequality
  have hpt : ∀ x, lam / 2 * (ζ x ^ 2 * ‖S.Dv x‖ ^ 2) ≤
      P x + c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2) + c₂ * (ζ x ^ 2 * S.v x ^ 2) := by
    intro x
    set a := |ζ x| * ‖S.Dv x‖ with ha
    set b := |S.v x| * ‖gradient ζ x‖ with hb
    set c := |ζ x| * |S.v x| with hc
    have ea : a ^ 2 = ζ x ^ 2 * ‖S.Dv x‖ ^ 2 := by rw [ha, mul_pow, sq_abs]
    have eb : b ^ 2 = S.v x ^ 2 * ‖gradient ζ x‖ ^ 2 := by rw [hb, mul_pow, sq_abs]
    have ec : c ^ 2 = ζ x ^ 2 * S.v x ^ 2 := by rw [hc, mul_pow, sq_abs, sq_abs]
    have ha0 : 0 ≤ a := by positivity
    have hb0 : 0 ≤ b := by positivity
    have hc0 : 0 ≤ c := by positivity
    have h1 : lam * a ^ 2 ≤ ζ x ^ 2 * ⟪S.A x (S.Dv x), S.Dv x⟫_ℝ := by
      have := S.coeffs.ell x (S.Dv x)
      rw [ea]
      have hz2 : 0 ≤ ζ x ^ 2 := sq_nonneg _
      calc lam * (ζ x ^ 2 * ‖S.Dv x‖ ^ 2) = ζ x ^ 2 * (lam * ‖S.Dv x‖ ^ 2) := by ring
        _ ≤ ζ x ^ 2 * ⟪S.A x (S.Dv x), S.Dv x⟫_ℝ := mul_le_mul_of_nonneg_left this hz2
    have hADv : ‖S.A x (S.Dv x)‖ ≤ K * ‖S.Dv x‖ :=
      (S.A x).le_of_opNorm_le (S.coeffs.bound_A x) _
    have h2 : |2 * ζ x * S.v x * ⟪S.A x (S.Dv x), gradient ζ x⟫_ℝ| ≤ 2 * K * a * b := by
      have hi := abs_real_inner_le_norm (S.A x (S.Dv x)) (gradient ζ x)
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      calc 2 * |ζ x| * |S.v x| * |⟪S.A x (S.Dv x), gradient ζ x⟫_ℝ|
          ≤ 2 * |ζ x| * |S.v x| * (K * ‖S.Dv x‖ * ‖gradient ζ x‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hi.trans (mul_le_mul_of_nonneg_right hADv (norm_nonneg _))
        _ = 2 * K * a * b := by rw [ha, hb]; ring
    have h3 : |ζ x ^ 2 * S.v x * ⟪S.B x, S.Dv x⟫_ℝ| ≤ K * a * c := by
      have hi := abs_real_inner_le_norm (S.B x) (S.Dv x)
      rw [abs_mul, abs_mul, abs_pow]
      calc |ζ x| ^ 2 * |S.v x| * |⟪S.B x, S.Dv x⟫_ℝ|
          ≤ |ζ x| ^ 2 * |S.v x| * (K * ‖S.Dv x‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hi.trans (mul_le_mul_of_nonneg_right (S.coeffs.bound_B x) (norm_nonneg _))
        _ = K * a * c := by rw [ha, hc]; ring
    have h4 : |ζ x ^ 2 * S.v x * (S.C x * S.v x)| ≤ K * c ^ 2 := by
      rw [show ζ x ^ 2 * S.v x * (S.C x * S.v x) = S.C x * (ζ x ^ 2 * S.v x ^ 2) by ring,
        abs_mul, ← ec, abs_of_nonneg (sq_nonneg c)]
      exact mul_le_mul_of_nonneg_right (S.coeffs.bound_C x) (sq_nonneg c)
    have key : lam / 2 * a ^ 2 ≤
        lam * a ^ 2 - 2 * K * a * b - K * a * c - K * c ^ 2 + c₁ * b ^ 2 + c₂ * c ^ 2 := by
      have e : lam * (lam * a ^ 2 - 2 * K * a * b - K * a * c - K * c ^ 2 + c₁ * b ^ 2
          + c₂ * c ^ 2 - lam / 2 * a ^ 2) =
          (lam * a / 2 - 2 * K * b) ^ 2 + (lam * a / 2 - K * c) ^ 2 := by
        rw [hc₁, hc₂]
        field_simp
        ring
      have hnn : 0 ≤ lam * a ^ 2 - 2 * K * a * b - K * a * c - K * c ^ 2 + c₁ * b ^ 2
          + c₂ * c ^ 2 - lam / 2 * a ^ 2 := by
        by_contra h
        push Not at h
        have := mul_neg_of_pos_of_neg hlam h
        rw [e] at this
        linarith [sq_nonneg (lam * a / 2 - 2 * K * b), sq_nonneg (lam * a / 2 - K * c)]
      linarith
    have eP : P x = ζ x ^ 2 * ⟪S.A x (S.Dv x), S.Dv x⟫_ℝ
        + 2 * ζ x * S.v x * ⟪S.A x (S.Dv x), gradient ζ x⟫_ℝ
        - ζ x ^ 2 * S.v x * ⟪S.B x, S.Dv x⟫_ℝ - ζ x ^ 2 * S.v x * (S.C x * S.v x) := by
      rw [hP]; ring
    rw [← ea, ← eb, ← ec, eP]
    have h2' := neg_abs_le (2 * ζ x * S.v x * ⟪S.A x (S.Dv x), gradient ζ x⟫_ℝ)
    have h3' := le_abs_self (ζ x ^ 2 * S.v x * ⟪S.B x, S.Dv x⟫_ℝ)
    have h4' := le_abs_self (ζ x ^ 2 * S.v x * (S.C x * S.v x))
    linarith
  -- integrability
  have hADc : ContinuousOn (fun x => S.A x (S.Dv x)) (closedHalfBall n S.R) :=
    S.coeffs.contDiff_A.continuous.continuousOn.clm_apply S.Dv_continuousOn
  have iL : IntegrableOn (fun x => ζ x ^ 2 * ‖S.Dv x‖ ^ 2) {x : Space n | 0 < vcoord x} :=
    integrableOn_halfSpace_of_continuousOn (hρ₁.trans hρR)
      ((hζc.continuousOn.pow 2).mul (S.Dv_continuousOn.norm.pow 2))
      (fun x hx => by simp [hζs x hx.le])
  have iP : IntegrableOn P {x : Space n | 0 < vcoord x} :=
    integrableOn_halfSpace_of_continuousOn (hρ₁.trans hρR)
      ((((hζc.continuousOn.pow 2).mul (hADc.inner S.Dv_continuousOn)).add
        (((continuousOn_const.mul hζc.continuousOn).mul S.v_continuousOn).mul
          (hADc.inner hζg.continuousOn))).sub
        (((hζc.continuousOn.pow 2).mul S.v_continuousOn).mul
          ((S.coeffs.cont_B.continuousOn.inner S.Dv_continuousOn).add
            (S.coeffs.cont_C.continuousOn.mul S.v_continuousOn))))
      (fun x hx => by simp [hP, hζs x hx.le])
  have ib : IntegrableOn (fun x => S.v x ^ 2 * ‖gradient ζ x‖ ^ 2) {x : Space n | 0 < vcoord x} :=
    integrableOn_halfSpace_of_continuousOn (hρ₁.trans hρR)
      ((S.v_continuousOn.pow 2).mul (hζg.continuousOn.norm.pow 2))
      (fun x hx => by simp [hgz x hx])
  have ic : IntegrableOn (fun x => ζ x ^ 2 * S.v x ^ 2) {x : Space n | 0 < vcoord x} :=
    integrableOn_halfSpace_of_continuousOn (hρ₁.trans hρR)
      ((hζc.continuousOn.pow 2).mul (S.v_continuousOn.pow 2))
      (fun x hx => by simp [hζs x hx.le])
  -- integrate the pointwise inequality
  have hint1 : lam / 2 * ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * ‖S.Dv x‖ ^ 2 ≤
      (∫ x in {x : Space n | 0 < vcoord x}, P x) +
        c₁ * (∫ x in {x : Space n | 0 < vcoord x}, S.v x ^ 2 * ‖gradient ζ x‖ ^ 2) +
        c₂ * ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * S.v x ^ 2 := by
    have i1 : IntegrableOn (fun x => P x + c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2))
        {x : Space n | 0 < vcoord x} := iP.add (ib.const_mul c₁)
    have i2 : IntegrableOn (fun x => c₂ * (ζ x ^ 2 * S.v x ^ 2)) {x : Space n | 0 < vcoord x} :=
      ic.const_mul c₂
    have i3 : IntegrableOn (fun x => c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2))
        {x : Space n | 0 < vcoord x} := ib.const_mul c₁
    have hm' : ∫ x in {x : Space n | 0 < vcoord x}, lam / 2 * (ζ x ^ 2 * ‖S.Dv x‖ ^ 2) ≤
        ∫ x in {x : Space n | 0 < vcoord x}, (P x + c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2)
          + c₂ * (ζ x ^ 2 * S.v x ^ 2)) :=
      integral_mono (iL.const_mul (lam / 2)) (i1.add i2) hpt
    have e1 : ∫ x in {x : Space n | 0 < vcoord x}, lam / 2 * (ζ x ^ 2 * ‖S.Dv x‖ ^ 2) =
        lam / 2 * ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * ‖S.Dv x‖ ^ 2 :=
      integral_const_mul _ _
    have e2 : ∫ x in {x : Space n | 0 < vcoord x}, (P x + c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2)
          + c₂ * (ζ x ^ 2 * S.v x ^ 2)) =
        (∫ x in {x : Space n | 0 < vcoord x}, (P x + c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2))) +
          ∫ x in {x : Space n | 0 < vcoord x}, c₂ * (ζ x ^ 2 * S.v x ^ 2) :=
      integral_add i1 i2
    have e3 : ∫ x in {x : Space n | 0 < vcoord x}, (P x + c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2)) =
        (∫ x in {x : Space n | 0 < vcoord x}, P x) +
          ∫ x in {x : Space n | 0 < vcoord x}, c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2) :=
      integral_add iP i3
    have e4 : ∫ x in {x : Space n | 0 < vcoord x}, c₁ * (S.v x ^ 2 * ‖gradient ζ x‖ ^ 2) =
        c₁ * ∫ x in {x : Space n | 0 < vcoord x}, S.v x ^ 2 * ‖gradient ζ x‖ ^ 2 :=
      integral_const_mul _ _
    have e5 : ∫ x in {x : Space n | 0 < vcoord x}, c₂ * (ζ x ^ 2 * S.v x ^ 2) =
        c₂ * ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * S.v x ^ 2 :=
      integral_const_mul _ _
    linarith
  -- the three right-hand terms
  have hPint : ∫ x in {x : Space n | 0 < vcoord x}, P x ≤ w1 * ρ ^ n * Bd := by
    have hid := caccioppoli_identity S ζ hζ (hρ₁.trans hρR) hζs
    change ∫ x in {x : Space n | 0 < vcoord x}, P x = _ at hid
    rw [hid]
    have hflat := abs_integral_flat_le (f := fun x => ζ x ^ 2 * S.v x *
        ⟪S.A x (S.Dv x), ed n⟫_ℝ) hρ (Bd := Bd) (fun x hx => by
          rw [mul_assoc, abs_mul, abs_of_nonneg (sq_nonneg _)]
          have hz2 : ζ x ^ 2 ≤ 1 := by
            have := hζ1 x
            rw [← sq_abs]
            exact pow_le_one₀ (abs_nonneg _) this
          calc ζ x ^ 2 * |S.v x * ⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ 1 * Bd :=
                mul_le_mul hz2 (hBd x hx) (abs_nonneg _) zero_le_one
            _ = Bd := one_mul _)
        (fun x hx => by simp [hζs x (by linarith)])
    have := neg_abs_le (∫ y : EuclideanSpace ℝ (Fin n), ζ (lift y 0) ^ 2 * S.v (lift y 0) *
      ⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ)
    linarith
  have hEint : ∀ (g : Space n → ℝ) (k : ℝ), 0 ≤ k → (∀ x, 0 < vcoord x →
      g x ≤ k * (halfBall n ρ).indicator (fun y => S.v y ^ 2) x) →
      IntegrableOn g {x : Space n | 0 < vcoord x} →
      ∫ x in {x : Space n | 0 < vcoord x}, g x ≤ k * E S ρ := by
    intro g k hk hg hgi
    have hii : IntegrableOn ((halfBall n ρ).indicator (fun y => S.v y ^ 2))
        {x : Space n | 0 < vcoord x} :=
      ((integrableOn_halfBall_of_continuousOn hρR (S.v_continuousOn.pow 2)).integrable_indicator
        (measurableSet_halfBall ρ)).integrableOn
    calc ∫ x in {x : Space n | 0 < vcoord x}, g x
        ≤ ∫ x in {x : Space n | 0 < vcoord x},
            k * (halfBall n ρ).indicator (fun y => S.v y ^ 2) x :=
          setIntegral_mono_on hgi (hii.const_mul k) (F1.measurableSet_halfSpace 0) hg
      _ = k * E S ρ := by
          rw [integral_const_mul, setIntegral_indicator (measurableSet_halfBall ρ)]
          unfold E
          congr 2
          rw [Set.inter_eq_right.mpr (fun x (hx : x ∈ halfBall n ρ) => hx.2)]
  have hbint : ∫ x in {x : Space n | 0 < vcoord x}, S.v x ^ 2 * ‖gradient ζ x‖ ^ 2 ≤
      L ^ 2 * E S ρ := by
    refine hEint _ _ (sq_nonneg L) (fun x hx => ?_) ib
    by_cases hxρ : ‖x‖ < ρ
    · rw [Set.indicator_of_mem (show x ∈ halfBall n ρ from ⟨hxρ, hx⟩)]
      have h2 : ‖gradient ζ x‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hζL x) 2
      calc S.v x ^ 2 * ‖gradient ζ x‖ ^ 2 ≤ S.v x ^ 2 * L ^ 2 :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = L ^ 2 * S.v x ^ 2 := mul_comm _ _
    · rw [Set.indicator_of_notMem (fun (h : x ∈ halfBall n ρ) => hxρ h.1),
        hgz x (by push Not at hxρ; linarith)]
      simp
  have hcint : ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * S.v x ^ 2 ≤ 1 * E S ρ := by
    refine hEint _ _ zero_le_one (fun x hx => ?_) ic
    by_cases hxρ : ‖x‖ < ρ
    · rw [Set.indicator_of_mem (show x ∈ halfBall n ρ from ⟨hxρ, hx⟩), one_mul]
      have hz2 : ζ x ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hζ1 x)
      calc ζ x ^ 2 * S.v x ^ 2 ≤ 1 * S.v x ^ 2 := mul_le_mul_of_nonneg_right hz2 (sq_nonneg _)
        _ = S.v x ^ 2 := one_mul _
    · rw [Set.indicator_of_notMem (fun (h : x ∈ halfBall n ρ) => hxρ h.1),
        hζs x (by push Not at hxρ; linarith)]
      simp
  have hE0 : 0 ≤ E S ρ := E_nonneg S ρ
  have hb' : c₁ * (∫ x in {x : Space n | 0 < vcoord x}, S.v x ^ 2 * ‖gradient ζ x‖ ^ 2) ≤
      c₁ * (L ^ 2 * E S ρ) := mul_le_mul_of_nonneg_left hbint hc₁0
  have hc' : c₂ * (∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * S.v x ^ 2) ≤
      c₂ * (1 * E S ρ) := mul_le_mul_of_nonneg_left hcint hc₂0
  set I := ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * ‖S.Dv x‖ ^ 2 with hI
  have hX : lam / 2 * I ≤ w1 * ρ ^ n * Bd + c₁ * (L ^ 2 * E S ρ) + c₂ * (1 * E S ρ) := by
    linarith
  have hY : I ≤ 2 / lam * (w1 * ρ ^ n * Bd + c₁ * (L ^ 2 * E S ρ) + c₂ * (1 * E S ρ)) := by
    have h := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 2 / lam)
    have e : 2 / lam * (lam / 2 * I) = I := by field_simp
    linarith
  refine hY.trans ?_
  rw [mul_assoc (2 / lam)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hρn : 0 ≤ ρ ^ n * Bd := by positivity
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hexp : (c₁ + c₂ + w1 + 1) * ((L ^ 2 + 1) * E S ρ + ρ ^ n * Bd) -
      (w1 * ρ ^ n * Bd + c₁ * (L ^ 2 * E S ρ) + c₂ * (1 * E S ρ)) =
      c₁ * E S ρ + c₂ * (L ^ 2 * E S ρ) + w1 * (L ^ 2 * E S ρ) + w1 * E S ρ + L ^ 2 * E S ρ
        + E S ρ + c₁ * (ρ ^ n * Bd) + c₂ * (ρ ^ n * Bd) + ρ ^ n * Bd := by ring
  have t1 := mul_nonneg hc₁0 hE0
  have t2 := mul_nonneg hc₂0 (mul_nonneg hL2 hE0)
  have t3 := mul_nonneg hw1 (mul_nonneg hL2 hE0)
  have t4 := mul_nonneg hw1 hE0
  have t5 := mul_nonneg hL2 hE0
  have t6 := mul_nonneg hc₁0 hρn
  have t7 := mul_nonneg hc₂0 hρn
  linarith

/-- Caccioppoli's inequality on half-balls (radial cut-off equal to `1` on `B_{3ρ/2}` and
supported in `B_{7ρ/4}`). -/
lemma caccioppoli_ball (S : HalfBallSolution n) : ∃ Cc : ℝ, 0 < Cc ∧
    ∀ ρ Bd : ℝ, 0 < ρ → 2 * ρ < S.R →
      (∀ x ∈ flatPiece n (2 * ρ), |S.v x * ⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ Bd) →
      ∫ x in halfBall n (3 / 2 * ρ), ‖S.Dv x‖ ^ 2 ≤
        Cc * ((ρ⁻¹ ^ 2 + 1) * E S (2 * ρ) + ρ ^ n * Bd) := by
  obtain ⟨C0, hC0, hineq⟩ := caccioppoli_ineq S
  let χ : ContDiffBump (0 : Space n) := ⟨3 / 2, 7 / 4, by norm_num, by norm_num⟩
  have hχ2 : ContDiff ℝ 2 χ := χ.contDiff
  have hχ0 : ∀ x : Space n, 7 / 4 ≤ ‖x‖ → χ x = 0 := fun x hx =>
    χ.zero_of_le_dist (by rw [dist_zero_right]; exact hx)
  have hχgc : Continuous (gradient χ) := (contDiff_gradient hχ2).continuous
  have hχgs : HasCompactSupport (gradient χ) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space n) 2) fun x hx => by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact gradient_eq_zero_of_norm_gt hχ0 (by linarith)
  obtain ⟨Lχ, hLχ⟩ := hχgc.bounded_above_of_compact_support hχgs
  set L' := max Lχ 1 with hL'
  have hL'1 : 1 ≤ L' := le_max_right _ _
  refine ⟨C0 * (L' ^ 2 + 1) * 2 ^ n, by positivity, fun ρ Bd hρ hρR hBd => ?_⟩
  have hBd0 : 0 ≤ Bd := by
    have h0 : (0 : Space n) ∈ flatPiece n (2 * ρ) := ⟨by simp; linarith, by simp [vcoord]⟩
    exact (abs_nonneg _).trans (hBd 0 h0)
  set ζ : Space n → ℝ := fun x => χ (ρ⁻¹ • x) with hζ
  have hζ2 : ContDiff ℝ 2 ζ := hχ2.comp (contDiff_const_smul _)
  have hnorm : ∀ x : Space n, ‖ρ⁻¹ • x‖ = ρ⁻¹ * ‖x‖ := fun x => by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
  have hζs : ∀ x, 7 / 4 * ρ ≤ ‖x‖ → ζ x = 0 := by
    intro x hx
    apply hχ0
    rw [hnorm]
    rw [le_inv_mul_iff₀ hρ]
    linarith
  have hζ1 : ∀ x, |ζ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg χ.nonneg]
    exact χ.le_one
  have hζL : ∀ x, ‖gradient ζ x‖ ≤ ρ⁻¹ * Lχ := by
    intro x
    rw [hζ, gradient_comp_smul (hχ2.of_le (by norm_num)) ρ x, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
    exact mul_le_mul_of_nonneg_left (hLχ _) (inv_nonneg.mpr hρ.le)
  have hζone : ∀ x, ‖x‖ ≤ 3 / 2 * ρ → ζ x = 1 := by
    intro x hx
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
    rw [inv_mul_le_iff₀ hρ]
    show ‖x‖ ≤ ρ * (3 / 2)
    linarith
  have h := hineq ζ (7 / 4 * ρ) (2 * ρ) (ρ⁻¹ * Lχ) Bd hζ2 (by positivity) (by linarith) hρR
    hζs hζ1 hζL hBd
  have hint : IntegrableOn (fun x => ζ x ^ 2 * ‖S.Dv x‖ ^ 2) {x : Space n | 0 < vcoord x} := by
    refine integrableOn_halfSpace_of_continuousOn (ρ := 7 / 4 * ρ) (R := S.R) (by linarith) ?_ ?_
    · exact (hζ2.continuous.continuousOn.pow 2).mul (S.Dv_continuousOn.norm.pow 2)
    · intro x hx
      simp [hζs x hx.le]
  have hmono : ∫ x in halfBall n (3 / 2 * ρ), ‖S.Dv x‖ ^ 2 ≤
      ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * ‖S.Dv x‖ ^ 2 := by
    calc ∫ x in halfBall n (3 / 2 * ρ), ‖S.Dv x‖ ^ 2
        = ∫ x in halfBall n (3 / 2 * ρ), ζ x ^ 2 * ‖S.Dv x‖ ^ 2 := by
          refine setIntegral_congr_fun (measurableSet_halfBall _) fun x hx => ?_
          rw [hζone x hx.1.le, one_pow, one_mul]
      _ ≤ ∫ x in {x : Space n | 0 < vcoord x}, ζ x ^ 2 * ‖S.Dv x‖ ^ 2 := by
          apply setIntegral_mono_set hint
          · exact Eventually.of_forall fun x => by positivity
          · exact ae_of_all _ fun x (hx : x ∈ halfBall n (3 / 2 * ρ)) => hx.2
  refine hmono.trans (h.trans ?_)
  have hE0 : 0 ≤ E S (2 * ρ) := E_nonneg S _
  have hρinv : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρ.le
  have hLχ0 : 0 ≤ Lχ := (norm_nonneg _).trans (hLχ 0)
  have hLL : Lχ ≤ L' := le_max_left _ _
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have e1 : (ρ⁻¹ * Lχ) ^ 2 + 1 ≤ (L' ^ 2 + 1) * (ρ⁻¹ ^ 2 + 1) := by
    have : (ρ⁻¹ * Lχ) ^ 2 ≤ ρ⁻¹ ^ 2 * L' ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLχ0 hLL 2) (by positivity)
    nlinarith [sq_nonneg ρ⁻¹, sq_nonneg L']
  have e2 : (2 * ρ) ^ n * Bd = 2 ^ n * (ρ ^ n * Bd) := by rw [mul_pow]; ring
  rw [e2]
  have hA : 0 ≤ (ρ⁻¹ ^ 2 + 1) * E S (2 * ρ) := by positivity
  have hB : 0 ≤ ρ ^ n * Bd := by positivity
  calc C0 * (((ρ⁻¹ * Lχ) ^ 2 + 1) * E S (2 * ρ) + 2 ^ n * (ρ ^ n * Bd))
      ≤ C0 * ((L' ^ 2 + 1) * 2 ^ n * ((ρ⁻¹ ^ 2 + 1) * E S (2 * ρ)) +
          (L' ^ 2 + 1) * 2 ^ n * (ρ ^ n * Bd)) := by
        apply mul_le_mul_of_nonneg_left _ hC0.le
        have hk : 1 ≤ (L' ^ 2 + 1) := by nlinarith
        have hk2 : 1 ≤ (L' ^ 2 + 1) * 2 ^ n := by nlinarith
        apply add_le_add
        · calc ((ρ⁻¹ * Lχ) ^ 2 + 1) * E S (2 * ρ)
              ≤ ((L' ^ 2 + 1) * (ρ⁻¹ ^ 2 + 1)) * E S (2 * ρ) :=
                mul_le_mul_of_nonneg_right e1 hE0
            _ ≤ (L' ^ 2 + 1) * 2 ^ n * ((ρ⁻¹ ^ 2 + 1) * E S (2 * ρ)) := by
                have : (L' ^ 2 + 1) * (ρ⁻¹ ^ 2 + 1) * E S (2 * ρ)
                    = (L' ^ 2 + 1) * 1 * ((ρ⁻¹ ^ 2 + 1) * E S (2 * ρ)) := by ring
                rw [this]
                apply mul_le_mul_of_nonneg_right _ hA
                exact mul_le_mul_of_nonneg_left h2n (by positivity)
        · have h3 : 0 ≤ 2 ^ n * (ρ ^ n * Bd) := by positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hk) h3]
    _ = C0 * (L' ^ 2 + 1) * 2 ^ n * ((ρ⁻¹ ^ 2 + 1) * E S (2 * ρ) + ρ ^ n * Bd) := by ring

/-- The estimate behind the asymptotic harmonicity: Green's formula, `|A(x) - I| ≤ K |x|` and
the bounds on `B`, `C`. -/
lemma abs_integral_v_lap_le (S : HalfBallSolution n) : ∃ Cl : ℝ, 0 < Cl ∧
    ∀ (ψ : Space n → ℝ) (ρ₁ ρ L0 L1 Bd : ℝ), ContDiff ℝ 2 ψ → 0 < ρ₁ → ρ₁ < ρ → ρ < S.R →
      (∀ x, ρ₁ ≤ ‖x‖ → ψ x = 0) → (∀ x, |ψ x| ≤ L0) → (∀ x, ‖gradient ψ x‖ ≤ L1) →
      (∀ x ∈ flatPiece n ρ,
        |ψ x * ⟪S.A x (S.Dv x), ed n⟫_ℝ - S.v x * ⟪gradient ψ x, ed n⟫_ℝ| ≤ Bd) →
      |∫ x in {x : Space n | 0 < vcoord x}, S.v x * lap ψ x| ≤
        Cl * ((ρ * L1 + L0) * (∫ x in halfBall n ρ, (‖S.Dv x‖ + |S.v x|)) + ρ ^ n * Bd) := by
  set K := S.K with hK_def
  have hK : 0 ≤ K := (norm_nonneg _).trans (S.coeffs.bound_A 0)
  set w1 : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hw1_def
  have hw1 : 0 ≤ w1 := measureReal_nonneg
  refine ⟨K + w1 + 1, by positivity, ?_⟩
  intro ψ ρ₁ ρ L0 L1 Bd hψ hρ₁0 hρ₁ hρR hψs hψ0 hψ1 hBd
  have hρ : 0 < ρ := hρ₁0.trans hρ₁
  have hBd0 : 0 ≤ Bd := by
    have h0 : (0 : Space n) ∈ flatPiece n ρ := ⟨by simpa using hρ, by simp [vcoord]⟩
    exact (abs_nonneg _).trans (hBd 0 h0)
  have hL0 : 0 ≤ L0 := (abs_nonneg _).trans (hψ0 0)
  have hL1 : 0 ≤ L1 := (norm_nonneg _).trans (hψ1 0)
  have hψc : Continuous ψ := hψ.continuous
  have hψg : Continuous (gradient ψ) := (contDiff_gradient hψ).continuous
  have hgz : ∀ x, ρ₁ < ‖x‖ → gradient ψ x = 0 := fun x hx => gradient_eq_zero_of_norm_gt hψs hx
  have hlz : ∀ x, ρ₁ < ‖x‖ → lap ψ x = 0 := fun x hx => lap_eq_zero_of_norm_gt hψs hx
  have hADc : ContinuousOn (fun x => S.A x (S.Dv x)) (closedHalfBall n S.R) :=
    S.coeffs.contDiff_A.continuous.continuousOn.clm_apply S.Dv_continuousOn
  set Q : Space n → ℝ := fun x => ⟪S.A x (S.Dv x), gradient ψ x⟫_ℝ
        - ψ x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) - ⟪S.Dv x, gradient ψ x⟫_ℝ
        - S.v x * lap ψ x with hQ
  set Rf : Space n → ℝ := fun x => ⟪S.A x (S.Dv x), gradient ψ x⟫_ℝ
        - ⟪S.Dv x, gradient ψ x⟫_ℝ - ψ x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) with hRf
  have hRc : ContinuousOn Rf (closedHalfBall n S.R) :=
    ((hADc.inner hψg.continuousOn).sub (S.Dv_continuousOn.inner hψg.continuousOn)).sub
      (hψc.continuousOn.mul ((S.coeffs.cont_B.continuousOn.inner S.Dv_continuousOn).add
          (S.coeffs.cont_C.continuousOn.mul S.v_continuousOn)))
  have hQc : ContinuousOn Q (closedHalfBall n S.R) :=
    (((hADc.inner hψg.continuousOn).sub
      (hψc.continuousOn.mul ((S.coeffs.cont_B.continuousOn.inner S.Dv_continuousOn).add
          (S.coeffs.cont_C.continuousOn.mul S.v_continuousOn)))).sub
      (S.Dv_continuousOn.inner hψg.continuousOn)).sub
      (S.v_continuousOn.mul (continuous_lap hψ).continuousOn)
  have iR : IntegrableOn Rf {x : Space n | 0 < vcoord x} :=
    integrableOn_halfSpace_of_continuousOn (hρ₁.trans hρR) hRc (fun x hx => by
      simp only [hRf, hgz x hx, hψs x hx.le, inner_zero_right, sub_zero, zero_mul])
  have iQ : IntegrableOn Q {x : Space n | 0 < vcoord x} :=
    integrableOn_halfSpace_of_continuousOn (hρ₁.trans hρR) hQc (fun x hx => by
      simp only [hQ, hgz x hx, hψs x hx.le, hlz x hx, inner_zero_right, sub_zero, zero_mul,
        mul_zero])
  have hid := green_lap_identity S ψ hψ (hρ₁.trans hρR) hψs
  change ∫ x in {x : Space n | 0 < vcoord x}, Q x = _ at hid
  -- `v Δψ = R - Q`
  have hsplit : ∫ x in {x : Space n | 0 < vcoord x}, S.v x * lap ψ x =
      (∫ x in {x : Space n | 0 < vcoord x}, Rf x) - ∫ x in {x : Space n | 0 < vcoord x}, Q x := by
    rw [← integral_sub iR iQ]
    congr 1
    funext x
    simp only [hRf, hQ]
    ring
  -- bound on `R`
  have hAI : ∀ x : Space n, ‖S.A x - ContinuousLinearMap.id ℝ (Space n)‖ ≤ K * ‖x‖ := by
    intro x
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := S.A) (s := Set.univ)
      (fun y _ => (S.coeffs.contDiff_A.differentiable (by norm_num)) y)
      (fun y _ => S.coeffs.bound_dA y) convex_univ (Set.mem_univ 0) (Set.mem_univ x)
    rwa [S.A_zero, sub_zero] at h
  have hRb : ∀ x, 0 < vcoord x → |Rf x| ≤ K * (ρ * L1 + L0) *
      (halfBall n ρ).indicator (fun y => ‖S.Dv y‖ + |S.v y|) x := by
    intro x hx
    by_cases hxρ : ‖x‖ < ρ
    · rw [Set.indicator_of_mem (show x ∈ halfBall n ρ from ⟨hxρ, hx⟩)]
      have e : ⟪S.A x (S.Dv x), gradient ψ x⟫_ℝ - ⟪S.Dv x, gradient ψ x⟫_ℝ =
          ⟪(S.A x - ContinuousLinearMap.id ℝ (Space n)) (S.Dv x), gradient ψ x⟫_ℝ := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_sub_left]
      have h1 : |⟪(S.A x - ContinuousLinearMap.id ℝ (Space n)) (S.Dv x), gradient ψ x⟫_ℝ| ≤
          K * ρ * L1 * ‖S.Dv x‖ := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        have h2 := (S.A x - ContinuousLinearMap.id ℝ (Space n)).le_opNorm (S.Dv x)
        have h3 : ‖S.A x - ContinuousLinearMap.id ℝ (Space n)‖ ≤ K * ρ :=
          (hAI x).trans (mul_le_mul_of_nonneg_left hxρ.le hK)
        calc ‖(S.A x - ContinuousLinearMap.id ℝ (Space n)) (S.Dv x)‖ * ‖gradient ψ x‖
            ≤ (K * ρ * ‖S.Dv x‖) * L1 := by
              apply mul_le_mul _ (hψ1 x) (norm_nonneg _) (by positivity)
              exact h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
          _ = K * ρ * L1 * ‖S.Dv x‖ := by ring
      have h4 : |ψ x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x)| ≤ L0 * (K * (‖S.Dv x‖ + |S.v x|)) := by
        rw [abs_mul]
        apply mul_le_mul (hψ0 x) _ (abs_nonneg _) hL0
        calc |⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x| ≤ |⟪S.B x, S.Dv x⟫_ℝ| + |S.C x * S.v x| :=
              abs_add_le _ _
          _ ≤ K * ‖S.Dv x‖ + K * |S.v x| := by
              apply add_le_add
              · exact (abs_real_inner_le_norm _ _).trans
                  (mul_le_mul_of_nonneg_right (S.coeffs.bound_B x) (norm_nonneg _))
              · rw [abs_mul]
                exact mul_le_mul_of_nonneg_right (S.coeffs.bound_C x) (abs_nonneg _)
          _ = K * (‖S.Dv x‖ + |S.v x|) := by ring
      have eR : Rf x = ⟪(S.A x - ContinuousLinearMap.id ℝ (Space n)) (S.Dv x), gradient ψ x⟫_ℝ
          - ψ x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) := by
        simp only [hRf]
        rw [e]
      rw [eR]
      have hv0 : 0 ≤ |S.v x| := abs_nonneg _
      have hD0 : 0 ≤ ‖S.Dv x‖ := norm_nonneg _
      calc |⟪(S.A x - ContinuousLinearMap.id ℝ (Space n)) (S.Dv x), gradient ψ x⟫_ℝ
            - ψ x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x)|
          ≤ |⟪(S.A x - ContinuousLinearMap.id ℝ (Space n)) (S.Dv x), gradient ψ x⟫_ℝ|
            + |ψ x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x)| := abs_sub _ _
        _ ≤ K * ρ * L1 * ‖S.Dv x‖ + L0 * (K * (‖S.Dv x‖ + |S.v x|)) := add_le_add h1 h4
        _ ≤ K * (ρ * L1 + L0) * (‖S.Dv x‖ + |S.v x|) := by
            have t1 : 0 ≤ K * ρ * L1 * |S.v x| := by positivity
            nlinarith [t1]
    · rw [Set.indicator_of_notMem (fun (h : x ∈ halfBall n ρ) => hxρ h.1)]
      push Not at hxρ
      simp only [hRf, hgz x (by linarith), hψs x (by linarith), inner_zero_right, sub_zero,
        zero_mul, abs_zero, mul_zero, le_refl]
  have hRint : |∫ x in {x : Space n | 0 < vcoord x}, Rf x| ≤
      K * (ρ * L1 + L0) * ∫ x in halfBall n ρ, (‖S.Dv x‖ + |S.v x|) := by
    have hii : IntegrableOn ((halfBall n ρ).indicator (fun y => ‖S.Dv y‖ + |S.v y|))
        {x : Space n | 0 < vcoord x} :=
      ((integrableOn_halfBall_of_continuousOn hρR
        (S.Dv_continuousOn.norm.add S.v_continuousOn.abs)).integrable_indicator
        (measurableSet_halfBall ρ)).integrableOn
    calc |∫ x in {x : Space n | 0 < vcoord x}, Rf x|
        ≤ ∫ x in {x : Space n | 0 < vcoord x}, |Rf x| := abs_integral_le_integral_abs
      _ ≤ ∫ x in {x : Space n | 0 < vcoord x}, K * (ρ * L1 + L0) *
            (halfBall n ρ).indicator (fun y => ‖S.Dv y‖ + |S.v y|) x :=
          setIntegral_mono_on iR.abs (hii.const_mul _) (F1.measurableSet_halfSpace 0) hRb
      _ = K * (ρ * L1 + L0) * ∫ x in halfBall n ρ, (‖S.Dv x‖ + |S.v x|) := by
          rw [integral_const_mul, setIntegral_indicator (measurableSet_halfBall ρ),
            Set.inter_eq_right.mpr (fun x (hx : x ∈ halfBall n ρ) => hx.2)]
  -- the boundary term
  have hflat := abs_integral_flat_le (f := fun x => ψ x * ⟪S.A x (S.Dv x), ed n⟫_ℝ
      - S.v x * ⟪gradient ψ x, ed n⟫_ℝ) hρ (Bd := Bd) hBd
      (fun x hx => by
        simp only [hψs x (by linarith), hgz x (by linarith), inner_zero_left, zero_mul,
          mul_zero, sub_zero])
  have hflat' : |∫ y, (ψ (lift y 0) * ⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ
      - S.v (lift y 0) * ⟪gradient ψ (lift y 0), ed n⟫_ℝ)| ≤ w1 * (ρ ^ n * Bd) := by
    rw [← mul_assoc]
    exact hflat
  rw [hsplit, hid]
  have hI0 : 0 ≤ ∫ x in halfBall n ρ, (‖S.Dv x‖ + |S.v x|) :=
    setIntegral_nonneg (measurableSet_halfBall ρ) fun x _ => by positivity
  have hρn : 0 ≤ ρ ^ n * Bd := by positivity
  have hX : 0 ≤ (ρ * L1 + L0) * ∫ x in halfBall n ρ, (‖S.Dv x‖ + |S.v x|) := by positivity
  calc |(∫ x in {x : Space n | 0 < vcoord x}, Rf x) -
        -∫ y, (ψ (lift y 0) * ⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ
          - S.v (lift y 0) * ⟪gradient ψ (lift y 0), ed n⟫_ℝ)|
      ≤ |∫ x in {x : Space n | 0 < vcoord x}, Rf x| +
          |∫ y, (ψ (lift y 0) * ⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ
          - S.v (lift y 0) * ⟪gradient ψ (lift y 0), ed n⟫_ℝ)| := by
        rw [sub_neg_eq_add]
        exact abs_add_le _ _
    _ ≤ K * ((ρ * L1 + L0) * ∫ x in halfBall n ρ, (‖S.Dv x‖ + |S.v x|)) +
          w1 * (ρ ^ n * Bd) := by
        rw [← mul_assoc K]
        exact add_le_add hRint hflat'
    _ ≤ (K + w1 + 1) * ((ρ * L1 + L0) * (∫ x in halfBall n ρ, (‖S.Dv x‖ + |S.v x|))
          + ρ ^ n * Bd) := by
        nlinarith [mul_nonneg hw1 hX, mul_nonneg hK hρn]

/-! ### Rescaling -/

lemma integral_Dw_sq_eq (S : HalfBallSolution n) {s r : ℝ} (hs : 0 < s) (hE : 0 < E S s) :
    ∫ x in halfBall n r, ‖Dw S s x‖ ^ 2 = s ^ 2 / E S s * ∫ x in halfBall n (s * r), ‖S.Dv x‖ ^ 2 := by
  have h : ∀ x, ‖Dw S s x‖ ^ 2 = (cst S s * s) ^ 2 * ‖S.Dv (s • x)‖ ^ 2 := fun x => by
    unfold Dw
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [h]
  rw [integral_const_mul, setIntegral_halfBall_comp_smul (fun y => ‖S.Dv y‖ ^ 2) hs r, mul_pow,
    cst_sq S hs hE]
  have hsn : (0 : ℝ) < s ^ (n + 1) := pow_pos hs _
  field_simp

/-- Change of variables `x = sX` on the upper half-space. -/
lemma setIntegral_halfSpace_comp_smul (f : Space n → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x in {x : Space n | 0 < vcoord x}, f (s • x) =
      (s ^ (n + 1))⁻¹ * ∫ x in {x : Space n | 0 < vcoord x}, f x := by
  have hset : s • {x : Space n | 0 < vcoord x} = {x : Space n | 0 < vcoord x} := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hs.ne']
    simp only [Set.mem_ofPred_eq, vcoord_smul]
    constructor
    · intro h
      have := mul_pos hs h
      rwa [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at this
    · intro h
      exact mul_pos (inv_pos.mpr hs) h
  rw [Measure.setIntegral_comp_smul_of_pos _ f _ hs, hset, finrank_space, smul_eq_mul]

/-- Caccioppoli's inequality up to the flat boundary, transported to the blow-up sequence. -/
lemma integral_Dw_sq_bdd (S : HalfBallSolution n)
    (hneu' : ∀ N : ℕ, ∃ Cn : ℝ, ∀ x ∈ flatPiece n S.R, |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ Cn * ‖x‖ ^ N)
    (D : ℝ) (K₀ : ℕ) (s : ℕ → ℝ) (hs_pos : ∀ j, 0 < s j) (hs_R : ∀ j, 4 * s j ≤ S.R)
    (hs1 : ∀ j, s j ≤ 1) (hdoub : ∀ j, E S (2 * s j) ≤ D * E S (s j))
    (hlow : ∀ j, s j ^ K₀ < E S (s j)) :
    ∃ C₁ : ℝ, ∀ j, ∫ x in halfBall n (3 / 2), ‖Dw S (s j) x‖ ^ 2 ≤ C₁ := by
  obtain ⟨Cc, hCc, hcac⟩ := caccioppoli_ball S
  obtain ⟨C1, hC1⟩ := S.dirichlet_flat K₀
  obtain ⟨C2, hC2⟩ := hneu' K₀
  have hEpos : ∀ j, 0 < E S (s j) := fun j => lt_of_le_of_lt (pow_pos (hs_pos j) _).le (hlow j)
  have hD0 : 0 ≤ D := by
    by_contra hD
    push Not at hD
    have h1 := hdoub 0
    have h2 : D * E S (s 0) < 0 := mul_neg_of_neg_of_pos hD (hEpos 0)
    linarith [E_nonneg S (2 * s 0)]
  refine ⟨Cc * (2 * D + |C1| * |C2| * 4 ^ K₀), fun j => ?_⟩
  set t := s j with ht
  have htpos : 0 < t := hs_pos j
  have ht1 : t ≤ 1 := hs1 j
  set Bd : ℝ := |C1| * |C2| * (2 * t) ^ (2 * K₀) with hBd_def
  have hBd : ∀ x ∈ flatPiece n (2 * t), |S.v x * ⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ Bd := by
    intro x hx
    have hxR : x ∈ flatPiece n S.R := ⟨by linarith [hx.1, hs_R j], hx.2⟩
    rw [abs_mul]
    have hxn : ‖x‖ ^ K₀ ≤ (2 * t) ^ K₀ := pow_le_pow_left₀ (norm_nonneg _) hx.1.le _
    have h1 : |S.v x| ≤ |C1| * (2 * t) ^ K₀ :=
      (hC1 x hxR).trans (mul_le_mul (le_abs_self C1) hxn (by positivity) (abs_nonneg _))
    have h2 : |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ |C2| * (2 * t) ^ K₀ :=
      (hC2 x hxR).trans (mul_le_mul (le_abs_self C2) hxn (by positivity) (abs_nonneg _))
    calc |S.v x| * |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ (|C1| * (2 * t) ^ K₀) * (|C2| * (2 * t) ^ K₀) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = Bd := by rw [hBd_def]; ring
  have hcac' := hcac t Bd htpos (by linarith [hs_R j]) hBd
  rw [integral_Dw_sq_eq S htpos (hEpos j), show t * (3 / 2) = 3 / 2 * t by ring]
  set E1 := E S t with hE1
  set E2 := E S (2 * t) with hE2
  have hE1pos : 0 < E1 := hEpos j
  have hE2le : E2 ≤ D * E1 := hdoub j
  have hlowt : t ^ K₀ < E1 := hlow j
  have hfac : 0 ≤ t ^ 2 / E1 := by positivity
  calc t ^ 2 / E1 * ∫ x in halfBall n (3 / 2 * t), ‖S.Dv x‖ ^ 2
      ≤ t ^ 2 / E1 * (Cc * ((t⁻¹ ^ 2 + 1) * E2 + t ^ n * Bd)) :=
        mul_le_mul_of_nonneg_left hcac' hfac
    _ = Cc * ((1 + t ^ 2) * (E2 / E1) + t ^ 2 * t ^ n * Bd / E1) := by
        field_simp
    _ ≤ Cc * (2 * D + |C1| * |C2| * 4 ^ K₀) := by
        apply mul_le_mul_of_nonneg_left _ hCc.le
        have hq : E2 / E1 ≤ D := by rw [div_le_iff₀ hE1pos]; exact hE2le
        have hq0 : 0 ≤ E2 / E1 := div_nonneg (E_nonneg S _) hE1pos.le
        have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ htpos.le ht1
        have h1 : (1 + t ^ 2) * (E2 / E1) ≤ 2 * D := by nlinarith
        have htK : t ^ K₀ ≤ 1 := pow_le_one₀ htpos.le ht1
        have htn : t ^ n ≤ 1 := pow_le_one₀ htpos.le ht1
        have hC0 : 0 ≤ |C1| * |C2| := by positivity
        have hBd' : Bd = |C1| * |C2| * 4 ^ K₀ * (t ^ K₀ * t ^ K₀) := by
          rw [hBd_def, pow_mul, mul_pow]; ring
        have h2 : t ^ 2 * t ^ n * Bd / E1 ≤ |C1| * |C2| * 4 ^ K₀ := by
          rw [div_le_iff₀ hE1pos, hBd']
          have hK0 : 0 ≤ t ^ K₀ := by positivity
          have h4 : (0 : ℝ) ≤ 4 ^ K₀ := by positivity
          have h5 : t ^ 2 * t ^ n * t ^ K₀ ≤ 1 := by
            have := mul_le_mul ht2 htn (by positivity) (by norm_num)
            have := mul_le_mul this htK (by positivity) (by norm_num)
            linarith
          have h6 : t ^ K₀ * t ^ K₀ ≤ t ^ K₀ * E1 := mul_le_mul_of_nonneg_left hlowt.le hK0
          calc t ^ 2 * t ^ n * (|C1| * |C2| * 4 ^ K₀ * (t ^ K₀ * t ^ K₀))
              ≤ t ^ 2 * t ^ n * (|C1| * |C2| * 4 ^ K₀ * (t ^ K₀ * E1)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left h6 (by positivity)
            _ = (|C1| * |C2| * 4 ^ K₀) * (t ^ 2 * t ^ n * t ^ K₀) * E1 := by ring
            _ ≤ (|C1| * |C2| * 4 ^ K₀) * 1 * E1 := by
                apply mul_le_mul_of_nonneg_right _ hE1pos.le
                exact mul_le_mul_of_nonneg_left h5 (by positivity)
            _ = |C1| * |C2| * 4 ^ K₀ * E1 := by ring
        linarith

/-- Cauchy–Schwarz on a set. -/
lemma abs_setIntegral_mul_le_sqrt {s : Set (Space n)} {f h : Space n → ℝ}
    (hf : MemLp f 2 (volume.restrict s)) (hh : MemLp h 2 (volume.restrict s)) :
    |∫ x in s, f x * h x| ≤ Real.sqrt (∫ x in s, f x ^ 2) * Real.sqrt (∫ x in s, h x ^ 2) := by
  have hf' : MemLp f (ENNReal.ofReal 2) (volume.restrict s) := by
    rwa [show ENNReal.ofReal 2 = 2 by norm_num]
  have hh' : MemLp h (ENNReal.ofReal 2) (volume.restrict s) := by
    rwa [show ENNReal.ofReal 2 = 2 by norm_num]
  calc |∫ x in s, f x * h x| ≤ ∫ x in s, ‖f x‖ * ‖h x‖ := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        simp only [norm_mul]
    _ ≤ (∫ x in s, ‖f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ x in s, ‖h x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hh'
    _ = _ := by
        simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]

/-- Squared Cauchy–Schwarz against the constant `1`. -/
lemma sq_setIntegral_le {s : Set (Space n)} (hfin : volume s < ⊤) {f : Space n → ℝ}
    (hf : MemLp f 2 (volume.restrict s)) :
    (∫ x in s, f x) ^ 2 ≤ volume.real s * ∫ x in s, f x ^ 2 := by
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hfin.ne
  have h1 : MemLp (fun _ => (1 : ℝ)) 2 (volume.restrict s) := memLp_const 1
  have h := abs_setIntegral_mul_le_sqrt hf h1
  simp only [mul_one, one_pow, setIntegral_const, smul_eq_mul] at h
  have hA : 0 ≤ ∫ x in s, f x ^ 2 := integral_nonneg fun x => sq_nonneg (f x)
  have hB : 0 ≤ volume.real s := measureReal_nonneg
  calc (∫ x in s, f x) ^ 2 = |∫ x in s, f x| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∫ x in s, f x ^ 2) * Real.sqrt (volume.real s)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = volume.real s * ∫ x in s, f x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB, mul_comm]

/-- The volume of a half-ball. -/
lemma volume_real_halfBall_le {r : ℝ} (hr : 0 < r) :
    volume.real (halfBall n r) ≤ volume.real (ball (0 : Space n) 1) * r ^ (n + 1) := by
  have hsub : halfBall n r ⊆ ball (0 : Space n) r :=
    fun x (hx : x ∈ halfBall n r) => mem_ball_zero_iff.mpr hx.1
  have h1 : volume.real (halfBall n r) ≤ volume.real (ball (0 : Space n) r) :=
    measureReal_mono hsub measure_ball_lt_top.ne
  have h2 : volume.real (ball (0 : Space n) r) = r ^ (n + 1) * volume.real (ball (0 : Space n) 1) := by
    simp only [measureReal_def]
    rw [Measure.addHaar_ball_of_pos _ _ hr, finrank_space, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rw [h2] at h1
  linarith

/-! Helpers for `integral_sub_translate_sq_le` (worker `R1_translate`). Route: for `x` off the
hyperplane `{t = 0}` the segment `s ↦ x + s • h` meets it at most once (`countable_hit`), so the
countable-exception FTC and Jensen on `(0, 1]` give the pointwise bound `sq_sub_le_segment`; the
hyperplane is null (`volume_vcoord_eq_zero`), and Tonelli plus translation invariance conclude. -/
namespace W_R1_translate

/-- The hyperplane `{t = 0}` is Lebesgue-null. -/
lemma volume_vcoord_eq_zero : volume {x : Space n | vcoord x = 0} = 0 := by
  have hker : ({x : Space n | vcoord x = 0} : Set (Space n)) =
      (LinearMap.ker (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).toLinearMap :
        Set (Space n)) := by
    ext x
    simp [vcoord]
  rw [hker]
  apply Measure.addHaar_submodule
  intro htop
  have hmem : EuclideanSpace.single (Fin.last n) (1 : ℝ) ∈
      LinearMap.ker (EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ).toLinearMap := by
    rw [htop]; exact Submodule.mem_top
  simp at hmem

/-- Jensen (or Cauchy–Schwarz) on `(0, 1]`. -/
lemma sq_integral_Ioc_le {φ : ℝ → ℝ} (hφ : MemLp φ 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∫ s in Ioc (0 : ℝ) 1, φ s) ^ 2 ≤ ∫ s in Ioc (0 : ℝ) 1, φ s ^ 2 := by
  have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have h1 := ProbabilityTheory.variance_nonneg φ (volume.restrict (Ioc (0 : ℝ) 1))
  rw [ProbabilityTheory.variance_eq_sub hφ] at h1
  simpa [Pi.pow_apply] using h1

/-- A bounded measurable vector field vanishing outside `B_R` has square-integrable norm. -/
lemma integrable_norm_sq (G : Space n → Space n) (R C : ℝ) (hGs : ∀ x, R ≤ ‖x‖ → G x = 0)
    (hGm : Measurable G) (hC : ∀ x, ‖G x‖ ≤ C) : Integrable (fun x => ‖G x‖ ^ 2) := by
  have hint : Integrable ((closedBall (0 : Space n) R).indicator (fun _ => C ^ 2)) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (measure_closedBall_lt_top).ne)
  refine hint.mono' ((hGm.norm.pow_const 2).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ closedBall (0 : Space n) R
  · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  · rw [indicator_of_notMem hx]
    have : R ≤ ‖x‖ := by
      rw [mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
    simp [hGs x this]

/-- Off the hyperplane, the segment `s ↦ x + s • h` meets `{t = 0}` at most once. -/
lemma countable_hit (x h : Space n) (hx : vcoord x ≠ 0) :
    {s : ℝ | vcoord (x + s • h) = 0}.Countable := by
  apply Set.Subsingleton.countable
  intro a ha b hb
  simp only [Set.mem_ofPred_eq, vcoord, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ha hb
  by_cases h0 : h (Fin.last n) = 0
  · rw [h0, mul_zero, add_zero] at ha
    exact absurd ha hx
  · have : (a - b) * h (Fin.last n) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp this with h2 | h2
    · linarith
    · exact absurd h2 h0

/-- Segment FTC plus Jensen: the pointwise bound behind the translation estimate. -/
lemma sq_sub_le_segment (f : Space n → ℝ) (G : Space n → Space n)
    (hf : Continuous f) (hGm : Measurable G) (C : ℝ) (hC : ∀ x, ‖G x‖ ≤ C)
    (hd : ∀ x, vcoord x ≠ 0 → HasGradientAt f (G x) x) (x h : Space n) (hx : vcoord x ≠ 0) :
    (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ s in Ioc (0 : ℝ) 1, ‖G (x + s • h)‖ ^ 2 := by
  set g : ℝ → ℝ := fun s => f (x + s • h)
  set g' : ℝ → ℝ := fun s => ⟪G (x + s • h), h⟫_ℝ
  have hpath : Continuous fun s : ℝ => x + s • h :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hgc : Continuous g := hf.comp hpath
  have hGpm : Measurable fun s : ℝ => G (x + s • h) := hGm.comp hpath.measurable
  have hg'm : Measurable g' := hGpm.inner measurable_const
  have hg'b : ∀ s, ‖g' s‖ ≤ C * ‖h‖ := fun s => by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1 \ {s : ℝ | vcoord (x + s • h) = 0},
      HasDerivAt g (g' s) s := by
    intro s hs
    have h1 := (hd (x + s • h) hs.2).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add x
    have h3 := h1.comp_hasDerivAt s h2
    rw [InnerProductSpace.toDual_apply_apply] at h3
    exact h3
  have hint : IntervalIntegrable g' volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact Integrable.of_bound hg'm.aestronglyMeasurable (C * ‖h‖) (ae_of_all _ hg'b)
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le g g' zero_le_one
    (countable_hit x h hx) hgc.continuousOn hderiv hint
  have hg1 : g 1 - g 0 = f (x + h) - f x := by simp [g]
  rw [← hg1, ← hftc, intervalIntegral.integral_of_le zero_le_one]
  have hmemLp : MemLp g' 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hg'm.aestronglyMeasurable (C * ‖h‖) (ae_of_all _ hg'b)
  refine (sq_integral_Ioc_le hmemLp).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun s => sq_nonneg _) ?_ (ae_of_all _ fun s => ?_)
  · refine Integrable.of_bound ((hGpm.norm.pow_const 2).const_mul _).aestronglyMeasurable
      (‖h‖ ^ 2 * C ^ 2) (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hC _) 2) (by positivity)
  · show g' s ^ 2 ≤ ‖h‖ ^ 2 * ‖G (x + s • h)‖ ^ 2
    have := abs_real_inner_le_norm (G (x + s • h)) h
    calc g' s ^ 2 = |g' s| ^ 2 := (sq_abs _).symm
      _ ≤ (‖G (x + s • h)‖ * ‖h‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = ‖h‖ ^ 2 * ‖G (x + s • h)‖ ^ 2 := by ring

end W_R1_translate

/-- `L²` translation bound for a continuous function supported in `B_R` which is differentiable
off the hyperplane `{t = 0}`, with bounded measurable gradient `G` supported in `B_R` (segment
FTC with at most one exceptional point, `intervalIntegral`'s countable-exception FTC, Jensen on
`[0, 1]`, Tonelli and translation invariance). This is the input needed to apply F3 to the cut-off
even reflections in `exists_L2_subseq_halfBall`. -/
lemma integral_sub_translate_sq_le (f : Space n → ℝ) (G : Space n → Space n) (R : ℝ)
    (hf : Continuous f) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0) (hGs : ∀ x, R ≤ ‖x‖ → G x = 0)
    (hGm : Measurable G) (hGb : ∃ C, ∀ x, ‖G x‖ ≤ C)
    (hd : ∀ x, vcoord x ≠ 0 → HasGradientAt f (G x) x) (h : Space n) :
    ∫ x, (f (x + h) - f x) ^ 2 ≤ (∫ x, ‖G x‖ ^ 2) * ‖h‖ ^ 2 := by
  -- `hfs` is not needed: `integral_mono_of_nonneg` requires no integrability of the left side.
  obtain ⟨C, hC⟩ := hGb
  set F : Space n → ℝ → ℝ := fun x s => ‖G (x + s • h)‖ ^ 2 with hF_def
  have hGsq := W_R1_translate.integrable_norm_sq G R C hGs hGm hC
  have hFm : Measurable (Function.uncurry F) := by
    have : Measurable fun p : Space n × ℝ => p.1 + p.2 • h :=
      measurable_fst.add (measurable_snd.smul_const h)
    exact (hGm.comp this).norm.pow_const 2
  have hFint :
      Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).mpr ⟨ae_of_all _ fun s => ?_, ?_⟩
    · exact hGsq.comp_add_right (s • h)
    · have : (fun s => ∫ x, ‖Function.uncurry F (x, s)‖) = fun _ => ∫ x, ‖G x‖ ^ 2 := by
        funext s
        simp only [Function.uncurry_apply_pair, hF_def, norm_pow, norm_norm]
        exact integral_add_right_eq_self (fun y => ‖G y‖ ^ 2) (s • h)
      rw [this]
      exact integrable_const _
  have hpt : ∀ᵐ x : Space n, (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ s in Ioc (0 : ℝ) 1, F x s := by
    have hnull := W_R1_translate.volume_vcoord_eq_zero (n := n)
    have hae : ∀ᵐ x : Space n, vcoord x ≠ 0 := by
      rw [ae_iff]
      simpa using hnull
    filter_upwards [hae] with x hx
    exact W_R1_translate.sq_sub_le_segment f G hf hGm C hC hd x h hx
  calc ∫ x, (f (x + h) - f x) ^ 2 ≤ ∫ x, ‖h‖ ^ 2 * ∫ s in Ioc (0 : ℝ) 1, F x s :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          (hFint.integral_prod_left.const_mul _) hpt
    _ = ‖h‖ ^ 2 * ∫ s in Ioc (0 : ℝ) 1, ∫ x, F x s := by
        rw [integral_const_mul, integral_integral_swap hFint]
    _ = ‖h‖ ^ 2 * ∫ s in Ioc (0 : ℝ) 1, ∫ x, ‖G x‖ ^ 2 := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
        exact integral_add_right_eq_self (fun y => ‖G y‖ ^ 2) (s • h)
    _ = (∫ x, ‖G x‖ ^ 2) * ‖h‖ ^ 2 := by
        simp [mul_comm]

/-- Rescaling the pairing of the blow-up with `Δψ`. -/
lemma integral_w_lap_eq (S : HalfBallSolution n) {s : ℝ} (hs : 0 < s) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 2 ψ) :
    ∫ x in {x : Space n | 0 < vcoord x}, w S s x * lap ψ x =
      cst S s * s ^ 2 * (s ^ (n + 1))⁻¹ *
        ∫ x in {x : Space n | 0 < vcoord x}, S.v x * lap (fun y => ψ (s⁻¹ • y)) x := by
  have hs0 : s ≠ 0 := hs.ne'
  have e1 : ∀ X : Space n, w S s X * lap ψ X =
      cst S s * (fun y => S.v y * lap ψ (s⁻¹ • y)) (s • X) := by
    intro X
    simp only [w, inv_smul_smul₀ hs0]
    ring
  simp_rw [e1]
  have hcv := setIntegral_halfSpace_comp_smul (fun y => S.v y * lap ψ (s⁻¹ • y)) hs
  rw [integral_const_mul, hcv]
  have e2 : ∀ y : Space n, S.v y * lap ψ (s⁻¹ • y) = s ^ 2 * (S.v y * lap (fun z => ψ (s⁻¹ • z)) y) := by
    intro y
    rw [lap_comp_smul hψ s y]
    field_simp
  simp_rw [e2]
  rw [integral_const_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- Green's formula, `A(0) = I` and the flat Cauchy data: the blow-ups are asymptotically weakly
harmonic, including across the flat boundary. -/
lemma tendsto_integral_w_lap (S : HalfBallSolution n)
    (hneu' : ∀ N : ℕ, ∃ Cn : ℝ, ∀ x ∈ flatPiece n S.R, |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ Cn * ‖x‖ ^ N)
    (D : ℝ) (K₀ : ℕ) (s : ℕ → ℝ) (hs_pos : ∀ j, 0 < s j) (hs_R : ∀ j, 4 * s j ≤ S.R)
    (hs1 : ∀ j, s j ≤ 1) (hs_lim : Tendsto s atTop (𝓝 0))
    (hdoub : ∀ j, E S (2 * s j) ≤ D * E S (s j)) (hlow : ∀ j, s j ^ K₀ < E S (s j))
    (ψ : Space n → ℝ) (hψ : ContDiff ℝ 2 ψ) (ρ : ℝ) (hρ : ρ < 3 / 2)
    (hψs : ∀ x, ρ ≤ ‖x‖ → ψ x = 0) :
    Tendsto (fun j => ∫ x in {x : Space n | 0 < vcoord x}, w S (s j) x * lap ψ x) atTop
      (𝓝 0) := by
  have hψc : Continuous ψ := hψ.continuous
  have hψcs : HasCompactSupport ψ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space n) (ρ + 1)) fun x hx => hψs x (by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx; linarith)
  obtain ⟨L0, hL0⟩ := hψc.bounded_above_of_compact_support hψcs
  have hgcs : HasCompactSupport (gradient ψ) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space n) (ρ + 1)) fun x hx =>
      gradient_eq_zero_of_norm_gt hψs (by
        simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx; linarith)
  obtain ⟨L1, hL1⟩ := (contDiff_gradient hψ).continuous.bounded_above_of_compact_support hgcs
  have hL00 : 0 ≤ L0 := (norm_nonneg _).trans (hL0 0)
  have hL10 : 0 ≤ L1 := (norm_nonneg _).trans (hL1 0)
  obtain ⟨Cl, hCl, hest⟩ := abs_integral_v_lap_le S
  obtain ⟨Cc, hCc, hcac⟩ := caccioppoli_ball S
  obtain ⟨C1, hC1⟩ := S.dirichlet_flat (K₀ + 1)
  obtain ⟨C2, hC2⟩ := hneu' (K₀ + 1)
  set ρψ := max ρ (1 / 2) with hρψ_def
  have hρψ : ρψ < 3 / 2 := max_lt hρ (by norm_num)
  have hρψ0 : 0 < ρψ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hψs' : ∀ x, ρψ ≤ ‖x‖ → ψ x = 0 := fun x hx => hψs x (le_trans (le_max_left _ _) hx)
  set ω₁ := volume.real (ball (0 : Space n) 1) with hω₁
  have hω₁0 : 0 ≤ ω₁ := measureReal_nonneg
  have hEpos : ∀ j, 0 < E S (s j) := fun j => lt_of_le_of_lt (pow_pos (hs_pos j) _).le (hlow j)
  have hD0 : 0 ≤ D := by
    by_contra hD
    push Not at hD
    have h1 := hdoub 0
    have h2 : D * E S (s 0) < 0 := mul_neg_of_neg_of_pos hD (hEpos 0)
    linarith [E_nonneg S (2 * s 0)]
  set α := 3 / 2 * L1 + L0 with hα
  have hα0 : 0 ≤ α := by positivity
  set Q := |C1| * |C2| * 4 ^ (K₀ + 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set B₀ := (3 / 2 : ℝ) ^ (n + (K₀ + 1)) * (L0 * |C2| + |C1| * L1) with hB₀
  set M := 2 * Cl ^ 2 * (α ^ 2 * (2 * ω₁ * (3 / 2) ^ (n + 1) * (2 * Cc * D + Cc * Q + D)) + B₀ ^ 2)
    with hM
  suffices hbound : ∀ j, (∫ x in {x : Space n | 0 < vcoord x}, w S (s j) x * lap ψ x) ^ 2 ≤
      M * s j ^ 2 by
    have hlim : Tendsto (fun j => Real.sqrt (max M 0) * s j) atTop (𝓝 0) := by
      simpa using hs_lim.const_mul (Real.sqrt (max M 0))
    refine squeeze_zero_norm (fun j => ?_) hlim
    rw [Real.norm_eq_abs]
    have h1 : (∫ x in {x : Space n | 0 < vcoord x}, w S (s j) x * lap ψ x) ^ 2 ≤
        max M 0 * s j ^ 2 :=
      (hbound j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    have h2 := Real.abs_le_sqrt h1
    rwa [Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq (hs_pos j).le] at h2
  intro j
  set t := s j with ht
  have htpos : 0 < t := hs_pos j
  have ht1 : t ≤ 1 := hs1 j
  have htR : 4 * t ≤ S.R := hs_R j
  set E1 := E S t with hE1
  have hE1pos : 0 < E1 := hEpos j
  have hlowt : t ^ K₀ < E1 := hlow j
  have hdoubt : E S (2 * t) ≤ D * E1 := hdoub j
  set ψt : Space n → ℝ := fun y => ψ (t⁻¹ • y) with hψt
  have hψt2 : ContDiff ℝ 2 ψt := hψ.comp (contDiff_const_smul _)
  have hnorm : ∀ x : Space n, ‖t⁻¹ • x‖ = t⁻¹ * ‖x‖ := fun x => by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le)]
  have hψts : ∀ x, t * ρψ ≤ ‖x‖ → ψt x = 0 := by
    intro x hx
    apply hψs'
    rw [hnorm, le_inv_mul_iff₀ htpos]
    linarith
  have hψt0 : ∀ x, |ψt x| ≤ L0 := fun x => by rw [← Real.norm_eq_abs]; exact hL0 _
  have hψt1 : ∀ x, ‖gradient ψt x‖ ≤ t⁻¹ * L1 := by
    intro x
    rw [hψt, gradient_comp_smul (hψ.of_le (by norm_num)) t x, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr htpos.le)]
    exact mul_le_mul_of_nonneg_left (hL1 _) (inv_nonneg.mpr htpos.le)
  have hed : ‖ed n‖ = 1 := by simp [ed]
  -- boundary bound for the Laplacian estimate
  set Bd := (L0 * |C2| + |C1| * (t⁻¹ * L1)) * (3 / 2 * t) ^ (K₀ + 1) with hBd
  have hBdb : ∀ x ∈ flatPiece n (3 / 2 * t),
      |ψt x * ⟪S.A x (S.Dv x), ed n⟫_ℝ - S.v x * ⟪gradient ψt x, ed n⟫_ℝ| ≤ Bd := by
    intro x hx
    have hxR : x ∈ flatPiece n S.R := ⟨by linarith [hx.1], hx.2⟩
    have hxn : ‖x‖ ^ (K₀ + 1) ≤ (3 / 2 * t) ^ (K₀ + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hx.1.le _
    have h1 : |S.v x| ≤ |C1| * (3 / 2 * t) ^ (K₀ + 1) :=
      (hC1 x hxR).trans (mul_le_mul (le_abs_self C1) hxn (by positivity) (abs_nonneg _))
    have h2 : |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ |C2| * (3 / 2 * t) ^ (K₀ + 1) :=
      (hC2 x hxR).trans (mul_le_mul (le_abs_self C2) hxn (by positivity) (abs_nonneg _))
    have h3 : |⟪gradient ψt x, ed n⟫_ℝ| ≤ t⁻¹ * L1 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hed, mul_one]
      exact hψt1 x
    calc |ψt x * ⟪S.A x (S.Dv x), ed n⟫_ℝ - S.v x * ⟪gradient ψt x, ed n⟫_ℝ|
        ≤ |ψt x * ⟪S.A x (S.Dv x), ed n⟫_ℝ| + |S.v x * ⟪gradient ψt x, ed n⟫_ℝ| := abs_sub _ _
      _ = |ψt x| * |⟪S.A x (S.Dv x), ed n⟫_ℝ| + |S.v x| * |⟪gradient ψt x, ed n⟫_ℝ| := by
          rw [abs_mul, abs_mul]
      _ ≤ L0 * (|C2| * (3 / 2 * t) ^ (K₀ + 1)) +
            (|C1| * (3 / 2 * t) ^ (K₀ + 1)) * (t⁻¹ * L1) := by
          apply add_le_add
          · exact mul_le_mul (hψt0 x) h2 (abs_nonneg _) hL00
          · exact mul_le_mul h1 h3 (abs_nonneg _) (by positivity)
      _ = Bd := by rw [hBd]; ring
  have hJ := hest ψt (t * ρψ) (3 / 2 * t) L0 (t⁻¹ * L1) Bd hψt2 (by positivity) (by nlinarith)
    (by linarith) hψts hψt0 hψt1 hBdb
  set I1 := ∫ x in halfBall n (3 / 2 * t), (‖S.Dv x‖ + |S.v x|) with hI1
  set J := ∫ x in {x : Space n | 0 < vcoord x}, S.v x * lap ψt x with hJdef
  have hcoef : 3 / 2 * t * (t⁻¹ * L1) + L0 = α := by rw [hα]; field_simp
  rw [hcoef] at hJ
  set β := (3 / 2 * t) ^ n * Bd with hβ
  have hI10 : 0 ≤ I1 := setIntegral_nonneg (measurableSet_halfBall _) fun x _ => by positivity
  have hBd0 : 0 ≤ Bd := by rw [hBd]; positivity
  have hβ0 : 0 ≤ β := by positivity
  -- `J² ≤ Cl² (2 α² I1² + 2 β²)`
  have hJ2 : J ^ 2 ≤ Cl ^ 2 * (2 * α ^ 2 * I1 ^ 2 + 2 * β ^ 2) := by
    have h1 : J ^ 2 ≤ (Cl * (α * I1 + β)) ^ 2 := by
      rw [← sq_abs J]
      exact pow_le_pow_left₀ (abs_nonneg _) hJ 2
    have h2 : (α * I1 + β) ^ 2 ≤ 2 * α ^ 2 * I1 ^ 2 + 2 * β ^ 2 := by
      have e : 2 * α ^ 2 * I1 ^ 2 + 2 * β ^ 2 - (α * I1 + β) ^ 2 = (α * I1 - β) ^ 2 := by ring
      have h := sq_nonneg (α * I1 - β)
      rw [← e] at h
      exact sub_nonneg.mp h
    calc J ^ 2 ≤ (Cl * (α * I1 + β)) ^ 2 := h1
      _ = Cl ^ 2 * (α * I1 + β) ^ 2 := by ring
      _ ≤ Cl ^ 2 * (2 * α ^ 2 * I1 ^ 2 + 2 * β ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  -- the rescaling identity: `I² = F J²` with `F = t⁴ / (E(t) t^(n+1))`
  have hI : (∫ x in {x : Space n | 0 < vcoord x}, w S t x * lap ψ x) ^ 2 =
      t ^ 4 / (E1 * t ^ (n + 1)) * J ^ 2 := by
    rw [integral_w_lap_eq S htpos hψ, mul_pow, mul_pow, mul_pow, cst_sq S htpos hE1pos]
    change t ^ (n + 1) / E1 * (t ^ 2) ^ 2 * ((t ^ (n + 1))⁻¹) ^ 2 * J ^ 2 = _
    have htn : (0 : ℝ) < t ^ (n + 1) := pow_pos htpos _
    field_simp
  -- the `L²` norm of `v` on `B_{3t/2}⁺`
  have hVsq : ∫ x in halfBall n (3 / 2 * t), S.v x ^ 2 ≤ D * E1 :=
    (E_mono S (show 3 / 2 * t ≤ 2 * t by linarith) (by linarith)).trans hdoubt
  set Dsq := ∫ x in halfBall n (3 / 2 * t), ‖S.Dv x‖ ^ 2 with hDsq_def
  set Vsq := ∫ x in halfBall n (3 / 2 * t), S.v x ^ 2 with hVsq_def
  have h32R : 3 / 2 * t < S.R := by linarith
  -- Cauchy–Schwarz on `B_{3t/2}⁺`
  have hI1sq : I1 ^ 2 ≤ ω₁ * (3 / 2 * t) ^ (n + 1) * (2 * Dsq + 2 * Vsq) := by
    have hc : ContinuousOn (fun x => ‖S.Dv x‖ + |S.v x|) (closedHalfBall n S.R) :=
      S.Dv_continuousOn.norm.add S.v_continuousOn.abs
    have hmem : MemLp (fun x => ‖S.Dv x‖ + |S.v x|) 2 (volume.restrict (halfBall n (3 / 2 * t))) :=
      (memLp_two_iff_integrable_sq ((hc.mono ((halfBall_subset_closedHalfBall _).trans
        (closedHalfBall_mono h32R.le))).aestronglyMeasurable (measurableSet_halfBall _))).mpr
        (integrableOn_halfBall_of_continuousOn h32R (hc.pow 2))
    have hcs := sq_setIntegral_le (volume_halfBall_lt_top _) hmem
    have hvol := volume_real_halfBall_le (n := n) (show 0 < 3 / 2 * t by positivity)
    have i1 : IntegrableOn (fun x => ‖S.Dv x‖ ^ 2) (halfBall n (3 / 2 * t)) :=
      integrableOn_halfBall_of_continuousOn h32R (S.Dv_continuousOn.norm.pow 2)
    have i2 : IntegrableOn (fun x => S.v x ^ 2) (halfBall n (3 / 2 * t)) :=
      integrableOn_halfBall_of_continuousOn h32R (S.v_continuousOn.pow 2)
    have i3 : IntegrableOn (fun x => (‖S.Dv x‖ + |S.v x|) ^ 2) (halfBall n (3 / 2 * t)) :=
      integrableOn_halfBall_of_continuousOn h32R (hc.pow 2)
    have hsq : ∫ x in halfBall n (3 / 2 * t), (‖S.Dv x‖ + |S.v x|) ^ 2 ≤ 2 * Dsq + 2 * Vsq := by
      have hm : ∫ x in halfBall n (3 / 2 * t), (‖S.Dv x‖ + |S.v x|) ^ 2 ≤
          ∫ x in halfBall n (3 / 2 * t), (2 * ‖S.Dv x‖ ^ 2 + 2 * S.v x ^ 2) := by
        refine integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 2)) fun x => ?_
        have e : 2 * ‖S.Dv x‖ ^ 2 + 2 * S.v x ^ 2 - (‖S.Dv x‖ + |S.v x|) ^ 2 =
            (‖S.Dv x‖ - |S.v x|) ^ 2 := by rw [← sq_abs (S.v x)]; ring
        have h := sq_nonneg (‖S.Dv x‖ - |S.v x|)
        rw [← e] at h
        exact sub_nonneg.mp h
      have e2 : ∫ x in halfBall n (3 / 2 * t), (2 * ‖S.Dv x‖ ^ 2 + 2 * S.v x ^ 2) =
          2 * Dsq + 2 * Vsq := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
          integral_const_mul]
      linarith
    have hint0 : 0 ≤ ∫ x in halfBall n (3 / 2 * t), (‖S.Dv x‖ + |S.v x|) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    calc I1 ^ 2 ≤ volume.real (halfBall n (3 / 2 * t)) *
          ∫ x in halfBall n (3 / 2 * t), (‖S.Dv x‖ + |S.v x|) ^ 2 := hcs
      _ ≤ (ω₁ * (3 / 2 * t) ^ (n + 1)) * (2 * Dsq + 2 * Vsq) :=
          mul_le_mul hvol hsq hint0 (by positivity)
  -- Caccioppoli at radius `t`
  have hDsq : Dsq ≤ Cc * ((t⁻¹ ^ 2 + 1) * D * E1 + Q * E1) := by
    have hBd2 : ∀ x ∈ flatPiece n (2 * t), |S.v x * ⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤
        |C1| * |C2| * (2 * t) ^ (2 * (K₀ + 1)) := by
      intro x hx
      have hxR : x ∈ flatPiece n S.R := ⟨by linarith [hx.1], hx.2⟩
      rw [abs_mul]
      have hxn : ‖x‖ ^ (K₀ + 1) ≤ (2 * t) ^ (K₀ + 1) := pow_le_pow_left₀ (norm_nonneg _) hx.1.le _
      have h1 : |S.v x| ≤ |C1| * (2 * t) ^ (K₀ + 1) :=
        (hC1 x hxR).trans (mul_le_mul (le_abs_self C1) hxn (by positivity) (abs_nonneg _))
      have h2 : |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ |C2| * (2 * t) ^ (K₀ + 1) :=
        (hC2 x hxR).trans (mul_le_mul (le_abs_self C2) hxn (by positivity) (abs_nonneg _))
      calc |S.v x| * |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤
          (|C1| * (2 * t) ^ (K₀ + 1)) * (|C2| * (2 * t) ^ (K₀ + 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = |C1| * |C2| * (2 * t) ^ (2 * (K₀ + 1)) := by ring
    have hc := hcac t _ htpos (by linarith) hBd2
    have hcomp : t ^ n * (|C1| * |C2| * (2 * t) ^ (2 * (K₀ + 1))) ≤ Q * E1 := by
      have e : t ^ n * (|C1| * |C2| * (2 * t) ^ (2 * (K₀ + 1))) =
          Q * (t ^ (n + (K₀ + 2)) * t ^ K₀) := by
        rw [hQ]
        rw [mul_pow, pow_mul, pow_mul]
        ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hQ0
      have h1 : t ^ (n + (K₀ + 2)) ≤ 1 := pow_le_one₀ htpos.le ht1
      calc t ^ (n + (K₀ + 2)) * t ^ K₀ ≤ 1 * t ^ K₀ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ E1 := by rw [one_mul]; exact hlowt.le
    have hE2 : (t⁻¹ ^ 2 + 1) * E S (2 * t) ≤ (t⁻¹ ^ 2 + 1) * D * E1 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hdoubt (by positivity)
    calc Dsq ≤ Cc * ((t⁻¹ ^ 2 + 1) * E S (2 * t) + t ^ n *
          (|C1| * |C2| * (2 * t) ^ (2 * (K₀ + 1)))) := by
          rw [show 3 / 2 * t = 3 / 2 * t from rfl] at hc
          exact hc
      _ ≤ Cc * ((t⁻¹ ^ 2 + 1) * D * E1 + Q * E1) := by
          apply mul_le_mul_of_nonneg_left _ hCc.le
          linarith
  have htne : t ≠ 0 := htpos.ne'
  have hE1ne : E1 ≠ 0 := hE1pos.ne'
  have hF0 : 0 ≤ t ^ 4 / (E1 * t ^ (n + 1)) := by positivity
  -- the gradient part
  have hFI1 : t ^ 4 / (E1 * t ^ (n + 1)) * I1 ^ 2 ≤
      2 * ω₁ * (3 / 2) ^ (n + 1) * (2 * Cc * D + Cc * Q + D) * t ^ 2 := by
    have step1 : t ^ 4 / (E1 * t ^ (n + 1)) * I1 ^ 2 ≤ t ^ 4 / (E1 * t ^ (n + 1)) *
        (ω₁ * (3 / 2 * t) ^ (n + 1) * (2 * (Cc * ((t⁻¹ ^ 2 + 1) * D * E1 + Q * E1)) +
          2 * (D * E1))) := by
      apply mul_le_mul_of_nonneg_left _ hF0
      refine hI1sq.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hDsq, hVsq]
    have step2 : t ^ 4 / (E1 * t ^ (n + 1)) *
        (ω₁ * (3 / 2 * t) ^ (n + 1) * (2 * (Cc * ((t⁻¹ ^ 2 + 1) * D * E1 + Q * E1)) +
          2 * (D * E1))) =
        ω₁ * (3 / 2) ^ (n + 1) * (2 * (Cc * D) * (t ^ 2 + t ^ 4) + 2 * (Cc * Q) * t ^ 4 +
          2 * D * t ^ 4) := by
      rw [mul_pow]
      field_simp
    have ht4 : t ^ 4 ≤ t ^ 2 := pow_le_pow_of_le_one htpos.le ht1 (by norm_num)
    have hcd : 0 ≤ Cc * D := mul_nonneg hCc.le hD0
    have hcq : 0 ≤ Cc * Q := mul_nonneg hCc.le hQ0
    have a1 := mul_le_mul_of_nonneg_left ht4 hcd
    have a2 := mul_le_mul_of_nonneg_left ht4 hcq
    have a3 := mul_le_mul_of_nonneg_left ht4 hD0
    have step3 : 2 * (Cc * D) * (t ^ 2 + t ^ 4) + 2 * (Cc * Q) * t ^ 4 + 2 * D * t ^ 4 ≤
        2 * (2 * Cc * D + Cc * Q + D) * t ^ 2 := by nlinarith
    have hA : 0 ≤ ω₁ * (3 / 2 : ℝ) ^ (n + 1) := by positivity
    calc t ^ 4 / (E1 * t ^ (n + 1)) * I1 ^ 2 ≤ _ := step1
      _ = _ := step2
      _ ≤ ω₁ * (3 / 2) ^ (n + 1) * (2 * (2 * Cc * D + Cc * Q + D) * t ^ 2) :=
          mul_le_mul_of_nonneg_left step3 hA
      _ = 2 * ω₁ * (3 / 2) ^ (n + 1) * (2 * Cc * D + Cc * Q + D) * t ^ 2 := by ring
  -- the boundary part
  have hβle : β ≤ B₀ * t ^ (n + K₀) := by
    have e : β = (3 / 2 : ℝ) ^ (n + (K₀ + 1)) * t ^ (n + K₀) * (L0 * |C2| * t + |C1| * L1) := by
      rw [hβ, hBd]
      field_simp
      ring
    rw [e, hB₀]
    have h1 : L0 * |C2| * t ≤ L0 * |C2| := by
      have := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hL00 (abs_nonneg C2))
      linarith
    have h2 : 0 ≤ (3 / 2 : ℝ) ^ (n + (K₀ + 1)) * t ^ (n + K₀) := by positivity
    calc (3 / 2 : ℝ) ^ (n + (K₀ + 1)) * t ^ (n + K₀) * (L0 * |C2| * t + |C1| * L1)
        ≤ (3 / 2 : ℝ) ^ (n + (K₀ + 1)) * t ^ (n + K₀) * (L0 * |C2| + |C1| * L1) :=
          mul_le_mul_of_nonneg_left (by linarith) h2
      _ = _ := by ring
  have hFβ : t ^ 4 / (E1 * t ^ (n + 1)) * β ^ 2 ≤ B₀ ^ 2 * t ^ 2 := by
    have hβ2 : β ^ 2 ≤ (B₀ * t ^ (n + K₀)) ^ 2 := pow_le_pow_left₀ hβ0 hβle 2
    have hkey : t ^ 4 * (t ^ (n + K₀)) ^ 2 ≤ t ^ 2 * (E1 * t ^ (n + 1)) := by
      have e : t ^ 4 * (t ^ (n + K₀)) ^ 2 = t ^ 2 * t ^ (n + 1) * (t ^ K₀ * t ^ (n + K₀ + 1)) := by
        ring
      rw [e]
      have h1 : t ^ (n + K₀ + 1) ≤ 1 := pow_le_one₀ htpos.le ht1
      have h2 : t ^ K₀ * t ^ (n + K₀ + 1) ≤ E1 := by
        calc t ^ K₀ * t ^ (n + K₀ + 1) ≤ t ^ K₀ * 1 :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ E1 := by rw [mul_one]; exact hlowt.le
      calc t ^ 2 * t ^ (n + 1) * (t ^ K₀ * t ^ (n + K₀ + 1)) ≤ t ^ 2 * t ^ (n + 1) * E1 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = t ^ 2 * (E1 * t ^ (n + 1)) := by ring
    have hden : 0 < E1 * t ^ (n + 1) := by positivity
    calc t ^ 4 / (E1 * t ^ (n + 1)) * β ^ 2 ≤ t ^ 4 / (E1 * t ^ (n + 1)) *
          (B₀ * t ^ (n + K₀)) ^ 2 := mul_le_mul_of_nonneg_left hβ2 hF0
      _ = B₀ ^ 2 * (t ^ 4 * (t ^ (n + K₀)) ^ 2 / (E1 * t ^ (n + 1))) := by ring
      _ ≤ B₀ ^ 2 * t ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          rw [div_le_iff₀ hden]
          exact hkey
  -- conclusion
  rw [hI]
  have hCl2 : 0 ≤ Cl ^ 2 := sq_nonneg _
  calc t ^ 4 / (E1 * t ^ (n + 1)) * J ^ 2
      ≤ t ^ 4 / (E1 * t ^ (n + 1)) * (Cl ^ 2 * (2 * α ^ 2 * I1 ^ 2 + 2 * β ^ 2)) :=
        mul_le_mul_of_nonneg_left hJ2 hF0
    _ = 2 * Cl ^ 2 * (α ^ 2 * (t ^ 4 / (E1 * t ^ (n + 1)) * I1 ^ 2) +
          t ^ 4 / (E1 * t ^ (n + 1)) * β ^ 2) := by ring
    _ ≤ 2 * Cl ^ 2 * (α ^ 2 * (2 * ω₁ * (3 / 2) ^ (n + 1) * (2 * Cc * D + Cc * Q + D) * t ^ 2) +
          B₀ ^ 2 * t ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (mul_le_mul_of_nonneg_left hFI1 (sq_nonneg _)) hFβ
    _ = M * t ^ 2 := by rw [hM]; ring

/-! ### Step 4: compactness -/

/-- The fold `(y, t) ↦ (y, |t|)`, used to build even reflections. -/
noncomputable def fold (x : Space n) : Space n := x - (vcoord x - |vcoord x|) • ed n

lemma vcoord_ed : vcoord (ed n) = 1 := by simp [vcoord, ed]

lemma vcoord_fold (x : Space n) : vcoord (fold x) = |vcoord x| := by
  have h : vcoord (fold x) = vcoord x - (vcoord x - |vcoord x|) * vcoord (ed n) := by
    simp [fold, vcoord]
  rw [h, vcoord_ed]
  ring

lemma fold_of_nonneg {x : Space n} (hx : 0 ≤ vcoord x) : fold x = x := by
  simp [fold, abs_of_nonneg hx]

lemma fold_apply_castSucc (x : Space n) (i : Fin n) : fold x (Fin.castSucc i) = x (Fin.castSucc i) := by
  simp [fold, ed, Fin.castSucc_ne_last]

lemma norm_fold (x : Space n) : ‖fold x‖ = ‖x‖ := by
  have h2 : ‖fold x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc,
      Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [fold_apply_castSucc]
    · have h1 : fold x (Fin.last n) = |vcoord x| := vcoord_fold x
      rw [h1, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs]
      rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

lemma continuous_fold : Continuous (fold (n := n)) := by
  unfold fold
  exact continuous_id.sub ((F1.continuous_vcoord.sub F1.continuous_vcoord.abs).smul
    continuous_const)

lemma fold_mem_closedHalfBall {x : Space n} {r : ℝ} (hx : ‖x‖ < r) :
    fold x ∈ closedHalfBall n r :=
  ⟨by rw [norm_fold]; exact hx, by rw [vcoord_fold]; exact abs_nonneg _⟩

/-- A cut-off even reflection is continuous. -/
lemma continuous_cutoff_fold {u : Space n → ℝ} (hu : ContinuousOn u (closedHalfBall n 2))
    {χ : Space n → ℝ} (hχ : Continuous χ) {r : ℝ} (hr : r < 2)
    (hχs : ∀ x, r ≤ ‖x‖ → χ x = 0) :
    Continuous (fun x => χ x * u (fold x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ‖x‖ < 2
  · have hcw : ContinuousWithinAt u (closedHalfBall n 2) (fold x) :=
      hu _ (fold_mem_closedHalfBall hx)
    have hev : ∀ᶠ y in 𝓝 x, fold y ∈ closedHalfBall n 2 := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      exact fold_mem_closedHalfBall hy
    have h1 : ContinuousAt (fun y => u (fold y)) x :=
      hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨continuous_fold.continuousAt, hev⟩)
    exact hχ.continuousAt.mul h1
  · push Not at hx
    have hev : (fun y => χ y * u (fold y)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show r < ‖x‖ by linarith)] with y hy
      rw [hχs y hy.le, zero_mul]
    exact continuousAt_const.congr hev.symm


namespace W_R1_subseq

/-! ### Helpers for `exists_L2_subseq_halfBall` (Step 4, all proved)

* `reflE`: the reflection `x ↦ x - 2 t e_d`, a linear isometry (hence measure preserving), with
  `fold = reflE` on `{t < 0}`;
* `volume_vcoord_eq_zero`: the hyperplane `{t = 0}` is a null set;
* `integral_le_two_mul_setIntegral`: `∫ F ≤ 2 ∫_{B_r⁺} H` when `F` and `F ∘ reflE` are bounded by
  `H` on `B_r⁺` and vanish on `{t > 0} \ B_r`;
* `bump`: the `ContDiffBump` with radii `5/4 < 3/2`; its gradient vanishes for `‖x‖ ≥ 3/2`;
* `cf u = bump · (u ∘ fold)` and `cG u Du`, its gradient off `{t = 0}` (measurable, bounded,
  supported in `B_{3/2}`), with the bounds `integral_cf_sq_le` and `integral_norm_cG_sq_le`. -/

/-! #### The reflection `(y, t) ↦ (y, -t)` -/

/-- The reflection `x ↦ x - 2 t e_d` in the hyperplane `{t = 0}`, as a linear map. -/
noncomputable def reflL (n : ℕ) : Space n →ₗ[ℝ] Space n where
  toFun x := x - (2 * vcoord x) • ed n
  map_add' x y := by
    have h : vcoord (x + y) = vcoord x + vcoord y := by simp [vcoord]
    rw [h, mul_add, add_smul]
    abel
  map_smul' a x := by
    have h : vcoord (a • x) = a * vcoord x := by simp [vcoord]
    rw [h, RingHom.id_apply, smul_sub, smul_smul]
    congr 2
    ring

lemma reflL_apply (x : Space n) : reflL n x = x - (2 * vcoord x) • ed n := rfl

lemma vcoord_reflL (x : Space n) : vcoord (reflL n x) = - vcoord x := by
  have h : vcoord (reflL n x) = vcoord x - (2 * vcoord x) * vcoord (ed n) := by
    simp [reflL_apply, vcoord]
  rw [h, vcoord_ed]
  ring

lemma reflL_reflL (x : Space n) : reflL n (reflL n x) = x := by
  rw [reflL_apply (reflL n x), vcoord_reflL, reflL_apply]
  module

lemma reflL_apply_castSucc (x : Space n) (i : Fin n) :
    reflL n x (Fin.castSucc i) = x (Fin.castSucc i) := by
  simp [reflL_apply, ed, Fin.castSucc_ne_last]

lemma norm_reflL (x : Space n) : ‖reflL n x‖ = ‖x‖ := by
  have h2 : ‖reflL n x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc,
      Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [reflL_apply_castSucc]
    · have h1 : reflL n x (Fin.last n) = - x (Fin.last n) := vcoord_reflL x
      rw [h1, norm_neg]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- The reflection as a linear isometry equivalence. -/
noncomputable def reflE (n : ℕ) : Space n ≃ₗᵢ[ℝ] Space n :=
  { LinearEquiv.ofInvolutive (reflL n) (fun x => reflL_reflL x) with
    norm_map' := norm_reflL }

lemma reflE_apply (x : Space n) : reflE n x = x - (2 * vcoord x) • ed n := rfl

lemma vcoord_reflE (x : Space n) : vcoord (reflE n x) = - vcoord x := vcoord_reflL x

lemma reflE_reflE (x : Space n) : reflE n (reflE n x) = x := reflL_reflL x

lemma norm_reflE (x : Space n) : ‖reflE n x‖ = ‖x‖ := (reflE n).norm_map x

lemma inner_reflE_left (v w : Space n) : ⟪reflE n v, w⟫_ℝ = ⟪v, reflE n w⟫_ℝ := by
  rw [reflE_apply, reflE_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm w (ed n), F1.inner_ed, F1.inner_ed]
  simp only [vcoord]
  ring

lemma fold_eq_reflE {x : Space n} (hx : vcoord x < 0) : fold x = reflE n x := by
  rw [reflE_apply]
  simp only [fold, abs_of_neg hx]
  congr 2
  ring

/-! #### The hyperplane `{t = 0}` is a null set -/

lemma volume_vcoord_eq_zero : volume {x : Space n | vcoord x = 0} = 0 := by
  set K : Submodule ℝ (Space n) :=
    LinearMap.ker ((EuclideanSpace.proj (Fin.last n) : Space n →L[ℝ] ℝ) : Space n →ₗ[ℝ] ℝ)
    with hK
  have hset : {x : Space n | vcoord x = 0} = (K : Set (Space n)) := by
    ext x
    simp [hK, vcoord]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  have hmem : ed n ∈ K := by
    rw [htop]
    exact Submodule.mem_top
  simp [hK, ed] at hmem

lemma ae_eq_halfSpace :
    ({x : Space n | 0 ≤ vcoord x} : Set (Space n)) =ᵐ[volume] {x : Space n | 0 < vcoord x} := by
  rw [← measure_symmDiff_eq_zero_iff]
  refine measure_mono_null (fun x hx => ?_) volume_vcoord_eq_zero
  simp only [Set.mem_symmDiff, Set.mem_ofPred_eq] at hx
  show vcoord x = 0
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact le_antisymm (not_lt.mp h2) h1
  · exact absurd h1.le h2

/-- Splitting `ℝⁿ⁺¹` into the two half-spaces and reflecting the lower one. -/
lemma integral_le_two_mul_setIntegral (F H : Space n → ℝ) (r : ℝ)
    (hF : ∀ x, 0 < vcoord x → F x ≤ (halfBall n r).indicator H x)
    (hFσ : ∀ x, 0 < vcoord x → F (reflE n x) ≤ (halfBall n r).indicator H x)
    (hH : IntegrableOn H (halfBall n r)) (hH0 : ∀ x ∈ halfBall n r, 0 ≤ H x) :
    ∫ x, F x ≤ 2 * ∫ x in halfBall n r, H x := by
  have hI0 : 0 ≤ ∫ x in halfBall n r, H x := setIntegral_nonneg (measurableSet_halfBall r) hH0
  by_cases hFi : Integrable F
  swap
  · rw [integral_undef hFi]
    linarith
  set P : Set (Space n) := {x | 0 < vcoord x} with hP_def
  have hP : MeasurableSet P := F1.measurableSet_halfSpace 0
  have hHP : IntegrableOn ((halfBall n r).indicator H) P :=
    (hH.integrable_indicator (measurableSet_halfBall r)).integrableOn
  have hHPeq : ∫ x in P, (halfBall n r).indicator H x = ∫ x in halfBall n r, H x := by
    have hset : P ∩ halfBall n r = halfBall n r := Set.inter_eq_right.mpr fun x hx => hx.2
    rw [setIntegral_indicator (measurableSet_halfBall r), hset]
  have h1 : ∫ x in P, F x ≤ ∫ x in halfBall n r, H x := by
    rw [← hHPeq]
    exact setIntegral_mono_on hFi.integrableOn hHP hP hF
  have hσ : MeasurePreserving (reflE n) := (reflE n).measurePreserving
  have hemb : MeasurableEmbedding (reflE n) := (reflE n).toHomeomorph.measurableEmbedding
  have hpre : (reflE n) ⁻¹' Pᶜ = {x : Space n | 0 ≤ vcoord x} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, hP_def, Set.mem_ofPred_eq, vcoord_reflE,
      not_lt]
    constructor <;> intro h <;> linarith
  have e2 : ∫ x in Pᶜ, F x = ∫ x in P, F (reflE n x) := by
    rw [← hσ.setIntegral_preimage_emb hemb F Pᶜ, hpre]
    exact setIntegral_congr_set ae_eq_halfSpace
  have hFσi : Integrable (fun x => F (reflE n x)) := (hσ.integrable_comp_emb hemb).mpr hFi
  have h2 : ∫ x in P, F (reflE n x) ≤ ∫ x in halfBall n r, H x := by
    rw [← hHPeq]
    exact setIntegral_mono_on hFσi.integrableOn hHP hP hFσ
  rw [← integral_add_compl hP hFi, e2]
  linarith

/-! #### The cut-off -/

/-- The cut-off `χ`: a smooth bump equal to `1` on `B_{5/4}` and to `0` off `B_{3/2}`. -/
noncomputable def bump (n : ℕ) : ContDiffBump (0 : Space n) where
  rIn := 5 / 4
  rOut := 3 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma bump_eq_zero {x : Space n} (hx : 3 / 2 ≤ ‖x‖) : bump n x = 0 :=
  (bump n).zero_of_le_dist (by rw [dist_zero_right]; exact hx)

lemma bump_eq_one {x : Space n} (hx : ‖x‖ ≤ 5 / 4) : bump n x = 1 :=
  (bump n).one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact hx)

lemma bump_nonneg (x : Space n) : 0 ≤ bump n x := (bump n).nonneg

lemma bump_le_one (x : Space n) : bump n x ≤ 1 := (bump n).le_one

lemma contDiff_bump : ContDiff ℝ 1 (bump n) := (bump n).contDiff

lemma gradient_bump_eq_zero {x : Space n} (hx : 3 / 2 ≤ ‖x‖) : gradient (bump n) x = 0 := by
  have hmin : IsLocalMin (bump n) x :=
    Filter.Eventually.of_forall fun y => by rw [bump_eq_zero hx]; exact bump_nonneg y
  show (toDual ℝ (Space n)).symm (fderiv ℝ (bump n) x) = 0
  rw [hmin.fderiv_eq_zero, map_zero]

lemma continuous_gradient_bump : Continuous (gradient (bump n : Space n → ℝ)) := by
  have h : gradient (bump n : Space n → ℝ) =
      fun x => (toDual ℝ (Space n)).symm (fderiv ℝ (bump n) x) := rfl
  rw [h]
  exact (toDual ℝ (Space n)).symm.continuous.comp (contDiff_bump.continuous_fderiv one_ne_zero)

lemma hasGradientAt_bump (x : Space n) : HasGradientAt (bump n) (gradient (bump n) x) x :=
  ((contDiff_bump.differentiable one_ne_zero) x).hasGradientAt

lemma exists_bound_gradient_bump :
    ∃ L, 0 ≤ L ∧ ∀ x : Space n, ‖gradient (bump n) x‖ ≤ L := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space n) (3 / 2)).exists_bound_of_continuousOn
    continuous_gradient_bump.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ 3 / 2
  · exact (hC x (by rw [Metric.mem_closedBall, dist_zero_right]; exact hx)).trans
      (le_max_left _ _)
  · rw [gradient_bump_eq_zero (le_of_lt (not_le.mp hx)), norm_zero]
    exact le_max_right _ _

/-! #### Leibniz and chain rules for gradients -/

lemma hasGradientAt_mul {f g : Space n → ℝ} {f' g' x : Space n} (hf : HasGradientAt f f' x)
    (hg : HasGradientAt g g' x) :
    HasGradientAt (fun y => f y * g y) (g x • f' + f x • g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf hg ⊢
  convert hf.mul hg using 1
  ext v
  simp
  ring

lemma hasGradientAt_comp_reflE {g : Space n → ℝ} {g' x : Space n}
    (hg : HasGradientAt g g' (reflE n x)) :
    HasGradientAt (fun y => g (reflE n y)) (reflE n g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hg ⊢
  have hL : HasFDerivAt (fun y => reflE n y)
      ((reflE n).toContinuousLinearEquiv : Space n →L[ℝ] Space n) x :=
    ((reflE n).toContinuousLinearEquiv : Space n →L[ℝ] Space n).hasFDerivAt
  have hD : (toDual ℝ (Space n)) (reflE n g') = ((toDual ℝ (Space n)) g').comp
      ((reflE n).toContinuousLinearEquiv : Space n →L[ℝ] Space n) := by
    ext v
    simp only [toDual_apply_apply, ContinuousLinearMap.comp_apply]
    exact inner_reflE_left g' v
  rw [hD]
  exact hg.comp x hL

/-! #### The cut-off even reflection and its gradient -/

/-- The cut-off even reflection `χ · (u ∘ fold)`. -/
noncomputable def cf (u : Space n → ℝ) (x : Space n) : ℝ := bump n x * u (fold x)

/-- The open set `{t > 0, ‖x‖ < 2}`. -/
def posSet (n : ℕ) : Set (Space n) := {x | 0 < vcoord x ∧ ‖x‖ < 2}

/-- The open set `{t < 0, ‖x‖ < 2}`. -/
def negSet (n : ℕ) : Set (Space n) := {x | vcoord x < 0 ∧ ‖x‖ < 2}

lemma isOpen_posSet : IsOpen (posSet n) :=
  (isOpen_lt continuous_const F1.continuous_vcoord).inter
    (isOpen_lt continuous_norm continuous_const)

lemma isOpen_negSet : IsOpen (negSet n) :=
  (isOpen_lt F1.continuous_vcoord continuous_const).inter
    (isOpen_lt continuous_norm continuous_const)

/-- The gradient of `cf u` off the hyperplane `{t = 0}` (and `0` on it). -/
noncomputable def cG (u : Space n → ℝ) (Du : Space n → Space n) (x : Space n) : Space n :=
  (posSet n).indicator (fun y => u y • gradient (bump n) y + bump n y • Du y) x +
    (negSet n).indicator
      (fun y => u (reflE n y) • gradient (bump n) y + bump n y • reflE n (Du (reflE n y))) x

lemma cf_eq_of_pos (u : Space n → ℝ) {x : Space n} (hx : 0 < vcoord x) :
    cf u x = bump n x * u x := by
  rw [cf, fold_of_nonneg hx.le]

lemma cf_eq_of_neg (u : Space n → ℝ) {x : Space n} (hx : vcoord x < 0) :
    cf u x = bump n x * u (reflE n x) := by
  rw [cf, fold_eq_reflE hx]

lemma cf_eq_zero (u : Space n → ℝ) {x : Space n} (hx : 3 / 2 ≤ ‖x‖) : cf u x = 0 := by
  rw [cf, bump_eq_zero hx, zero_mul]

lemma cf_eq_self (u : Space n → ℝ) {x : Space n} (hx : x ∈ halfBall n (5 / 4)) :
    cf u x = u x := by
  rw [cf_eq_of_pos u hx.2, bump_eq_one hx.1.le, one_mul]

lemma cG_eq_of_pos (u : Space n → ℝ) (Du : Space n → Space n) {x : Space n}
    (hx : 0 < vcoord x) (hx2 : ‖x‖ < 2) :
    cG u Du x = u x • gradient (bump n) x + bump n x • Du x := by
  have h1 : x ∈ posSet n := ⟨hx, hx2⟩
  have h2 : x ∉ negSet n := fun h => absurd h.1 (not_lt.mpr hx.le)
  rw [cG, Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]

lemma cG_eq_of_neg (u : Space n → ℝ) (Du : Space n → Space n) {x : Space n}
    (hx : vcoord x < 0) (hx2 : ‖x‖ < 2) :
    cG u Du x = u (reflE n x) • gradient (bump n) x + bump n x • reflE n (Du (reflE n x)) := by
  have h1 : x ∉ posSet n := fun h => absurd h.1 (not_lt.mpr hx.le)
  have h2 : x ∈ negSet n := ⟨hx, hx2⟩
  rw [cG, Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]

lemma cG_eq_zero (u : Space n → ℝ) (Du : Space n → Space n) {x : Space n}
    (hx : 3 / 2 ≤ ‖x‖) : cG u Du x = 0 := by
  have h1 : u x • gradient (bump n) x + bump n x • Du x = 0 := by
    rw [gradient_bump_eq_zero hx, bump_eq_zero hx, smul_zero, zero_smul, add_zero]
  have h2 : u (reflE n x) • gradient (bump n) x + bump n x • reflE n (Du (reflE n x)) = 0 := by
    rw [gradient_bump_eq_zero hx, bump_eq_zero hx, smul_zero, zero_smul, add_zero]
  have e1 : (posSet n).indicator (fun y => u y • gradient (bump n) y + bump n y • Du y) x = 0 :=
    Set.indicator_apply_eq_zero.mpr fun _ => h1
  have e2 : (negSet n).indicator (fun y => u (reflE n y) • gradient (bump n) y +
      bump n y • reflE n (Du (reflE n y))) x = 0 :=
    Set.indicator_apply_eq_zero.mpr fun _ => h2
  rw [cG, e1, e2, add_zero]

lemma cG_eq_zero_of_vcoord (u : Space n → ℝ) (Du : Space n → Space n) {x : Space n}
    (hx : vcoord x = 0) : cG u Du x = 0 := by
  have h1 : x ∉ posSet n := fun h => absurd h.1 (by rw [hx]; exact lt_irrefl 0)
  have h2 : x ∉ negSet n := fun h => absurd h.1 (by rw [hx]; exact lt_irrefl 0)
  rw [cG, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]

lemma continuous_cf {u : Space n → ℝ} (hu : ContinuousOn u (closedHalfBall n 2)) :
    Continuous (cf u) :=
  continuous_cutoff_fold hu (bump n).continuous (by norm_num : (3 / 2 : ℝ) < 2)
    (fun _ hx => bump_eq_zero hx)

lemma measurable_indicator_of_continuousOn {f : Space n → Space n} {s : Set (Space n)}
    (hs : IsOpen s) (hf : ContinuousOn f s) : Measurable (s.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hf.measurable_piecewise continuousOn_const hs.measurableSet

lemma measurable_cG {u : Space n → ℝ} {Du : Space n → Space n}
    (hu : ContinuousOn u (closedHalfBall n 2)) (hDu : ContinuousOn Du (closedHalfBall n 2)) :
    Measurable (cG u Du) := by
  have h1 : ContinuousOn (fun y => u y • gradient (bump n) y + bump n y • Du y) (posSet n) := by
    have hsub : posSet n ⊆ closedHalfBall n 2 := fun x hx => ⟨hx.2, hx.1.le⟩
    exact ((hu.mono hsub).smul continuous_gradient_bump.continuousOn).add
      ((bump n).continuous.continuousOn.smul (hDu.mono hsub))
  have h2 : ContinuousOn (fun y => u (reflE n y) • gradient (bump n) y +
      bump n y • reflE n (Du (reflE n y))) (negSet n) := by
    have hmaps : Set.MapsTo (reflE n) (negSet n) (closedHalfBall n 2) := fun x hx =>
      ⟨by rw [norm_reflE]; exact hx.2, by rw [vcoord_reflE]; linarith [hx.1]⟩
    have hu' : ContinuousOn (fun y => u (reflE n y)) (negSet n) :=
      hu.comp (reflE n).continuous.continuousOn hmaps
    have hDu' : ContinuousOn (fun y => reflE n (Du (reflE n y))) (negSet n) :=
      (reflE n).continuous.comp_continuousOn (hDu.comp (reflE n).continuous.continuousOn hmaps)
    exact (hu'.smul continuous_gradient_bump.continuousOn).add
      ((bump n).continuous.continuousOn.smul hDu')
  exact (measurable_indicator_of_continuousOn isOpen_posSet h1).add
    (measurable_indicator_of_continuousOn isOpen_negSet h2)

lemma norm_smul_add_smul_le {a b : ℝ} {v w : Space n} {L : ℝ} (hv : ‖v‖ ≤ L) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : ‖a • v + b • w‖ ≤ |a| * L + ‖w‖ := by
  calc ‖a • v + b • w‖ ≤ ‖a • v‖ + ‖b • w‖ := norm_add_le _ _
    _ = |a| * ‖v‖ + b * ‖w‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb0]
    _ ≤ |a| * L + 1 * ‖w‖ := add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg a))
        (mul_le_mul_of_nonneg_right hb1 (norm_nonneg w))
    _ = |a| * L + ‖w‖ := by ring

lemma norm_sq_smul_add_smul_le {a b : ℝ} {v w : Space n} {L : ℝ} (hv : ‖v‖ ≤ L) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : ‖a • v + b • w‖ ^ 2 ≤ 2 * L ^ 2 * a ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := norm_smul_add_smul_le (a := a) (w := w) hv hb0 hb1
  have hL : 0 ≤ L := (norm_nonneg v).trans hv
  have h2 : ‖a • v + b • w‖ ^ 2 ≤ (|a| * L + ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have h3 : (|a| * L + ‖w‖) ^ 2 ≤ 2 * L ^ 2 * a ^ 2 + 2 * ‖w‖ ^ 2 := by
    have e : 2 * L ^ 2 * a ^ 2 + 2 * ‖w‖ ^ 2 - (|a| * L + ‖w‖) ^ 2 = (|a| * L - ‖w‖) ^ 2 := by
      rw [← sq_abs a]
      ring
    nlinarith [sq_nonneg (|a| * L - ‖w‖)]
  exact h2.trans h3

lemma exists_bound_cG {u : Space n → ℝ} {Du : Space n → Space n}
    (hu : ContinuousOn u (closedHalfBall n 2)) (hDu : ContinuousOn Du (closedHalfBall n 2)) :
    ∃ C, ∀ x, ‖cG u Du x‖ ≤ C := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_gradient_bump (n := n)
  have hK := isCompact_halfBallLe (n := n) (3 / 2)
  have hKsub : {x : Space n | ‖x‖ ≤ 3 / 2 ∧ 0 ≤ vcoord x} ⊆ closedHalfBall n 2 :=
    fun x hx => ⟨by linarith [hx.1], hx.2⟩
  obtain ⟨Cu, hCu⟩ := hK.exists_bound_of_continuousOn (hu.mono hKsub)
  obtain ⟨CD, hCD⟩ := hK.exists_bound_of_continuousOn (hDu.mono hKsub)
  have h0K : (0 : Space n) ∈ {x : Space n | ‖x‖ ≤ 3 / 2 ∧ 0 ≤ vcoord x} :=
    ⟨by rw [norm_zero]; norm_num, by simp [vcoord]⟩
  have hCu0 : 0 ≤ Cu := (norm_nonneg _).trans (hCu 0 h0K)
  have hCD0 : 0 ≤ CD := (norm_nonneg _).trans (hCD 0 h0K)
  refine ⟨Cu * L + CD, fun x => ?_⟩
  have key : ∀ (a b : ℝ) (v w : Space n), ‖a‖ ≤ Cu → ‖v‖ ≤ L → 0 ≤ b → b ≤ 1 → ‖w‖ ≤ CD →
      ‖a • v + b • w‖ ≤ Cu * L + CD := by
    intro a b v w ha hv hb0 hb1 hw
    refine (norm_smul_add_smul_le hv hb0 hb1).trans ?_
    rw [← Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_right ha hL0) hw
  by_cases hx : 3 / 2 ≤ ‖x‖
  · rw [cG_eq_zero u Du hx, norm_zero]
    positivity
  have hx' : ‖x‖ < 3 / 2 := lt_of_not_ge hx
  rcases lt_trichotomy (vcoord x) 0 with hneg | hzero | hpos
  · rw [cG_eq_of_neg u Du hneg (by linarith)]
    have hσK : reflE n x ∈ {x : Space n | ‖x‖ ≤ 3 / 2 ∧ 0 ≤ vcoord x} :=
      ⟨by rw [norm_reflE]; exact hx'.le, by rw [vcoord_reflE]; linarith⟩
    exact key _ _ _ _ (hCu _ hσK) (hL x) (bump_nonneg x) (bump_le_one x)
      (by rw [LinearIsometryEquiv.norm_map]; exact hCD _ hσK)
  · rw [cG_eq_zero_of_vcoord u Du hzero, norm_zero]
    positivity
  · rw [cG_eq_of_pos u Du hpos (by linarith)]
    have hxK : x ∈ {x : Space n | ‖x‖ ≤ 3 / 2 ∧ 0 ≤ vcoord x} := ⟨hx'.le, hpos.le⟩
    exact key _ _ _ _ (hCu _ hxK) (hL x) (bump_nonneg x) (bump_le_one x) (hCD _ hxK)

lemma hasGradientAt_cf {u : Space n → ℝ} {Du : Space n → Space n}
    (hgrad : ∀ x ∈ halfBall n 2, HasGradientAt u (Du x) x) {x : Space n} (hx : vcoord x ≠ 0) :
    HasGradientAt (cf u) (cG u Du x) x := by
  by_cases hx2 : ‖x‖ < 2
  · rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [cG_eq_of_neg u Du hneg hx2]
      have hev : cf u =ᶠ[𝓝 x] fun y => bump n y * u (reflE n y) := by
        filter_upwards [(isOpen_lt F1.continuous_vcoord continuous_const).mem_nhds hneg] with y hy
        exact cf_eq_of_neg u hy
      have hσx : reflE n x ∈ halfBall n 2 :=
        ⟨by rw [norm_reflE]; exact hx2, by rw [vcoord_reflE]; linarith⟩
      exact (hasGradientAt_mul (hasGradientAt_bump x)
        (hasGradientAt_comp_reflE (hgrad _ hσx))).congr_of_eventuallyEq hev
    · rw [cG_eq_of_pos u Du hpos hx2]
      have hev : cf u =ᶠ[𝓝 x] fun y => bump n y * u y := by
        filter_upwards [(isOpen_lt continuous_const F1.continuous_vcoord).mem_nhds hpos] with y hy
        exact cf_eq_of_pos u hy
      exact (hasGradientAt_mul (hasGradientAt_bump x) (hgrad x ⟨hx2, hpos⟩)).congr_of_eventuallyEq
        hev
  · have hx2' : (3 / 2 : ℝ) < ‖x‖ := by linarith [not_lt.mp hx2]
    rw [cG_eq_zero u Du hx2'.le]
    have hev : cf u =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx2'] with y hy
      exact cf_eq_zero u hy.le
    exact (hasGradientAt_const x (0 : ℝ)).congr_of_eventuallyEq hev

lemma sq_bump_mul_le (y a : ℝ) (hb0 : 0 ≤ y) (hb1 : y ≤ 1) : (y * a) ^ 2 ≤ a ^ 2 := by
  rw [mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg a) (pow_le_one₀ hb0 hb1)

/-- The `L²` bound of the cut-off even reflection. -/
lemma integral_cf_sq_le {u : Space n → ℝ} (hu : ContinuousOn u (closedHalfBall n 2)) :
    ∫ x, cf u x ^ 2 ≤ 2 * ∫ x in halfBall n (3 / 2), u x ^ 2 := by
  apply integral_le_two_mul_setIntegral (fun x => cf u x ^ 2) (fun x => u x ^ 2) (3 / 2)
  · intro x hx
    by_cases hx2 : ‖x‖ < 3 / 2
    · rw [Set.indicator_of_mem (show x ∈ halfBall n (3 / 2) from ⟨hx2, hx⟩), cf_eq_of_pos u hx]
      exact sq_bump_mul_le _ _ (bump_nonneg x) (bump_le_one x)
    · rw [cf_eq_zero u (not_lt.mp hx2), zero_pow two_ne_zero]
      exact Set.indicator_nonneg (fun y _ => sq_nonneg (u y)) x
  · intro x hx
    have hσ : vcoord (reflE n x) < 0 := by rw [vcoord_reflE]; linarith
    by_cases hx2 : ‖x‖ < 3 / 2
    · rw [Set.indicator_of_mem (show x ∈ halfBall n (3 / 2) from ⟨hx2, hx⟩), cf_eq_of_neg u hσ,
        reflE_reflE]
      exact sq_bump_mul_le _ _ (bump_nonneg _) (bump_le_one _)
    · rw [cf_eq_zero u (by rw [norm_reflE]; exact not_lt.mp hx2), zero_pow two_ne_zero]
      exact Set.indicator_nonneg (fun y _ => sq_nonneg (u y)) x
  · exact integrableOn_halfBall_of_continuousOn (by norm_num) (hu.pow 2)
  · intro x _
    exact sq_nonneg _

/-- The `L²` bound of the gradient of the cut-off even reflection. -/
lemma integral_norm_cG_sq_le {u : Space n → ℝ} {Du : Space n → Space n}
    (hu : ContinuousOn u (closedHalfBall n 2)) (hDu : ContinuousOn Du (closedHalfBall n 2))
    {L : ℝ} (hL : ∀ x, ‖gradient (bump n) x‖ ≤ L) :
    ∫ x, ‖cG u Du x‖ ^ 2 ≤
      2 * ∫ x in halfBall n (3 / 2), (2 * L ^ 2 * u x ^ 2 + 2 * ‖Du x‖ ^ 2) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  apply integral_le_two_mul_setIntegral (fun x => ‖cG u Du x‖ ^ 2)
    (fun x => 2 * L ^ 2 * u x ^ 2 + 2 * ‖Du x‖ ^ 2) (3 / 2)
  · intro x hx
    by_cases hx2 : ‖x‖ < 3 / 2
    · rw [Set.indicator_of_mem (show x ∈ halfBall n (3 / 2) from ⟨hx2, hx⟩),
        cG_eq_of_pos u Du hx (by linarith)]
      exact norm_sq_smul_add_smul_le (hL x) (bump_nonneg x) (bump_le_one x)
    · rw [cG_eq_zero u Du (not_lt.mp hx2), norm_zero, zero_pow two_ne_zero]
      exact Set.indicator_nonneg (fun y _ => by positivity) x
  · intro x hx
    have hσ : vcoord (reflE n x) < 0 := by rw [vcoord_reflE]; linarith
    by_cases hx2 : ‖x‖ < 3 / 2
    · rw [Set.indicator_of_mem (show x ∈ halfBall n (3 / 2) from ⟨hx2, hx⟩),
        cG_eq_of_neg u Du hσ (by rw [norm_reflE]; linarith), reflE_reflE]
      have h := norm_sq_smul_add_smul_le (a := u x) (w := reflE n (Du x)) (hL (reflE n x))
        (bump_nonneg (reflE n x)) (bump_le_one _)
      rwa [LinearIsometryEquiv.norm_map] at h
    · rw [cG_eq_zero u Du (by rw [norm_reflE]; exact not_lt.mp hx2), norm_zero,
        zero_pow two_ne_zero]
      exact Set.indicator_nonneg (fun y _ => by positivity) x
  · exact integrableOn_halfBall_of_continuousOn (by norm_num)
      ((continuousOn_const.mul (hu.pow 2)).add (continuousOn_const.mul (hDu.norm.pow 2)))
  · intro x _
    positivity

end W_R1_subseq

/-- Compactness in `L²(B_{5/4}⁺)` from `H¹(B_{3/2}⁺)` bounds, for functions that are `C¹` in the
open half-ball and continuous with their gradients up to the flat boundary (F3 applied to the
cut-off even reflections).

Plan: let `fold x = x - (t - |t|) e_d` (so `fold (y, t) = (y, |t|)`, `‖fold x‖ = ‖x‖`), let `χ` be
the `ContDiffBump` with radii `5/4 < 3/2`, and `f j = χ · (u j ∘ fold)`. Then
* `f j` is continuous and vanishes for `‖x‖ ≥ 3/2`;
* `∫ (f j)² ≤ 2 ∫_{B_{3/2}⁺} (u j)² ≤ 2M` (Fubini through `lift` and `integral_comp_abs`, or the
  reflection `x ↦ x - 2 t e_d`, a measure preserving linear isometry);
* off `{t = 0}`, `f j` has gradient `G j = (u j ∘ fold) ∇χ + χ · R (Du j ∘ fold)` (`R` = reflection
  for `t < 0`), which is measurable, bounded, supported in `B_{3/2}`, with
  `∫ ‖G j‖² ≤ (4 sup‖∇χ‖² + 4) M`;
* `integral_sub_translate_sq_le` gives the translation bound, and `exists_L2_convergent_subseq`
  (F3) a subsequence converging in `L²(ℝⁿ⁺¹)` to some `g`;
* since `f j = u j` on `B_{5/4}⁺`, `∫_{B_{5/4}⁺} (u (φ j) - g)² ≤ ∫ (f (φ j) - g)² → 0`. -/
lemma exists_L2_subseq_halfBall (u : ℕ → Space n → ℝ) (Du : ℕ → Space n → Space n) (M : ℝ)
    (hcont : ∀ j, ContinuousOn (u j) (closedHalfBall n 2))
    (hDcont : ∀ j, ContinuousOn (Du j) (closedHalfBall n 2))
    (hgrad : ∀ j, ∀ x ∈ halfBall n 2, HasGradientAt (u j) (Du j x) x)
    (hL2 : ∀ j, ∫ x in halfBall n (3 / 2), u j x ^ 2 ≤ M)
    (hH1 : ∀ j, ∫ x in halfBall n (3 / 2), ‖Du j x‖ ^ 2 ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : Space n → ℝ), StrictMono φ ∧ MemLp g 2 ∧
      Tendsto (fun j => ∫ x in halfBall n (5 / 4), (u (φ j) x - g x) ^ 2) atTop (𝓝 0) := by
  obtain ⟨L, hL0, hL⟩ := W_R1_subseq.exists_bound_gradient_bump (n := n)
  have hM0 : 0 ≤ M :=
    (setIntegral_nonneg (measurableSet_halfBall _) fun x _ => sq_nonneg (u 0 x)).trans (hL2 0)
  set f : ℕ → Space n → ℝ := fun j => W_R1_subseq.cf (u j) with hf_def
  set M' : ℝ := (4 * L ^ 2 + 4) * M + 2 * M with hM'_def
  have hfc : ∀ j, Continuous (f j) := fun j => W_R1_subseq.continuous_cf (hcont j)
  have hfs : ∀ j x, (3 / 2 : ℝ) ≤ ‖x‖ → f j x = 0 := fun j x hx => W_R1_subseq.cf_eq_zero _ hx
  have hA : 0 ≤ (4 * L ^ 2 + 4) * M := by positivity
  have hbdd : ∀ j, ∫ x, f j x ^ 2 ≤ M' := by
    intro j
    have h1 := W_R1_subseq.integral_cf_sq_le (hcont j)
    have h2 := hL2 j
    show ∫ x, W_R1_subseq.cf (u j) x ^ 2 ≤ M'
    linarith
  have hG : ∀ j, ∫ x, ‖W_R1_subseq.cG (u j) (Du j) x‖ ^ 2 ≤ (4 * L ^ 2 + 4) * M := by
    intro j
    have h1 := W_R1_subseq.integral_norm_cG_sq_le (hcont j) (hDcont j) hL
    have i1 : IntegrableOn (fun x => u j x ^ 2) (halfBall n (3 / 2)) :=
      integrableOn_halfBall_of_continuousOn (by norm_num) ((hcont j).pow 2)
    have i2 : IntegrableOn (fun x => ‖Du j x‖ ^ 2) (halfBall n (3 / 2)) :=
      integrableOn_halfBall_of_continuousOn (by norm_num) ((hDcont j).norm.pow 2)
    have h2 : ∫ x in halfBall n (3 / 2), (2 * L ^ 2 * u j x ^ 2 + 2 * ‖Du j x‖ ^ 2) =
        2 * L ^ 2 * (∫ x in halfBall n (3 / 2), u j x ^ 2) +
          2 * ∫ x in halfBall n (3 / 2), ‖Du j x‖ ^ 2 := by
      rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
    have h3 : 2 * L ^ 2 * ∫ x in halfBall n (3 / 2), u j x ^ 2 ≤ 2 * L ^ 2 * M :=
      mul_le_mul_of_nonneg_left (hL2 j) (by positivity)
    have h4 := hH1 j
    rw [h2] at h1
    linarith
  have htrans : ∀ j (h : Space n), ∫ x, (f j (x + h) - f j x) ^ 2 ≤ M' * ‖h‖ ^ 2 := by
    intro j h
    have h1 := integral_sub_translate_sq_le (W_R1_subseq.cf (u j))
      (W_R1_subseq.cG (u j) (Du j)) (3 / 2)
      (W_R1_subseq.continuous_cf (hcont j)) (fun x hx => W_R1_subseq.cf_eq_zero _ hx)
      (fun x hx => W_R1_subseq.cG_eq_zero _ _ hx) (W_R1_subseq.measurable_cG (hcont j) (hDcont j))
      (W_R1_subseq.exists_bound_cG (hcont j) (hDcont j))
      (fun x hx => W_R1_subseq.hasGradientAt_cf (hgrad j) hx) h
    have h2 : (∫ x, ‖W_R1_subseq.cG (u j) (Du j) x‖ ^ 2) * ‖h‖ ^ 2 ≤ M' * ‖h‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have := hG j
      linarith
    exact h1.trans h2
  obtain ⟨φ, g, hφ, hg, hlim⟩ := exists_L2_convergent_subseq f (3 / 2) M' hfc hfs hbdd htrans
  refine ⟨φ, g, hφ, hg, ?_⟩
  have hmem : ∀ j, MemLp (f j) 2 := fun j =>
    (hfc j).memLp_of_hasCompactSupport (F3.hasCompactSupport_of_eq_zero (hfs j))
  have hle : ∀ j, ∫ x in halfBall n (5 / 4), (u (φ j) x - g x) ^ 2 ≤
      ∫ x, (f (φ j) x - g x) ^ 2 := by
    intro j
    have heq : ∫ x in halfBall n (5 / 4), (u (φ j) x - g x) ^ 2 =
        ∫ x in halfBall n (5 / 4), (f (φ j) x - g x) ^ 2 := by
      refine setIntegral_congr_fun (measurableSet_halfBall _) fun x hx => ?_
      simp only [hf_def, W_R1_subseq.cf_eq_self _ hx]
    rw [heq]
    exact setIntegral_le_integral ((hmem (φ j)).sub hg).integrable_sq
      (Eventually.of_forall fun x => sq_nonneg _)
  have hnn : ∀ j, 0 ≤ ∫ x in halfBall n (5 / 4), (u (φ j) x - g x) ^ 2 := fun j =>
    setIntegral_nonneg (measurableSet_halfBall _) fun x _ => sq_nonneg _
  exact squeeze_zero hnn hle hlim

/-! ### Step 5: the limit is weakly harmonic -/

lemma integral_lap_eq_zero_of_tendsto (u : ℕ → Space n → ℝ) (g : Space n → ℝ)
    (hg : MemLp g 2) (hu : ∀ j, MemLp (u j) 2 (volume.restrict (halfBall n (5 / 4))))
    (hconv : Tendsto (fun j => ∫ x in halfBall n (5 / 4), (u j x - g x) ^ 2) atTop (𝓝 0))
    (ψ : Space n → ℝ) (hψ : ContDiff ℝ 2 ψ) (ρ : ℝ) (hρ : ρ < 5 / 4)
    (hψs : ∀ x, ρ ≤ ‖x‖ → ψ x = 0)
    (hlim : Tendsto (fun j => ∫ x in {x : Space n | 0 < vcoord x}, u j x * lap ψ x) atTop
      (𝓝 0)) :
    ∫ x in halfBall n (5 / 4), g x * lap ψ x = 0 := by
  have := isFiniteMeasure_halfBall (n := n) (5 / 4)
  have hlc := continuous_lap hψ
  have hcs := hasCompactSupport_lap hψs
  obtain ⟨L, hL⟩ := hlc.bounded_above_of_compact_support hcs
  have hlapL2 : MemLp (lap ψ) 2 (volume.restrict (halfBall n (5 / 4))) :=
    (hlc.memLp_of_hasCompactSupport hcs).restrict _
  have hint : ∀ f : Space n → ℝ, MemLp f 2 (volume.restrict (halfBall n (5 / 4))) →
      IntegrableOn (fun x => f x * lap ψ x) (halfBall n (5 / 4)) := by
    intro f hf
    have h1 : Integrable f (volume.restrict (halfBall n (5 / 4))) := hf.integrable one_le_two
    have h2 := h1.bdd_mul (c := L) hlc.aestronglyMeasurable (Eventually.of_forall hL)
    have h3 : (fun x => lap ψ x * f x) = fun x => f x * lap ψ x := by funext x; ring
    rw [h3] at h2
    exact h2
  -- the integrals over `{t > 0}` are integrals over `B_{5/4}⁺`
  have hconv1 : ∀ j, ∫ x in {x : Space n | 0 < vcoord x}, u j x * lap ψ x
      = ∫ x in halfBall n (5 / 4), u j x * lap ψ x := by
    intro j
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (F1.measurableSet_halfSpace 0)
      (fun x (hx : x ∈ halfBall n (5 / 4)) => hx.2)
    intro x hx
    have h2 : 0 < vcoord x := hx.1
    have h3 : ¬ (‖x‖ < 5 / 4 ∧ 0 < vcoord x) := hx.2
    have h4 : ρ < ‖x‖ := by
      by_contra h5
      exact h3 ⟨by linarith [not_lt.mp h5], h2⟩
    simp [lap_eq_zero_of_norm_gt hψs h4]
  have hdiff : ∀ j, |(∫ x in halfBall n (5 / 4), u j x * lap ψ x) -
      ∫ x in halfBall n (5 / 4), g x * lap ψ x| ≤
      Real.sqrt (∫ x in halfBall n (5 / 4), (u j x - g x) ^ 2) *
        Real.sqrt (∫ x in halfBall n (5 / 4), lap ψ x ^ 2) := by
    intro j
    have e : (∫ x in halfBall n (5 / 4), u j x * lap ψ x) - ∫ x in halfBall n (5 / 4), g x * lap ψ x
        = ∫ x in halfBall n (5 / 4), (u j x - g x) * lap ψ x := by
      calc _ = ∫ x in halfBall n (5 / 4), (u j x * lap ψ x - g x * lap ψ x) :=
            (integral_sub (hint _ (hu j)) (hint _ (hg.restrict _))).symm
        _ = _ := by congr 1; funext x; ring
    rw [e]
    exact abs_setIntegral_mul_le_sqrt ((hu j).sub (hg.restrict _)) hlapL2
  have h0 : Tendsto (fun j => Real.sqrt (∫ x in halfBall n (5 / 4), (u j x - g x) ^ 2) *
      Real.sqrt (∫ x in halfBall n (5 / 4), lap ψ x ^ 2)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hconv).mul_const
      (Real.sqrt (∫ x in halfBall n (5 / 4), lap ψ x ^ 2))
    simpa using this
  have hT : Tendsto (fun j => ∫ x in halfBall n (5 / 4), u j x * lap ψ x) atTop
      (𝓝 (∫ x in halfBall n (5 / 4), g x * lap ψ x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => by rw [Real.norm_eq_abs]; exact hdiff j)
      h0
  have hT0 : Tendsto (fun j => ∫ x in halfBall n (5 / 4), u j x * lap ψ x) atTop (𝓝 0) := by
    simpa only [hconv1] using hlim
  exact tendsto_nhds_unique hT hT0

/-! ### Step 6: Weyl's lemma and unique continuation -/

/-- The Laplacian as a sum of second partial derivatives. -/
lemma lap_eq_sum_pd {F : Space n → ℝ} (hF : ContDiff ℝ 2 F) (x : Space n) :
    lap F x = ∑ i, fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)) x
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i) := by
  rw [lap_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ i
  have hG : Differentiable ℝ (gradient F) := (contDiff_gradient hF).differentiable (by norm_num)
  have e : (fun y => fderiv ℝ F y b) = fun y => (innerSL ℝ b) (gradient F y) := by
    funext y
    show fderiv ℝ F y b = ⟪b, (InnerProductSpace.toDual ℝ (Space n)).symm (fderiv ℝ F y)⟫_ℝ
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have h := (innerSL ℝ b).hasFDerivAt.comp x (hG x).hasFDerivAt
  rw [e, show (fun y => (innerSL ℝ b) (gradient F y)) = (innerSL ℝ b) ∘ gradient F from rfl,
    h.fderiv]
  simp

/-- Adapted from PDEAtlas, `PDE/FDeriv/Calculus/Convolution.lean` (`partialDeriv_convolution_right`). -/
lemma fderiv_convolution_right_apply {u k : Space n → ℝ} (hu : LocallyIntegrable u)
    (hk : HasCompactSupport k) (hk1 : ContDiff ℝ 1 k) (x v : Space n) :
    fderiv ℝ (convolution u k (ContinuousLinearMap.lsmul ℝ ℝ).flip volume) x v =
      convolution u (fun a => fderiv ℝ k a v) (ContinuousLinearMap.lsmul ℝ ℝ).flip volume x := by
  rw [(hk.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ).flip hu hk1 x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ).flip hu (hk.fderiv ℝ)
    (hk1.continuous_fderiv one_ne_zero) x v

/-- Adapted from PDEAtlas, `PDE/FDeriv/Calculus/Convolution.lean` (`laplacian_convolution_right`). -/
lemma lap_convolution_right {u k : Space n → ℝ} (hu : LocallyIntegrable u)
    (hk : HasCompactSupport k) (hk2 : ContDiff ℝ 2 k) (x : Space n) :
    lap (convolution u k (ContinuousLinearMap.lsmul ℝ ℝ).flip volume) x =
      convolution u (lap k) (ContinuousLinearMap.lsmul ℝ ℝ).flip volume x := by
  set L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip with hL
  set b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ with hb
  have hk1 : ContDiff ℝ 1 k := hk2.of_le (by norm_num)
  have hpd : ∀ i, ContDiff ℝ 1 (fun a => fderiv ℝ k a (b i)) := fun i =>
    (hk2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hpdc : ∀ i, HasCompactSupport (fun a => fderiv ℝ k a (b i)) := fun i =>
    hk.fderiv_apply ℝ (b i)
  have hpd2c : ∀ i, Continuous (fun a => fderiv ℝ (fun a => fderiv ℝ k a (b i)) a (b i)) :=
    fun i => ((hpd i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpd2s : ∀ i, HasCompactSupport (fun a => fderiv ℝ (fun a => fderiv ℝ k a (b i)) a (b i)) :=
    fun i => (hpdc i).fderiv_apply ℝ (b i)
  have hC2 : ContDiff ℝ 2 (convolution u k L volume) := hk.contDiff_convolution_right L hu hk2
  rw [lap_eq_sum_pd hC2 x, ← hb]
  have step : ∀ i, fderiv ℝ (fun y => fderiv ℝ (convolution u k L volume) y (b i)) x (b i)
      = convolution u (fun a => fderiv ℝ (fun a => fderiv ℝ k a (b i)) a (b i)) L volume x := by
    intro i
    have e : (fun y => fderiv ℝ (convolution u k L volume) y (b i)) =
        convolution u (fun a => fderiv ℝ k a (b i)) L volume :=
      funext fun y => fderiv_convolution_right_apply hu hk hk1 y (b i)
    rw [e]
    exact fderiv_convolution_right_apply hu (hpdc i) (hpd i) x (b i)
  simp_rw [step]
  have hlapk : lap k = fun a => ∑ i, fderiv ℝ (fun a => fderiv ℝ k a (b i)) a (b i) :=
    funext (lap_eq_sum_pd hk2)
  rw [hlapk]
  simp only [convolution_def]
  rw [← integral_finsetSum]
  · congr 1
    funext t
    rw [map_sum]
  · intro i _
    exact (hpd2s i).convolutionExists_right L hu (hpd2c i) x

/-- The Laplacian of a mollification falls on the smooth compactly supported kernel. -/
lemma lap_convolution_left {k u : Space n → ℝ} (hk : HasCompactSupport k) (hk2 : ContDiff ℝ 2 k)
    (hu : LocallyIntegrable u) (x : Space n) :
    lap (convolution k u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x =
      convolution (lap k) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have e1 : convolution k u (ContinuousLinearMap.lsmul ℝ ℝ) volume =
      convolution u k (ContinuousLinearMap.lsmul ℝ ℝ).flip volume := by
    rw [convolution_flip]
  have e2 : convolution (lap k) u (ContinuousLinearMap.lsmul ℝ ℝ) volume =
      convolution u (lap k) (ContinuousLinearMap.lsmul ℝ ℝ).flip volume := by
    rw [convolution_flip]
  rw [e1, e2]
  exact lap_convolution_right hu hk hk2 x

/-- The Laplacian commutes with the point reflection `z ↦ x - z`. -/
lemma lap_comp_sub {k : Space n → ℝ} (hk : ContDiff ℝ 2 k) (x y : Space n) :
    lap (fun z => k (x - z)) y = lap k (x - y) := by
  have hk1 : Differentiable ℝ k := hk.differentiable (by norm_num)
  have hsub : ∀ z : Space n, HasFDerivAt (fun z : Space n => x - z)
      (-ContinuousLinearMap.id ℝ (Space n)) z := fun z => (hasFDerivAt_id z).const_sub x
  have hg : ∀ z, gradient (fun z => k (x - z)) z = -(gradient k (x - z)) := by
    intro z
    have h2 : HasGradientAt k (gradient k (x - z)) (x - z) := (hk1 _).hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt] at h2
    have h3 := h2.comp z (hsub z)
    have h4 : HasGradientAt (fun z => k (x - z)) (-(gradient k (x - z))) z := by
      rw [hasGradientAt_iff_hasFDerivAt]
      exact h3.congr_fderiv (by ext w; simp)
    exact h4.gradient
  have hgf : gradient (fun z => k (x - z)) = fun z => -(gradient k (x - z)) := funext hg
  unfold lap divergence
  rw [hgf]
  have hG : Differentiable ℝ (gradient k) := (contDiff_gradient hk).differentiable (by norm_num)
  have h5 : HasFDerivAt (fun z => -(gradient k (x - z))) (fderiv ℝ (gradient k) (x - y)) y := by
    have h6 := ((hG (x - y)).hasFDerivAt.comp y (hsub y)).neg
    exact h6.congr_fderiv (by ext w; simp)
  rw [h5.fderiv]

lemma ellOp_id_eq_lap (F : Space n → ℝ) (x : Space n) :
    ellOp (fun _ => ContinuousLinearMap.id ℝ (Space n)) (fun _ => 0) (fun _ => 0) F x = lap F x := by
  simp [ellOp, lap]

/-- A mollification (with a kernel of radius `≤ 1/8`) of a weakly harmonic function vanishing on
`{t ≤ 0}` vanishes on `B_{9/8}`. -/
lemma mollified_eq_zero (u : Space n → ℝ) (hu : LocallyIntegrable u)
    (hzero : ∀ x, vcoord x ≤ 0 → u x = 0)
    (hharm : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → ∀ ρ < 5 / 4, (∀ x, ρ ≤ ‖x‖ → ψ x = 0) →
      ∫ x, u x * lap ψ x = 0)
    (φ : ContDiffBump (0 : Space n)) (hφ : φ.rOut ≤ 1 / 8) :
    ∀ x ∈ ball (0 : Space n) (9 / 8),
      convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
  set ρ : Space n → ℝ := φ.normed volume with hρ
  set F : Space n → ℝ := convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hF
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρ2 : ContDiff ℝ 2 ρ := φ.contDiff_normed
  have hρ0 : ∀ t : Space n, φ.rOut ≤ ‖t‖ → ρ t = 0 := by
    intro t ht
    have : t ∉ Function.support ρ := by
      rw [hρ, φ.support_normed_eq]
      simpa using ht
    simpa [Function.mem_support] using this
  have hF2 : ContDiff ℝ 2 F := hρc.contDiff_convolution_left _ hρ2 hu
  have hrpos : 0 < φ.rOut := φ.rIn_pos.trans φ.rIn_lt_rOut
  -- `F` vanishes below the level `-rOut`
  have hFlow : ∀ x : Space n, vcoord x < -φ.rOut → F x = 0 := by
    intro x hx
    rw [hF, convolution_def]
    have h0 : ∀ t : Space n, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (u (x - t)) = 0 := by
      intro t
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      by_cases ht : φ.rOut ≤ ‖t‖
      · rw [hρ0 t ht, zero_mul]
      · push Not at ht
        have hvt : |vcoord t| ≤ ‖t‖ := by
          calc |vcoord t| = ‖t (Fin.last n)‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖t‖ := PiLp.norm_apply_le t (Fin.last n)
        have hv : vcoord (x - t) ≤ 0 := by
          have : vcoord (x - t) = vcoord x - vcoord t := by simp [vcoord]
          rw [this]
          linarith [neg_abs_le (vcoord t)]
        rw [hzero _ hv, mul_zero]
    simp [h0]
  -- `F` is harmonic in `B_{9/8}`
  have hFharm : ∀ x ∈ ball (0 : Space n) (9 / 8),
      ellOp (fun _ => ContinuousLinearMap.id ℝ (Space n)) (fun _ => 0) (fun _ => 0) F x = 0 := by
    intro x hx
    rw [ellOp_id_eq_lap, hF, lap_convolution_left hρc hρ2 hu x, convolution_eq_swap]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have hxn : ‖x‖ < 9 / 8 := by simpa using hx
    have hψ2 : ContDiff ℝ 2 (fun z => ρ (x - z)) := hρ2.comp (contDiff_const.sub contDiff_id)
    have hψs : ∀ z : Space n, ‖x‖ + φ.rOut ≤ ‖z‖ → ρ (x - z) = 0 := by
      intro z hz
      apply hρ0
      have := norm_sub_norm_le z x
      rw [norm_sub_rev]
      linarith
    have h := hharm (fun z => ρ (x - z)) hψ2 (‖x‖ + φ.rOut) (by linarith) hψs
    rw [← h]
    congr 1
    funext t
    rw [lap_comp_sub hρ2 x t, mul_comm]
  -- weak unique continuation from the lower half
  set x₀ : Space n := (-(1 / 2 : ℝ)) • ed n with hx₀
  have hed : ‖ed n‖ = 1 := by simp [ed]
  have hvx₀ : vcoord x₀ = -(1 / 2) := by
    rw [hx₀, vcoord_smul]
    simp [vcoord, ed]
  have hx₀mem : x₀ ∈ ball (0 : Space n) (9 / 8) := by
    rw [mem_ball_zero_iff, hx₀, norm_smul, hed]
    norm_num
  have hloc : ∀ᶠ x in 𝓝 x₀, F x = 0 := by
    have hopen : IsOpen {x : Space n | vcoord x < -φ.rOut} :=
      isOpen_lt F1.continuous_vcoord continuous_const
    filter_upwards [hopen.mem_nhds (show vcoord x₀ < -φ.rOut by rw [hvx₀]; linarith)] with x hx
    exact hFlow x hx
  exact weak_ucp isOpen_ball (convex_ball _ _).isPreconnected
    (fun _ => ContinuousLinearMap.id ℝ (Space n)) (fun _ => 0) (fun _ => 0) contDiffOn_const
    (fun _ _ ξ η => rfl)
    (fun _ _ ξ hξ => by
      simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.mpr hξ) 2)
    continuousOn_const continuousOn_const F hF2.contDiffOn hFharm x₀ hx₀mem hloc

/-- A locally integrable function vanishing on `{t ≤ 0}` and weakly harmonic in `B_{5/4}`
vanishes a.e. on `B_1` (mollification and weak unique continuation). -/
lemma ae_eq_zero_of_weakly_harmonic (u : Space n → ℝ) (hu : LocallyIntegrable u)
    (hzero : ∀ x, vcoord x ≤ 0 → u x = 0)
    (hharm : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → ∀ ρ < 5 / 4, (∀ x, ρ ≤ ‖x‖ → ψ x = 0) →
      ∫ x, u x * lap ψ x = 0) :
    ∀ᵐ x, ‖x‖ < 1 → u x = 0 := by
  let φ : ℕ → ContDiffBump (0 : Space n) := fun k =>
    ⟨1 / (16 * ((k : ℝ) + 1)), 1 / (8 * ((k : ℝ) + 1)), by positivity, by
      apply one_div_lt_one_div_of_lt (by positivity)
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      linarith⟩
  have hrOut : ∀ k, (φ k).rOut = 1 / (8 * ((k : ℝ) + 1)) := fun k => rfl
  have hrIn : ∀ k, (φ k).rIn = 1 / (16 * ((k : ℝ) + 1)) := fun k => rfl
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    have h1 : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) * (1 / 8)) atTop (𝓝 (0 * (1 / 8))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _
    rw [zero_mul] at h1
    refine h1.congr fun k => ?_
    field_simp
  have h'φ : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn := by
    refine Eventually.of_forall fun k => ?_
    rw [hrOut, hrIn]
    have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_le_iff₀ (by positivity)]
    field_simp
    linarith
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) hφ h'φ hu
  filter_upwards [hae] with x hx hx1
  have hvan : ∀ k, convolution ((φ k).normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x
      = 0 := by
    intro k
    refine mollified_eq_zero u hu hzero hharm (φ k) ?_ x (by rw [mem_ball_zero_iff]; linarith)
    rw [hrOut]
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h0 : Tendsto (fun k => convolution ((φ k).normed volume) u
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop (𝓝 0) := by
    simp only [hvan]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hx h0

/-! ### Step 7: the blow-up contradiction -/

lemma blowup_false (S : HalfBallSolution n)
    (hneu' : ∀ N : ℕ, ∃ Cn : ℝ, ∀ x ∈ flatPiece n S.R, |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ Cn * ‖x‖ ^ N)
    (D : ℝ) (K₀ : ℕ) (s : ℕ → ℝ) (hs_pos : ∀ j, 0 < s j) (hs_R : ∀ j, 4 * s j ≤ S.R)
    (hs1 : ∀ j, s j ≤ 1) (hs_lim : Tendsto s atTop (𝓝 0))
    (hdoub : ∀ j, E S (2 * s j) ≤ D * E S (s j)) (hlow : ∀ j, s j ^ K₀ < E S (s j)) :
    False := by
  have hEpos : ∀ j, 0 < E S (s j) := fun j => lt_of_le_of_lt (pow_pos (hs_pos j) _).le (hlow j)
  have hs2R : ∀ j, 2 * s j ≤ S.R := fun j => by linarith [hs_pos j, hs_R j]
  obtain ⟨C₁, hC₁⟩ := integral_Dw_sq_bdd S hneu' D K₀ s hs_pos hs_R hs1 hdoub hlow
  have hL2 : ∀ j, ∫ x in halfBall n (3 / 2), w S (s j) x ^ 2 ≤ max D C₁ := by
    intro j
    rw [integral_w_sq_eq S (hs_pos j) (by norm_num) (hEpos j)]
    have h1 : E S (s j * (3 / 2)) ≤ E S (2 * s j) :=
      E_mono S (by nlinarith [hs_pos j]) (by linarith [hs_pos j, hs_R j])
    rw [div_le_iff₀ (hEpos j)]
    calc E S (s j * (3 / 2)) ≤ E S (2 * s j) := h1
      _ ≤ D * E S (s j) := hdoub j
      _ ≤ max D C₁ * E S (s j) := mul_le_mul_of_nonneg_right (le_max_left _ _) (hEpos j).le
  have hH1 : ∀ j, ∫ x in halfBall n (3 / 2), ‖Dw S (s j) x‖ ^ 2 ≤ max D C₁ :=
    fun j => (hC₁ j).trans (le_max_right _ _)
  obtain ⟨φ, g0, hφ, hg0, hconv⟩ := exists_L2_subseq_halfBall (fun j => w S (s j))
    (fun j => Dw S (s j)) (max D C₁) (fun j => continuousOn_w S (hs_pos j) (hs2R j))
    (fun j => continuousOn_Dw S (hs_pos j) (hs2R j))
    (fun j => hasGradientAt_w S (hs_pos j) (hs2R j)) hL2 hH1
  have hcont : ∀ j, ContinuousOn (w S (s j)) (closedHalfBall n 2) :=
    fun j => continuousOn_w S (hs_pos j) (hs2R j)
  have hu2 : ∀ j, IntegrableOn (fun x => w S (s (φ j)) x ^ 2) (halfBall n (5 / 4)) :=
    fun j => integrableOn_halfBall_of_continuousOn (by norm_num) ((hcont (φ j)).pow 2)
  have hmem : ∀ j, MemLp (w S (s (φ j))) 2 (volume.restrict (halfBall n (5 / 4))) := by
    intro j
    have hc : ContinuousOn (w S (s (φ j))) (halfBall n (5 / 4)) :=
      (hcont (φ j)).mono ((halfBall_subset_closedHalfBall _).trans
        (closedHalfBall_mono (by norm_num)))
    exact (memLp_two_iff_integrable_sq
      (hc.aestronglyMeasurable (measurableSet_halfBall _))).mpr (hu2 j)
  -- the zero extension of `g0` from `B_{5/4}⁺`
  set U : Space n → ℝ := Set.indicator (halfBall n (5 / 4)) g0 with hU
  have hUloc : LocallyIntegrable U :=
    (hg0.locallyIntegrable (by norm_num)).indicator (measurableSet_halfBall _)
  have hUzero : ∀ x, vcoord x ≤ 0 → U x = 0 := by
    intro x hx
    rw [hU, Set.indicator_of_notMem]
    intro hmem
    exact absurd hmem.2 (not_lt.mpr hx)
  have hharm : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → ∀ ρ < 5 / 4, (∀ x, ρ ≤ ‖x‖ → ψ x = 0) →
      ∫ x, U x * lap ψ x = 0 := by
    intro ψ hψ ρ hρ hψs
    have hlim := (tendsto_integral_w_lap S hneu' D K₀ s hs_pos hs_R hs1 hs_lim hdoub hlow ψ hψ
      ρ (by linarith) hψs).comp hφ.tendsto_atTop
    have h := integral_lap_eq_zero_of_tendsto (fun j => w S (s (φ j))) g0 hg0 hmem hconv ψ hψ ρ hρ
      hψs hlim
    have heq : (fun x => U x * lap ψ x) = Set.indicator (halfBall n (5 / 4))
        (fun x => g0 x * lap ψ x) := by
      funext x
      by_cases hx : x ∈ halfBall n (5 / 4)
      · simp [hU, Set.indicator_of_mem hx]
      · simp [hU, Set.indicator_of_notMem hx]
    rw [heq, integral_indicator (measurableSet_halfBall _)]
    exact h
  have hzero := ae_eq_zero_of_weakly_harmonic U hUloc hUzero hharm
  -- `g0 = 0` a.e. on `B_1⁺`
  have hg0zero : ∀ᵐ x ∂(volume.restrict (halfBall n 1)), g0 x = 0 := by
    rw [ae_restrict_iff' (measurableSet_halfBall 1)]
    filter_upwards [hzero] with x hx hxB
    have h1 := hx hxB.1
    have hxB' : x ∈ halfBall n (5 / 4) := halfBall_mono (by norm_num) hxB
    rwa [hU, Set.indicator_of_mem hxB'] at h1
  -- the normalization `∫_{B_1⁺} w_j² = 1` survives in the limit
  have hge : ∀ j, 1 ≤ ∫ x in halfBall n (5 / 4), (w S (s (φ j)) x - g0 x) ^ 2 := by
    intro j
    have h1 : ∫ x in halfBall n 1, w S (s (φ j)) x ^ 2 = 1 := by
      rw [integral_w_sq_eq S (hs_pos _) one_pos (hEpos _), mul_one, div_self (hEpos _).ne']
    have h2 : ∫ x in halfBall n 1, (w S (s (φ j)) x - g0 x) ^ 2
        = ∫ x in halfBall n 1, w S (s (φ j)) x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hg0zero] with x hx
      simp [hx]
    have hint : IntegrableOn (fun x => (w S (s (φ j)) x - g0 x) ^ 2) (halfBall n (5 / 4)) :=
      ((hmem j).sub (hg0.restrict _)).integrable_sq
    calc (1 : ℝ) = ∫ x in halfBall n 1, (w S (s (φ j)) x - g0 x) ^ 2 := by rw [h2, h1]
      _ ≤ ∫ x in halfBall n (5 / 4), (w S (s (φ j)) x - g0 x) ^ 2 := by
          apply setIntegral_mono_set hint
          · exact Eventually.of_forall (fun x => sq_nonneg _)
          · exact ae_of_all _ (halfBall_mono (by norm_num))
  have := ge_of_tendsto' hconv hge
  norm_num at this

/-! ### Assembly for `n ≥ 1` -/

lemma small_scales (S : HalfBallSolution n)
    (hneu' : ∀ N : ℕ, ∃ Cn : ℝ, ∀ x ∈ flatPiece n S.R, |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ Cn * ‖x‖ ^ N)
    (M : ℕ) (hM : 1 ≤ M) : ∃ r₁ > 0, ∀ r ∈ Ioo 0 r₁, E S r ≤ r ^ M := by
  by_contra hcon
  push Not at hcon
  have hfail : ∀ ε > 0, ∃ r ∈ Ioo 0 ε, r ^ M < E S r := hcon
  obtain ⟨s, hs_pos, hs_R, hs1, hs_lim, hdoub, hlow⟩ := exists_scales S M hM hfail
  exact blowup_false S hneu' (2 ^ (3 * M)) (2 * M) s hs_pos hs_R hs1 hs_lim hdoub hlow

theorem main_of_pos (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) (hn : 0 < n) :
    ∀ M : ℕ, ∃ Cm : ℝ, ∀ r ∈ Set.Ioc 0 (S.R / 2), ∫ x in halfBall n r, S.v x ^ 2 ≤ Cm * r ^ M := by
  intro M
  have hneu' := neumann_flat S g hneu hg hn
  obtain ⟨r₁, hr₁, hsmall⟩ := small_scales S hneu' (M + 1) (by omega)
  set r₂ := min r₁ (min 1 (S.R / 2)) with hr₂
  have hR := S.R_pos
  have hr₂pos : 0 < r₂ := lt_min hr₁ (lt_min one_pos (by linarith))
  have hr₂1 : r₂ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hr₂r₁ : r₂ ≤ r₁ := min_le_left _ _
  refine ⟨max 1 (E S (S.R / 2) / r₂ ^ M), fun r hr => ?_⟩
  change E S r ≤ _
  have hrpos := hr.1
  by_cases hrr : r < r₂
  · have h1 : E S r ≤ r ^ (M + 1) := hsmall r ⟨hrpos, lt_of_lt_of_le hrr hr₂r₁⟩
    have h2 : r ^ (M + 1) ≤ r ^ M := by
      rw [pow_succ]
      have : r ≤ 1 := by linarith
      have hrM : 0 ≤ r ^ M := by positivity
      nlinarith
    have h3 : r ^ M ≤ max 1 (E S (S.R / 2) / r₂ ^ M) * r ^ M := by
      have hrM : 0 ≤ r ^ M := by positivity
      have : 1 ≤ max 1 (E S (S.R / 2) / r₂ ^ M) := le_max_left _ _
      nlinarith
    linarith
  · push Not at hrr
    have h1 : E S r ≤ E S (S.R / 2) := E_mono S hr.2 (by linarith)
    have h2 : E S (S.R / 2) ≤ E S (S.R / 2) / r₂ ^ M * r ^ M := by
      have hr2M : 0 < r₂ ^ M := by positivity
      have hle : r₂ ^ M ≤ r ^ M := by gcongr
      rw [div_mul_eq_mul_div, le_div_iff₀ hr2M]
      exact mul_le_mul_of_nonneg_left hle (E_nonneg S _)
    have h3 : E S (S.R / 2) / r₂ ^ M * r ^ M ≤ max 1 (E S (S.R / 2) / r₂ ^ M) * r ^ M := by
      have hrM : 0 ≤ r ^ M := by positivity
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hrM
    linarith

end R1Aux

/-! ## Package R1: infinite order vanishing (Lemma R1) -/

/-- **Lemma R1.** Flat Dirichlet data and flat conormal data force infinite order vanishing. -/
theorem HalfBallSolution.integral_sq_le_pow (S : HalfBallSolution n) (hn : 0 < n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) :
    ∀ M : ℕ, ∃ Cm : ℝ, ∀ r ∈ Set.Ioc 0 (S.R / 2), ∫ x in halfBall n r, S.v x ^ 2 ≤ Cm * r ^ M := by
  -- `0 < n` is necessary: for `n = 0` the flat piece is `{0}`, the Neumann hypothesis is vacuous,
  -- and `v x = x 0` is a counterexample.
  exact R1Aux.main_of_pos S g hneu hg hn

end MazyaRefinedCauchy
