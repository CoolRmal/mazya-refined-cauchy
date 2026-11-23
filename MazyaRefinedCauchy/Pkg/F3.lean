module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F3

The theorems stated in this file are the frozen contract of package F3 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## Proof of the Kolmogorov–Riesz criterion

We prove `exists_L2_convergent_subseq` by showing that the family `{f j}` is totally bounded in
`L²`; its closure is then compact (`L²` is complete), and a convergent subsequence exists.

For total boundedness we mollify: for a continuous probability density `φ` supported in the ball
of radius `δ` and bounded by `Φ`, the mollifications `g j = φ ⋆ f j` are

* uniformly bounded by `√(Φ M)` and uniformly Lipschitz with constant `√(Φ M)` (weighted Jensen
  inequality plus the hypotheses on `f j`);
* supported in the ball of radius `|R| + δ`;
* `L²`-close to `f j`: `∫ (g j - f j)² ≤ M δ²` (weighted Jensen plus Fubini plus the translation
  hypothesis).

An elementary Arzelà–Ascoli argument (`F3.exists_finite_approx`) gives a finite uniform net of
the `g j` on the ball, hence a finite `L²` net of the `f j`.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F3: compactness in `L²` -/

namespace F3

/-- A function on `Space n` vanishing outside a ball has compact support. -/
theorem hasCompactSupport_of_eq_zero {u : Space n → ℝ} {S : ℝ}
    (h : ∀ y, S ≤ ‖y‖ → u y = 0) : HasCompactSupport u := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space n) S) fun y hy => h y ?_
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  exact hy.le

/-- Weighted Jensen inequality for a probability density `φ`. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ u : α → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∫ t, φ t ∂μ = 1)
    (hφi : Integrable φ μ) (h1 : Integrable (fun t => φ t * u t) μ)
    (h2 : Integrable (fun t => φ t * u t ^ 2) μ) :
    (∫ t, φ t * u t ∂μ) ^ 2 ≤ ∫ t, φ t * u t ^ 2 ∂μ := by
  set c := ∫ t, φ t * u t ∂μ with hc
  have h0 : 0 ≤ ∫ t, φ t * (u t - c) ^ 2 ∂μ :=
    integral_nonneg fun t => mul_nonneg (hφ0 t) (sq_nonneg _)
  have e : (fun t => φ t * (u t - c) ^ 2) =
      fun t => (φ t * u t ^ 2 - (2 * c) * (φ t * u t)) + c ^ 2 * φ t := by
    funext t; ring
  have hA : Integrable (fun t => φ t * u t ^ 2 - (2 * c) * (φ t * u t)) μ :=
    h2.sub (h1.const_mul _)
  have hB : Integrable (fun t => c ^ 2 * φ t) μ := hφi.const_mul _
  have hC : Integrable (fun t => (2 * c) * (φ t * u t)) μ := h1.const_mul _
  have hI : ∫ t, φ t * (u t - c) ^ 2 ∂μ = ∫ t, φ t * u t ^ 2 ∂μ - (2 * c) * c + c ^ 2 * 1 := by
    rw [e, integral_add hA hB, integral_sub h2 hC, integral_const_mul, integral_const_mul, hφ1]
  nlinarith [h0, hI]

/-- From `a² ≤ c b²` to `|a| ≤ √c b`. -/
theorem abs_le_sqrt_mul_of_sq_le {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ^ 2 ≤ c * b ^ 2) :
    |a| ≤ Real.sqrt c * b := by
  have := Real.abs_le_sqrt h
  rwa [Real.sqrt_mul hc, Real.sqrt_sq hb] at this

/-- Existence of a mollifier: a continuous probability density supported in the ball of radius
`δ`, with an upper bound `Φ`. -/
theorem exists_kernel (δ : ℝ) (hδ : 0 < δ) :
    ∃ (φ : Space n → ℝ) (Φ : ℝ), Continuous φ ∧ (∀ t, 0 ≤ φ t) ∧ ∫ t, φ t = 1 ∧
      (∀ t, δ ≤ ‖t‖ → φ t = 0) ∧ (∀ t, φ t ≤ Φ) := by
  let b : ContDiffBump (0 : Space n) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨b.normed volume, 1 / volume.real (Metric.closedBall (0 : Space n) b.rIn),
    b.continuous_normed, b.nonneg_normed, b.integral_normed, fun t ht => ?_,
    b.normed_le_div_measure_closedBall_rIn volume⟩
  have : t ∉ Function.support (b.normed volume) := by
    rw [b.support_normed_eq]
    simp only [Metric.mem_ball, dist_zero_right, not_lt]
    exact ht
  simpa [Function.mem_support] using this

/-- The product of a compactly supported continuous kernel with a continuous function is
integrable. -/
theorem integrable_mul_of_kernel {φ u : Space n → ℝ} {δ : ℝ} (hφc : Continuous φ)
    (hφs : ∀ t, δ ≤ ‖t‖ → φ t = 0) (hu : Continuous u) :
    Integrable (fun t => φ t * u t) := by
  refine (hφc.mul hu).integrable_of_hasCompactSupport ?_
  exact hasCompactSupport_of_eq_zero (S := δ) fun t ht => by simp [Pi.mul_apply, hφs t ht]

/-- The mollification `x ↦ ∫ φ(t) f(x - t) dt`. -/
noncomputable def moll (φ f : Space n → ℝ) (x : Space n) : ℝ := ∫ t, φ t * f (x - t)

/-- Uniform bound for the mollification. -/
theorem moll_sq_le {φ f : Space n → ℝ} {δ Φ R M : ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∫ t, φ t = 1)
    (hφs : ∀ t, δ ≤ ‖t‖ → φ t = 0) (hφΦ : ∀ t, φ t ≤ Φ)
    (hfc : Continuous f) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0) (hfM : ∫ x, f x ^ 2 ≤ M)
    (x : Space n) :
    moll φ f x ^ 2 ≤ Φ * M := by
  have hΦ : 0 ≤ Φ := (hφ0 0).trans (hφΦ 0)
  have hφi : Integrable φ :=
    hφc.integrable_of_hasCompactSupport (hasCompactSupport_of_eq_zero hφs)
  have hu : Continuous fun t => f (x - t) := hfc.comp (continuous_const.sub continuous_id)
  have hf2 : Integrable fun y => f y ^ 2 :=
    (hfc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_of_eq_zero (S := R)
      fun y hy => by simp [Pi.pow_apply, hfs y hy])
  have i1 : Integrable fun t => φ t * f (x - t) := integrable_mul_of_kernel hφc hφs hu
  have i2 : Integrable fun t => φ t * f (x - t) ^ 2 := integrable_mul_of_kernel hφc hφs (hu.pow 2)
  have i3 : Integrable fun t => Φ * f (x - t) ^ 2 := (hf2.comp_sub_left x).const_mul Φ
  calc moll φ f x ^ 2 ≤ ∫ t, φ t * f (x - t) ^ 2 := sq_integral_mul_le hφ0 hφ1 hφi i1 i2
    _ ≤ ∫ t, Φ * f (x - t) ^ 2 := by
        refine integral_mono i2 i3 fun t => ?_
        exact mul_le_mul_of_nonneg_right (hφΦ t) (sq_nonneg _)
    _ = Φ * ∫ y, f y ^ 2 := by
        rw [integral_const_mul]
        have := integral_sub_left_eq_self (fun y => f y ^ 2) (volume : Measure (Space n)) x
        rw [this]
    _ ≤ Φ * M := mul_le_mul_of_nonneg_left hfM hΦ

/-- Uniform Lipschitz bound for the mollification, in squared form. -/
theorem moll_sub_sq_le {φ f : Space n → ℝ} {δ Φ R M : ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∫ t, φ t = 1)
    (hφs : ∀ t, δ ≤ ‖t‖ → φ t = 0) (hφΦ : ∀ t, φ t ≤ Φ)
    (hfc : Continuous f) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0)
    (hfT : ∀ h : Space n, ∫ x, (f (x + h) - f x) ^ 2 ≤ M * ‖h‖ ^ 2) (x h : Space n) :
    (moll φ f (x + h) - moll φ f x) ^ 2 ≤ Φ * M * ‖h‖ ^ 2 := by
  have hΦ : 0 ≤ Φ := (hφ0 0).trans (hφΦ 0)
  have hφi : Integrable φ :=
    hφc.integrable_of_hasCompactSupport (hasCompactSupport_of_eq_zero hφs)
  have hu1 : Continuous fun t => f (x + h - t) := hfc.comp (continuous_const.sub continuous_id)
  have hu2 : Continuous fun t => f (x - t) := hfc.comp (continuous_const.sub continuous_id)
  have j1 : Integrable fun t => φ t * f (x + h - t) := integrable_mul_of_kernel hφc hφs hu1
  have j2 : Integrable fun t => φ t * f (x - t) := integrable_mul_of_kernel hφc hφs hu2
  have hdiff : moll φ f (x + h) - moll φ f x = ∫ t, φ t * (f (x + h - t) - f (x - t)) := by
    unfold moll
    rw [← integral_sub j1 j2]
    congr 1; funext t; ring
  have hw : Continuous fun t => f (x + h - t) - f (x - t) := hu1.sub hu2
  have hg2 : Integrable fun y => (f (y + h) - f y) ^ 2 := by
    refine (((hfc.comp (continuous_id.add continuous_const)).sub hfc).pow 2
      ).integrable_of_hasCompactSupport ?_
    refine hasCompactSupport_of_eq_zero (S := |R| + ‖h‖) fun y hy => ?_
    have h1 : R ≤ ‖y + h‖ := by
      have := norm_sub_le (y + h) h
      rw [add_sub_cancel_right] at this
      linarith [le_abs_self R]
    have h2 : R ≤ ‖y‖ := by linarith [le_abs_self R, norm_nonneg h]
    simp [hfs _ h1, hfs _ h2]
  have k1 : Integrable fun t => φ t * (f (x + h - t) - f (x - t)) :=
    integrable_mul_of_kernel hφc hφs hw
  have k2 : Integrable fun t => φ t * (f (x + h - t) - f (x - t)) ^ 2 :=
    integrable_mul_of_kernel hφc hφs (hw.pow 2)
  have k3 : Integrable fun t => Φ * (f (x - t + h) - f (x - t)) ^ 2 :=
    (hg2.comp_sub_left x).const_mul Φ
  calc (moll φ f (x + h) - moll φ f x) ^ 2
        = (∫ t, φ t * (f (x + h - t) - f (x - t))) ^ 2 := by rw [hdiff]
    _ ≤ ∫ t, φ t * (f (x + h - t) - f (x - t)) ^ 2 := sq_integral_mul_le hφ0 hφ1 hφi k1 k2
    _ ≤ ∫ t, Φ * (f (x - t + h) - f (x - t)) ^ 2 := by
        refine integral_mono k2 k3 fun t => ?_
        simp only
        rw [sub_add_eq_add_sub]
        exact mul_le_mul_of_nonneg_right (hφΦ t) (sq_nonneg _)
    _ = Φ * ∫ y, (f (y + h) - f y) ^ 2 := by
        rw [integral_const_mul]
        have := integral_sub_left_eq_self (fun y => (f (y + h) - f y) ^ 2)
          (volume : Measure (Space n)) x
        rw [this]
    _ ≤ Φ * (M * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left (hfT h) hΦ
    _ = Φ * M * ‖h‖ ^ 2 := by ring

/-- The mollification vanishes outside the ball of radius `R + δ`. -/
theorem moll_eq_zero {φ f : Space n → ℝ} {δ R : ℝ}
    (hφs : ∀ t, δ ≤ ‖t‖ → φ t = 0) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0)
    (x : Space n) (hx : R + δ ≤ ‖x‖) : moll φ f x = 0 := by
  unfold moll
  have : ∀ t, φ t * f (x - t) = 0 := by
    intro t
    by_cases ht : δ ≤ ‖t‖
    · rw [hφs t ht, zero_mul]
    · push Not at ht
      have : R ≤ ‖x - t‖ := by
        have := norm_sub_norm_le x t
        linarith
      rw [hfs _ this, mul_zero]
  simp [this]

/-- Uniform Lipschitz bound for the mollification. -/
theorem moll_abs_sub_le {φ f : Space n → ℝ} {δ Φ R M : ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∫ t, φ t = 1)
    (hφs : ∀ t, δ ≤ ‖t‖ → φ t = 0) (hφΦ : ∀ t, φ t ≤ Φ)
    (hfc : Continuous f) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0) (hfM : ∫ x, f x ^ 2 ≤ M)
    (hfT : ∀ h : Space n, ∫ x, (f (x + h) - f x) ^ 2 ≤ M * ‖h‖ ^ 2) (x y : Space n) :
    |moll φ f x - moll φ f y| ≤ Real.sqrt (Φ * M) * dist x y := by
  have hM : 0 ≤ M := (integral_nonneg fun x => sq_nonneg (f x)).trans hfM
  have hΦ : 0 ≤ Φ := (hφ0 0).trans (hφΦ 0)
  have := moll_sub_sq_le hφc hφ0 hφ1 hφs hφΦ hfc hfs hfT y (x - y)
  have e : y + (x - y) = x := by abel
  rw [e] at this
  rw [dist_eq_norm]
  exact abs_le_sqrt_mul_of_sq_le (norm_nonneg _) (mul_nonneg hΦ hM) this

/-- Uniform bound for the mollification. -/
theorem moll_abs_le {φ f : Space n → ℝ} {δ Φ R M : ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∫ t, φ t = 1)
    (hφs : ∀ t, δ ≤ ‖t‖ → φ t = 0) (hφΦ : ∀ t, φ t ≤ Φ)
    (hfc : Continuous f) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0) (hfM : ∫ x, f x ^ 2 ≤ M)
    (x : Space n) :
    |moll φ f x| ≤ Real.sqrt (Φ * M) :=
  Real.abs_le_sqrt (moll_sq_le hφc hφ0 hφ1 hφs hφΦ hfc hfs hfM x)

/-- The mollification is continuous. -/
theorem continuous_moll {φ f : Space n → ℝ} {δ Φ R M : ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∫ t, φ t = 1)
    (hφs : ∀ t, δ ≤ ‖t‖ → φ t = 0) (hφΦ : ∀ t, φ t ≤ Φ)
    (hfc : Continuous f) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0) (hfM : ∫ x, f x ^ 2 ≤ M)
    (hfT : ∀ h : Space n, ∫ x, (f (x + h) - f x) ^ 2 ≤ M * ‖h‖ ^ 2) :
    Continuous (moll φ f) :=
  (LipschitzWith.of_dist_le' fun x y => by
    rw [Real.dist_eq]
    exact moll_abs_sub_le hφc hφ0 hφ1 hφs hφΦ hfc hfs hfM hfT x y).continuous

/-- The mollification is `L²`-close to the function: `∫ (φ ⋆ f - f)² ≤ M δ²`. -/
theorem integral_moll_sub_sq_le {φ f : Space n → ℝ} {δ R M : ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∫ t, φ t = 1)
    (hφs : ∀ t, δ ≤ ‖t‖ → φ t = 0)
    (hfc : Continuous f) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0) (hfM : ∫ x, f x ^ 2 ≤ M)
    (hfT : ∀ h : Space n, ∫ x, (f (x + h) - f x) ^ 2 ≤ M * ‖h‖ ^ 2) :
    ∫ x, (moll φ f x - f x) ^ 2 ≤ M * δ ^ 2 := by
  have hM : 0 ≤ M := (integral_nonneg fun x => sq_nonneg (f x)).trans hfM
  have hφi : Integrable φ :=
    hφc.integrable_of_hasCompactSupport (hasCompactSupport_of_eq_zero hφs)
  set k : Space n × Space n → ℝ := fun p => φ p.2 * (f (p.1 - p.2) - f p.1) ^ 2 with hk_def
  have hkc : Continuous k :=
    (hφc.comp continuous_snd).mul
      (((hfc.comp (continuous_fst.sub continuous_snd)).sub (hfc.comp continuous_fst)).pow 2)
  have hk : Integrable k ((volume : Measure (Space n)).prod volume) := by
    refine hkc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro ((isCompact_closedBall (0 : Space n) (|R| + δ)).prod
      (isCompact_closedBall (0 : Space n) δ)) ?_
    rintro ⟨x, t⟩ hxt
    simp only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right, not_and_or, not_le] at hxt
    simp only [k]
    by_cases ht : δ ≤ ‖t‖
    · rw [hφs t ht, zero_mul]
    · push Not at ht
      have hx : |R| + δ < ‖x‖ := by
        rcases hxt with h | h
        · exact h
        · linarith
      have h1 : R ≤ ‖x - t‖ := by
        have := norm_sub_norm_le x t
        linarith [le_abs_self R]
      have h2 : R ≤ ‖x‖ := by linarith [le_abs_self R, norm_nonneg t]
      rw [hfs _ h1, hfs _ h2]; ring
  have hpt : ∀ x, (moll φ f x - f x) ^ 2 ≤ ∫ t, k (x, t) := by
    intro x
    have hu0 : Continuous fun t => f (x - t) := hfc.comp (continuous_const.sub continuous_id)
    have hu : Continuous fun t => f (x - t) - f x := hu0.sub continuous_const
    have h1 : Integrable fun t => φ t * f (x - t) := integrable_mul_of_kernel hφc hφs hu0
    have h2 : Integrable fun t => φ t * f x := hφi.mul_const _
    have e : moll φ f x - f x = ∫ t, φ t * (f (x - t) - f x) := by
      simp_rw [mul_sub]
      rw [integral_sub h1 h2, integral_mul_const, hφ1, one_mul]
      rfl
    rw [e]
    exact sq_integral_mul_le hφ0 hφ1 hφi (integrable_mul_of_kernel hφc hφs hu)
      (integrable_mul_of_kernel hφc hφs (hu.pow 2))
  have hH : Integrable fun x => ∫ t, k (x, t) := hk.integral_prod_left
  calc ∫ x, (moll φ f x - f x) ^ 2 ≤ ∫ x, ∫ t, k (x, t) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hH
          (Eventually.of_forall hpt)
    _ = ∫ t, ∫ x, k (x, t) := integral_integral_swap (f := fun x t => k (x, t)) hk
    _ ≤ ∫ t, φ t * (M * δ ^ 2) := by
        refine integral_mono hk.integral_prod_right (hφi.mul_const _) fun t => ?_
        simp only [k]
        rw [integral_const_mul]
        by_cases ht : δ ≤ ‖t‖
        · rw [hφs t ht, zero_mul, zero_mul]
        · push Not at ht
          have h1 : ∫ x, (f (x - t) - f x) ^ 2 ≤ M * ‖t‖ ^ 2 := by
            have := hfT (-t)
            simpa [sub_eq_add_neg, norm_neg] using this
          have h2 : M * ‖t‖ ^ 2 ≤ M * δ ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hM
            gcongr
          exact mul_le_mul_of_nonneg_left (h1.trans h2) (hφ0 t)
    _ = M * δ ^ 2 := by rw [integral_mul_const, hφ1, one_mul]

/-- An elementary Arzelà–Ascoli lemma: a uniformly bounded, uniformly Lipschitz sequence of
functions on a compact set admits, for every `η > 0`, a finite uniform `η`-net among its own
members. -/
theorem exists_finite_approx {E : Type*} [PseudoMetricSpace E] {K : Set E} (hK : IsCompact K)
    (g : ℕ → E → ℝ) {B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hB : ∀ j, ∀ x ∈ K, |g j x| ≤ B)
    (hL : ∀ j, ∀ x ∈ K, ∀ y ∈ K, |g j x - g j y| ≤ L * dist x y) {η : ℝ} (hη : 0 < η) :
    ∃ T : Finset ℕ, ∀ j, ∃ i ∈ T, ∀ x ∈ K, |g j x - g i x| ≤ η := by
  set ρ : ℝ := η / (4 * (L + 1)) with hρ
  have hL1 : L + 1 ≠ 0 := by positivity
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨P, hPK, hPfin, hcov⟩ := Metric.finite_approx_of_totallyBounded hK.totallyBounded ρ hρ0
  have : Fintype P := hPfin.fintype
  let Ψ : ℕ → (P → ℝ) := fun j p => g j (p : E)
  have hΨ : Set.range Ψ ⊆ Metric.closedBall 0 B := by
    rintro _ ⟨j, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hB0).2 fun p => ?_
    rw [Real.norm_eq_abs]
    exact hB j p (hPK p.2)
  have htb : TotallyBounded (Set.range Ψ) :=
    (isCompact_closedBall (0 : P → ℝ) B).totallyBounded.subset hΨ
  obtain ⟨S, hSR, hSfin, hScov⟩ :=
    Metric.finite_approx_of_totallyBounded htb (η / 2) (by positivity)
  choose! ι hι using fun y (hy : y ∈ S) => hSR hy
  refine ⟨hSfin.toFinset.image ι, fun j => ?_⟩
  obtain ⟨y, hyS, hjy⟩ := Set.mem_iUnion₂.1 (hScov ⟨j, rfl⟩)
  refine ⟨ι y, Finset.mem_image.2 ⟨y, hSfin.mem_toFinset.2 hyS, rfl⟩, fun x hx => ?_⟩
  obtain ⟨p, hpP, hxp⟩ := Set.mem_iUnion₂.1 (hcov hx)
  have hdist : dist (Ψ j) (Ψ (ι y)) < η / 2 := by
    rw [hι y hyS]; exact hjy
  have hp : |g j p - g (ι y) p| < η / 2 := by
    have := (dist_le_pi_dist (Ψ j) (Ψ (ι y)) ⟨p, hpP⟩).trans_lt hdist
    simpa [Ψ, Real.dist_eq] using this
  have hxp' : dist x p < ρ := hxp
  have hLρ : L * ρ ≤ η / 4 := by
    have h' : (L + 1) * ρ = η / 4 := by rw [hρ]; field_simp
    nlinarith
  have h1 : |g j x - g j p| ≤ L * ρ :=
    (hL j x hx p (hPK hpP)).trans (mul_le_mul_of_nonneg_left hxp'.le hL0)
  have h2 : |g (ι y) p - g (ι y) x| ≤ L * ρ := by
    rw [dist_comm] at hxp'
    exact (hL (ι y) p (hPK hpP) x hx).trans (mul_le_mul_of_nonneg_left hxp'.le hL0)
  have h3 : |g j x - g (ι y) x| ≤ |g j x - g j p| + |g j p - g (ι y) p| +
      |g (ι y) p - g (ι y) x| := by
    calc |g j x - g (ι y) x| ≤ |g j x - g (ι y) p| + |g (ι y) p - g (ι y) x| :=
          abs_sub_le _ _ _
      _ ≤ |g j x - g j p| + |g j p - g (ι y) p| + |g (ι y) p - g (ι y) x| := by
          gcongr
          exact abs_sub_le _ _ _
  linarith

/-- The `L²` distance of two `L²` functions, in squared form. -/
theorem dist_toLp_sq {u v : Space n → ℝ} (hu : MemLp u 2 (volume : Measure (Space n)))
    (hv : MemLp v 2 (volume : Measure (Space n))) :
    dist (hu.toLp u) (hv.toLp v) ^ 2 = ∫ x, (u x - v x) ^ 2 := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hu hv, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(hu.sub hv).coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, Pi.sub_apply]

/-- The family `{f j}` is totally bounded in `L²`. -/
theorem totallyBounded_range_toLp (f : ℕ → Space n → ℝ) (R M : ℝ)
    (hcont : ∀ j, Continuous (f j)) (hsupp : ∀ j x, R ≤ ‖x‖ → f j x = 0)
    (hbdd : ∀ j, ∫ x, f j x ^ 2 ≤ M)
    (htrans : ∀ j (h : Space n), ∫ x, (f j (x + h) - f j x) ^ 2 ≤ M * ‖h‖ ^ 2)
    (hmem : ∀ j, MemLp (f j) 2 (volume : Measure (Space n))) :
    TotallyBounded (Set.range fun j => (hmem j).toLp (f j)) := by
  have hM : 0 ≤ M := (integral_nonneg fun x => sq_nonneg (f 0 x)).trans (hbdd 0)
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set δ : ℝ := ε / (4 * (Real.sqrt M + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨φ, Φ, hφc, hφ0, hφ1, hφs, hφΦ⟩ := exists_kernel (n := n) δ hδ
  have hΦ : 0 ≤ Φ := (hφ0 0).trans (hφΦ 0)
  set g : ℕ → Space n → ℝ := fun j => moll φ (f j) with hg_def
  have hgc : ∀ j, Continuous (g j) := fun j =>
    continuous_moll hφc hφ0 hφ1 hφs hφΦ (hcont j) (hsupp j) (hbdd j) (htrans j)
  have hgs : ∀ j x, |R| + δ ≤ ‖x‖ → g j x = 0 := fun j x hx =>
    moll_eq_zero hφs (hsupp j) x (by linarith [le_abs_self R])
  have hgmem : ∀ j, MemLp (g j) 2 (volume : Measure (Space n)) := fun j =>
    (hgc j).memLp_of_hasCompactSupport (hasCompactSupport_of_eq_zero (hgs j))
  set K : Set (Space n) := Metric.closedBall 0 (|R| + δ) with hK_def
  have hKc : IsCompact K := isCompact_closedBall _ _
  set V : ℝ := (volume : Measure (Space n)).real K with hV_def
  have hV : 0 ≤ V := measureReal_nonneg
  set η : ℝ := ε / (4 * (Real.sqrt V + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨T, hT⟩ := exists_finite_approx hKc g (Real.sqrt_nonneg (Φ * M))
    (Real.sqrt_nonneg (Φ * M))
    (fun j x _ => moll_abs_le hφc hφ0 hφ1 hφs hφΦ (hcont j) (hsupp j) (hbdd j) x)
    (fun j x _ y _ => moll_abs_sub_le hφc hφ0 hφ1 hφs hφΦ (hcont j) (hsupp j) (hbdd j)
      (htrans j) x y) hη
  refine ⟨(fun j => (hmem j).toLp (f j)) '' (T : Set ℕ), T.finite_toSet.image _, ?_⟩
  rintro _ ⟨j, rfl⟩
  obtain ⟨i, hiT, hji⟩ := hT j
  refine Set.mem_iUnion₂.2 ⟨(hmem i).toLp (f i), ⟨i, hiT, rfl⟩, ?_⟩
  rw [Metric.mem_ball]
  -- the three distances
  have hfg : ∀ k, dist ((hmem k).toLp (f k)) ((hgmem k).toLp (g k)) ≤ Real.sqrt M * δ := by
    intro k
    have h := dist_toLp_sq (hmem k) (hgmem k)
    have h' : ∫ x, (f k x - g k x) ^ 2 ≤ M * δ ^ 2 := by
      have := integral_moll_sub_sq_le hφc hφ0 hφ1 hφs (hcont k) (hsupp k) (hbdd k) (htrans k)
      calc ∫ x, (f k x - g k x) ^ 2 = ∫ x, (g k x - f k x) ^ 2 := by
            congr 1; funext x; ring
        _ ≤ M * δ ^ 2 := this
    exact (le_abs_self _).trans (abs_le_sqrt_mul_of_sq_le hδ.le hM (by rw [h]; exact h'))
  have d2 : dist ((hgmem j).toLp (g j)) ((hgmem i).toLp (g i)) ≤ Real.sqrt V * η := by
    have h := dist_toLp_sq (hgmem j) (hgmem i)
    have hpw : ∀ x, (g j x - g i x) ^ 2 ≤ K.indicator (fun _ => η ^ 2) x := by
      intro x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        have := hji x hx
        calc (g j x - g i x) ^ 2 = |g j x - g i x| ^ 2 := (sq_abs _).symm
          _ ≤ η ^ 2 := by gcongr
      · rw [Set.indicator_of_notMem hx]
        have hx' : |R| + δ ≤ ‖x‖ := by
          simp only [K, Metric.mem_closedBall, dist_zero_right, not_le] at hx
          exact hx.le
        rw [hgs j x hx', hgs i x hx']
        norm_num
    have hint1 : Integrable fun x => (g j x - g i x) ^ 2 :=
      (((hgc j).sub (hgc i)).pow 2).integrable_of_hasCompactSupport
        (hasCompactSupport_of_eq_zero (S := |R| + δ) fun x hx => by
          simp [hgs j x hx, hgs i x hx])
    have hint2 : Integrable (K.indicator fun _ => η ^ 2) :=
      (integrableOn_const hKc.measure_lt_top.ne).integrable_indicator
        measurableSet_closedBall
    have h' : ∫ x, (g j x - g i x) ^ 2 ≤ V * η ^ 2 := by
      calc ∫ x, (g j x - g i x) ^ 2 ≤ ∫ x, K.indicator (fun _ => η ^ 2) x :=
            integral_mono hint1 hint2 hpw
        _ = V * η ^ 2 := by
            rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
    exact (le_abs_self _).trans (abs_le_sqrt_mul_of_sq_le hη.le hV (by rw [h]; exact h'))
  have d1 := hfg j
  have d3 : dist ((hgmem i).toLp (g i)) ((hmem i).toLp (f i)) ≤ Real.sqrt M * δ := by
    rw [dist_comm]; exact hfg i
  have e1 : Real.sqrt M * δ < ε / 4 := by
    have h' : (Real.sqrt M + 1) * δ = ε / 4 := by
      rw [hδdef]; field_simp
    nlinarith
  have e2 : Real.sqrt V * η < ε / 4 := by
    have h' : (Real.sqrt V + 1) * η = ε / 4 := by
      rw [hη_def]; field_simp
    nlinarith
  calc dist ((hmem j).toLp (f j)) ((hmem i).toLp (f i))
      ≤ dist ((hmem j).toLp (f j)) ((hgmem j).toLp (g j)) +
          dist ((hgmem j).toLp (g j)) ((hgmem i).toLp (g i)) +
          dist ((hgmem i).toLp (g i)) ((hmem i).toLp (f i)) := dist_triangle4 _ _ _ _
    _ < ε := by linarith

end F3

/-- Kolmogorov–Riesz type compactness: a sequence of continuous functions supported in a fixed
ball, bounded in `L²` and with uniformly controlled `L²` translations, has an `L²`-convergent
subsequence. -/
theorem exists_L2_convergent_subseq (f : ℕ → Space n → ℝ) (R M : ℝ)
    (hcont : ∀ j, Continuous (f j)) (hsupp : ∀ j x, R ≤ ‖x‖ → f j x = 0)
    (hbdd : ∀ j, ∫ x, f j x ^ 2 ≤ M)
    (htrans : ∀ j (h : Space n), ∫ x, (f j (x + h) - f j x) ^ 2 ≤ M * ‖h‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (g : Space n → ℝ), StrictMono φ ∧ MemLp g 2 ∧
      Tendsto (fun j => ∫ x, (f (φ j) x - g x) ^ 2) atTop (𝓝 0) := by
  have hmem : ∀ j, MemLp (f j) 2 (volume : Measure (Space n)) := fun j =>
    (hcont j).memLp_of_hasCompactSupport (F3.hasCompactSupport_of_eq_zero (hsupp j))
  set F : ℕ → Lp ℝ 2 (volume : Measure (Space n)) := fun j => (hmem j).toLp (f j) with hF_def
  have htb : TotallyBounded (Set.range F) :=
    F3.totallyBounded_range_toLp f R M hcont hsupp hbdd htrans hmem
  have hcpt : IsCompact (closure (Set.range F)) :=
    htb.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq fun j => subset_closure ⟨j, rfl⟩
  refine ⟨φ, a, hφ, Lp.memLp a, ?_⟩
  have key : ∀ j, ∫ x, (f (φ j) x - a x) ^ 2 = dist (F (φ j)) a ^ 2 := by
    intro j
    have h := F3.dist_toLp_sq (hmem (φ j)) (Lp.memLp a)
    rw [Lp.toLp_coeFn] at h
    exact h.symm
  simp_rw [key]
  have h0 : Tendsto (fun j => dist (F (φ j)) a) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 hlim
  simpa using h0.pow 2

end MazyaRefinedCauchy
