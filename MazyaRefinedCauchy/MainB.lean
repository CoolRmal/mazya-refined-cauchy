module

public import MazyaRefinedCauchy.Interfaces

/-!
# Theorem I(b)

Assembly of the proof from the package interfaces in `MazyaRefinedCauchy.Interfaces`.

Route: the collar reduction (package C) with `a = id`, `b = 0`, `c = 0`; the interior decay
(package R) for a positive monotone extension of `h`; the `L²` comparison of the collar; a tangent
ball (package L); the Kelvin transform (package L) and the sup bound from `L²` (package F4) on small
balls; Lemma DC (package L); weak unique continuation (package U) in collar coordinates.
-/

public section

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazyaRefinedCauchy

namespace MainBAux

variable {n : ℕ}

/-! ### The Laplacian as the divergence of the gradient -/

/-- For real spaces, `toDual.symm` as a real continuous linear equivalence. -/
noncomputable def toDualSymmCLE : StrongDual ℝ (Space n) ≃L[ℝ] Space n :=
  ((toDual ℝ (Space n)).symm : StrongDual ℝ (Space n) ≃ₗᵢ⋆[ℝ] Space n).toContinuousLinearEquiv

lemma divergence_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space n))
    (F : Space n → Space n) (x : Space n) :
    divergence F x = ∑ i, ⟪b i, fderiv ℝ F x (b i)⟫_ℝ := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ b]
  rfl

open Laplacian in
/-- `Δ u = div ∇u` for `C²` functions. Adapted from the project scouting probe `Probe2.lean`. -/
lemma laplacian_eq_divergence_gradient {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) : Δ u x = divergence (gradient u) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u (stdOrthonormalBasis ℝ (Space n)),
    divergence_eq_sum (stdOrthonormalBasis ℝ (Space n))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key : ∀ v w : Space n,
      ⟪fderiv ℝ (gradient u) x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ u) x v w := by
    intro v w
    have hg : HasFDerivAt (gradient u)
        ((toDualSymmCLE (n := n) : StrongDual ℝ (Space n) →L[ℝ] Space n) ∘L
          fderiv ℝ (fderiv ℝ u) x) x :=
      (toDualSymmCLE (n := n)).hasFDerivAt.comp x hd.hasFDerivAt
    rw [hg.fderiv]
    simp [toDualSymmCLE]
  rw [iteratedFDeriv_two_apply, real_inner_comm, key]
  simp

lemma divergence_gradient_eq_zero {u : Space n → ℝ} {s : Set (Space n)}
    (hu : HarmonicOnNhd u s) : ∀ x ∈ s, divergence (gradient u) x = 0 := by
  intro x hx
  rw [← laplacian_eq_divergence_gradient (hu x hx).1]
  exact (hu x hx).2.eq_of_nhds

/-! ### Elementary topology -/

lemma continuous_vcoord : Continuous (vcoord (n := n)) := by
  unfold vcoord
  exact PiLp.continuous_apply _ _ _

lemma continuous_graphFn {Γ : (Fin n → ℝ) → ℝ} (hΓc : Continuous Γ) :
    Continuous (graphFn Γ) := by
  unfold graphFn
  exact (hΓc.comp (continuous_pi fun i => PiLp.continuous_apply _ _ _)).sub
    (PiLp.continuous_apply _ _ _)

lemma isOpen_halfBall (R : ℝ) : IsOpen (halfBall n R) := by
  show IsOpen ({x : Space n | ‖x‖ < R} ∩ {x | 0 < vcoord x})
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const continuous_vcoord)

lemma convex_halfBall (R : ℝ) : Convex ℝ (halfBall n R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · have hx' : x ∈ Metric.ball (0 : Space n) R := by simpa using hx.1
    have hy' : y ∈ Metric.ball (0 : Space n) R := by simpa using hy.1
    simpa using (convex_ball (0 : Space n) R) hx' hy' ha hb hab
  · have hx2 : 0 < vcoord x := hx.2
    have hy2 : 0 < vcoord y := hy.2
    simp only [vcoord, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx2 hy2 ⊢
    have hm : 0 < min (x (Fin.last n)) (y (Fin.last n)) := lt_min hx2 hy2
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left (x (Fin.last n)) (y (Fin.last n))) ha,
      mul_le_mul_of_nonneg_left (min_le_right (x (Fin.last n)) (y (Fin.last n))) hb]

lemma integrableOn_halfBall (S : HalfBallSolution n) {r : ℝ} (hr : r < S.R) (c : ℝ) :
    IntegrableOn (fun x => S.v x ^ 2 + c * ‖S.Dv x‖ ^ 2) (halfBall n r) := by
  set K : Set (Space n) := Metric.closedBall 0 r ∩ {x | 0 ≤ vcoord x} with hK_def
  have hK : IsCompact K :=
    (isCompact_closedBall 0 r).inter_right (isClosed_le continuous_const continuous_vcoord)
  have hKsub : K ⊆ closedHalfBall n S.R := fun x hx =>
    ⟨lt_of_le_of_lt (by simpa using hx.1) hr, hx.2⟩
  have hcont : ContinuousOn (fun x => S.v x ^ 2 + c * ‖S.Dv x‖ ^ 2) K :=
    ((S.v_continuousOn.mono hKsub).pow 2).add
      (continuousOn_const.mul ((S.Dv_continuousOn.mono hKsub).norm.pow 2))
  refine (hcont.integrableOn_compact hK).mono_set ?_
  intro x hx
  exact ⟨by simpa using hx.1.le, hx.2.le⟩

lemma integrableOn_u_sq {Γ : (Fin n → ℝ) → ℝ} (hΓc : Continuous Γ) {ρ : ℝ} (u : Space n → ℝ)
    (hu_cont : ContinuousOn u (domainWithBoundary Γ ρ)) {s : ℝ} (hs : s < ρ) :
    IntegrableOn (fun x => u x ^ 2) (domain Γ ρ ∩ Metric.ball 0 s) := by
  set K : Set (Space n) := Metric.closedBall 0 s ∩ {x | graphFn Γ x ≤ 0} with hK_def
  have hK : IsCompact K :=
    (isCompact_closedBall 0 s).inter_right (isClosed_le (continuous_graphFn hΓc) continuous_const)
  have hKsub : K ⊆ domainWithBoundary Γ ρ := fun x hx =>
    ⟨lt_of_le_of_lt (by simpa using hx.1) hs, hx.2⟩
  refine (((hu_cont.mono hKsub).pow 2).integrableOn_compact hK).mono_set ?_
  intro x hx
  refine ⟨?_, hx.1.2.le⟩
  have := hx.2
  rw [Metric.mem_ball, dist_zero_right] at this
  simpa using this.le

/-! ### The inversion `y ↦ y / ‖y‖²` -/

/-- The inversion `y ↦ y / ‖y‖²` (in the form used by `kelvin_harmonicOnNhd`). -/
noncomputable def kinv (y : Space n) : Space n := ‖y‖⁻¹ ^ 2 • y

lemma norm_kinv (y : Space n) : ‖kinv y‖ = ‖y‖⁻¹ := by
  unfold kinv
  rw [norm_smul, norm_pow, norm_inv, norm_norm]
  by_cases hy : ‖y‖ = 0
  · simp [hy]
  · field_simp

lemma kinv_kinv (y : Space n) : kinv (kinv y) = y := by
  rw [kinv, norm_kinv, inv_inv, kinv, smul_smul]
  by_cases hy : ‖y‖ = 0
  · rw [norm_eq_zero.1 hy, smul_zero]
  · rw [← mul_pow, mul_inv_cancel₀ hy, one_pow, one_smul]

lemma inner_kinv (y ν : Space n) : ⟪kinv y, ν⟫_ℝ = ‖y‖⁻¹ ^ 2 * ⟪y, ν⟫_ℝ := by
  rw [kinv, real_inner_smul_left]

/-- The ball `B(Rν, R)` is the inverse image of the half-space `{⟪y, ν⟫ > 1/(2R)}`. -/
lemma mem_tangentBall_iff {ν : Space n} (hν : ‖ν‖ = 1) {R : ℝ} (hR : 0 < R) (x : Space n) :
    x ∈ Metric.ball (R • ν) R ↔ x ≠ 0 ∧ 1 / (2 * R) < ⟪kinv x, ν⟫_ℝ := by
  have hsq : ‖x - R • ν‖ ^ 2 = ‖x‖ ^ 2 - 2 * R * ⟪x, ν⟫_ℝ + R ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hν, Real.norm_eq_abs,
      abs_of_pos hR]
    ring
  rw [Metric.mem_ball, dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hR.le, hsq, inner_kinv]
  constructor
  · intro h
    have hx : x ≠ 0 := by
      rintro rfl
      simp at h
    refine ⟨hx, ?_⟩
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [inv_pow, ← div_eq_inv_mul, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rintro ⟨hx, h⟩
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [inv_pow, ← div_eq_inv_mul, div_lt_div_iff₀ (by positivity) (by positivity)] at h
    nlinarith

/-- Small balls around the inverted points of `{⟪y, ν⟫ > 1/(2R) + 1}` stay in `B(Rν, R)`. -/
lemma closedBall_subset_tangentBall {ν : Space n} (hν : ‖ν‖ = 1) {R : ℝ} (hR : 0 < R)
    (hR2 : R ≤ 1 / 2) (y : Space n) (hy : 1 / (2 * R) + 1 < ⟪y, ν⟫_ℝ) :
    Metric.closedBall (kinv y) (‖y‖⁻¹ ^ 2 / 8) ⊆ Metric.ball (R • ν) R := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have hp : ⟪y, ν⟫_ℝ ≤ ‖y‖ := by
    have := real_inner_le_norm y ν
    rwa [hν, mul_one] at this
  have hsq : ‖x - R • ν‖ ^ 2 = ‖x‖ ^ 2 - 2 * R * ⟪x, ν⟫_ℝ + R ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hν, Real.norm_eq_abs,
      abs_of_pos hR]
    ring
  have hlam : 1 ≤ 1 / (2 * R) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h2Rp : 1 + 2 * R < 2 * R * ⟪y, ν⟫_ℝ := by
    have h1 := mul_lt_mul_of_pos_left hy (by positivity : (0 : ℝ) < 2 * R)
    have h2 : 2 * R * (1 / (2 * R)) = 1 := by field_simp
    rw [mul_add, h2] at h1
    linarith
  have hspos : 0 < ‖y‖ := by linarith
  have hts : ‖y‖⁻¹ * ‖y‖ = 1 := inv_mul_cancel₀ hspos.ne'
  have htpos : 0 < ‖y‖⁻¹ := inv_pos.2 hspos
  have ht2R : ‖y‖⁻¹ < 2 * R := by
    by_contra hcon
    have : 2 * R * ‖y‖ ≤ ‖y‖⁻¹ * ‖y‖ := mul_le_mul_of_nonneg_right (not_lt.1 hcon) hspos.le
    nlinarith
  have ht1 : ‖y‖⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hspos]
    linarith
  have hxn : ‖x‖ ≤ ‖y‖⁻¹ + ‖y‖⁻¹ ^ 2 / 8 := by
    have := norm_le_insert' x (kinv y)
    rw [norm_kinv] at this
    linarith
  have hxi : ‖y‖⁻¹ ^ 2 * ⟪y, ν⟫_ℝ - ‖y‖⁻¹ ^ 2 / 8 ≤ ⟪x, ν⟫_ℝ := by
    have e : ⟪x, ν⟫_ℝ = ⟪kinv y, ν⟫_ℝ + ⟪x - kinv y, ν⟫_ℝ := by
      rw [← inner_add_left]
      congr 1
      abel
    have h1 : |⟪x - kinv y, ν⟫_ℝ| ≤ ‖x - kinv y‖ := by
      have := abs_real_inner_le_norm (x - kinv y) ν
      rwa [hν, mul_one] at this
    rw [inner_kinv] at e
    have := neg_abs_le ⟪x - kinv y, ν⟫_ℝ
    linarith
  rw [Metric.mem_ball, dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hR.le, hsq]
  set t := ‖y‖⁻¹ with ht_def
  set p := ⟪y, ν⟫_ℝ with hp_def
  have key : (1 + t / 8) ^ 2 < 2 * R * p - R / 4 := by nlinarith
  have hx2 : ‖x‖ ^ 2 ≤ (t + t ^ 2 / 8) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxn 2
  have e2 : (t + t ^ 2 / 8) ^ 2 = t ^ 2 * (1 + t / 8) ^ 2 := by ring
  have hlt : t ^ 2 * (1 + t / 8) ^ 2 < t ^ 2 * (2 * R * p - R / 4) :=
    mul_lt_mul_of_pos_left key (by positivity)
  have e3 : t ^ 2 * (2 * R * p - R / 4) = 2 * R * (t ^ 2 * p - t ^ 2 / 8) := by ring
  have h4 : 2 * R * (t ^ 2 * p - t ^ 2 / 8) ≤ 2 * R * ⟪x, ν⟫_ℝ :=
    mul_le_mul_of_nonneg_left hxi (by positivity)
  nlinarith

lemma norm_innerNormalZero_eq_one {Γ : (Fin n → ℝ) → ℝ} (hΓ0 : Γ 0 = 0) {ρ R : ℝ} (hR : 0 < R)
    (hball : Metric.ball (R • innerNormalZero Γ) R ⊆ domain Γ ρ) :
    ‖innerNormalZero Γ‖ = 1 := by
  have hnorm : ‖innerNormalZero Γ‖ = 0 ∨ ‖innerNormalZero Γ‖ = 1 := by
    unfold innerNormalZero outerNormal
    rw [norm_neg, norm_smul, norm_inv, norm_norm]
    by_cases hg : ‖gradient (graphFn Γ) 0‖ = 0
    · left
      rw [hg, inv_zero, zero_mul]
    · right
      exact inv_mul_cancel₀ hg
  rcases hnorm with h0 | h1
  · exfalso
    have hν0 : innerNormalZero Γ = 0 := norm_eq_zero.1 h0
    have hmem : (0 : Space n) ∈ Metric.ball (R • innerNormalZero Γ) R := by
      rw [hν0, smul_zero]
      exact Metric.mem_ball_self hR
    have hdom := hball hmem
    have hz : (fun i : Fin n => (0 : Space n) (Fin.castSucc i)) = 0 := by
      funext i
      simp
    have hg0 : graphFn Γ 0 = 0 := by
      simp only [graphFn, hz, hΓ0]
      simp
    have h2 := hdom.2
    rw [hg0] at h2
    exact lt_irrefl _ h2
  · exact h1

/-! ### The extension of the profile -/

/-- The extension `r ↦ h (min r (ρ/2))` of `h` to `(0, ∞)`. -/
noncomputable def hExt (h : ℝ → ℝ) (ρ : ℝ) (r : ℝ) : ℝ := h (min r (ρ / 2))

lemma hExt_pos {ρ : ℝ} (hρ : 0 < ρ) (h : ℝ → ℝ) (hh_pos : ∀ r ∈ Set.Ioo 0 ρ, 0 < h r) :
    ∀ r, 0 < r → 0 < hExt h ρ r := by
  intro r hr
  exact hh_pos _ ⟨lt_min hr (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩

lemma hExt_mono {ρ : ℝ} (hρ : 0 < ρ) (h : ℝ → ℝ) (hh_mono : MonotoneOn h (Set.Ioo 0 ρ)) :
    MonotoneOn (hExt h ρ) (Set.Ioi 0) := by
  intro r hr s hs hrs
  have hr' : (0 : ℝ) < r := hr
  have hs' : (0 : ℝ) < s := hs
  exact hh_mono ⟨lt_min hr' (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    ⟨lt_min hs' (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    (min_le_min_right _ hrs)

lemma hExt_eq (h : ℝ → ℝ) (ρ : ℝ) {r : ℝ} (hr : r ≤ ρ / 2) : hExt h ρ r = h r := by
  rw [hExt, min_eq_left hr]

lemma hExt_regular {ρ : ℝ} (hρ : 0 < ρ) (h : ℝ → ℝ)
    (hΛ_super : Tendsto (fun σ => Real.log (1 / h (Real.exp (-σ))) / σ) atTop atTop)
    (hΛ_convex : ∃ σ₀ : ℝ,
      ConvexOn ℝ (Set.Ici σ₀) (fun σ => Real.log (1 / h (Real.exp (-σ)))))
    (hΛ_growth : ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ t ≥ 0,
      Real.log (1 / h (Real.exp (-(σ + t))))
        ≤ Real.exp (C * t) * Real.log (1 / h (Real.exp (-σ)))) :
    RegularProfile (hExt h ρ) := by
  have key : ∀ σ, -Real.log (ρ / 2) ≤ σ → hExt h ρ (Real.exp (-σ)) = h (Real.exp (-σ)) := by
    intro σ hσ
    apply hExt_eq
    calc Real.exp (-σ) ≤ Real.exp (Real.log (ρ / 2)) := Real.exp_le_exp.2 (by linarith)
      _ = ρ / 2 := Real.exp_log (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨σ₀, hσ₀⟩ := hΛ_convex
    refine ⟨max σ₀ (-Real.log (ρ / 2)), ?_⟩
    have := hσ₀.subset (Set.Ici_subset_Ici.2 (le_max_left σ₀ (-Real.log (ρ / 2))))
      (convex_Ici _)
    refine this.congr ?_
    intro σ hσ
    have hσ' : max σ₀ (-Real.log (ρ / 2)) ≤ σ := hσ
    simp only [key σ (le_trans (le_max_right _ _) hσ')]
  · refine hΛ_super.congr' ?_
    filter_upwards [eventually_ge_atTop (-Real.log (ρ / 2))] with σ hσ
    rw [key σ hσ]
  · obtain ⟨C, σ₀, hC⟩ := hΛ_growth
    refine ⟨C, max σ₀ (-Real.log (ρ / 2)), fun σ hσ t ht => ?_⟩
    have h1 : -Real.log (ρ / 2) ≤ σ := le_trans (le_max_right _ _) hσ
    rw [key σ h1, key (σ + t) (by linarith)]
    exact hC σ (le_trans (le_max_left _ _) hσ) t ht

/-! ### The decay profile `ψ` -/

/-- `ψ(s) = log (1 / H (C / s)) / 8`. -/
noncomputable def psiOf (H : ℝ → ℝ) (C : ℝ) (s : ℝ) : ℝ := (1 / 8) * Real.log (1 / H (C / s))

lemma psiOf_mono {H : ℝ → ℝ} (hH_pos : ∀ r, 0 < r → 0 < H r)
    (hH_mono : MonotoneOn H (Set.Ioi 0)) {C : ℝ} (hC : 0 < C) :
    MonotoneOn (psiOf H C) (Set.Ioi 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  unfold psiOf
  have h1 : C / t ≤ C / s := div_le_div_of_nonneg_left hC.le hs' hst
  have h2 : H (C / t) ≤ H (C / s) := hH_mono (div_pos hC ht') (div_pos hC hs') h1
  have h3 : 1 / H (C / s) ≤ 1 / H (C / t) :=
    one_div_le_one_div_of_le (hH_pos _ (div_pos hC ht')) h2
  have h4 := Real.log_le_log (one_div_pos.2 (hH_pos _ (div_pos hC hs'))) h3
  linarith

lemma psiOf_exp (H : ℝ → ℝ) {C : ℝ} (hC : 0 < C) (σ : ℝ) :
    psiOf H C (Real.exp σ) = (1 / 8) * Real.log (1 / H (Real.exp (-(σ - Real.log C)))) := by
  unfold psiOf
  rw [neg_sub, Real.exp_sub, Real.exp_log hC]

lemma psiOf_convex {H : ℝ → ℝ} (hH : RegularProfile H) {C : ℝ} (hC : 0 < C) :
    ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => psiOf H C (Real.exp σ)) := by
  obtain ⟨σ₀, hσ₀⟩ := hH.convex
  refine ⟨σ₀ + Real.log C, ?_⟩
  have h1 := hσ₀.translate_right (-Real.log C)
  have hset : (fun z => -Real.log C + z) ⁻¹' Set.Ici σ₀ = Set.Ici (σ₀ + Real.log C) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  rw [hset] at h1
  have h2 := h1.smul (by norm_num : (0 : ℝ) ≤ 1 / 8)
  refine h2.congr ?_
  intro σ _
  simp only [Function.comp, smul_eq_mul, psiOf_exp H hC]
  rw [show -(-Real.log C + σ) = -(σ - Real.log C) by ring]

lemma psiOf_log {H : ℝ → ℝ} (hH : RegularProfile H) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun s => psiOf H C s / Real.log s) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  set M' : ℝ := max M 0 with hM'_def
  have hM' : M ≤ M' := le_max_left _ _
  have hM'0 : 0 ≤ M' := le_max_right _ _
  obtain ⟨σ₁, hσ₁⟩ := eventually_atTop.1 (tendsto_atTop.1 hH.super (16 * M'))
  set A : ℝ := max (max (max σ₁ 1 + Real.log C) (2 * Real.log C)) 1 with hA_def
  filter_upwards [eventually_ge_atTop (Real.exp A)] with s hs
  have hA1 : 1 ≤ A := le_max_right _ _
  have hA2 : max σ₁ 1 + Real.log C ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA3 : 2 * Real.log C ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hσ1' : σ₁ ≤ max σ₁ 1 := le_max_left _ _
  have hσ1'' : 1 ≤ max σ₁ 1 := le_max_right _ _
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos A) hs
  have hlogs : A ≤ Real.log s := by
    rw [← Real.exp_le_exp, Real.exp_log hspos]
    exact hs
  have hlogpos : 0 < Real.log s := by linarith
  set σ : ℝ := Real.log s - Real.log C with hσ_def
  have hσ1 : σ₁ ≤ σ := by linarith
  have hσpos : 1 ≤ σ := by linarith
  have hσhalf : Real.log s / 2 ≤ σ := by linarith
  have hΛ : 16 * M' ≤ Real.log (1 / H (Real.exp (-σ))) / σ := hσ₁ σ hσ1
  rw [le_div_iff₀ (by linarith)] at hΛ
  have hpsi : psiOf H C s = (1 / 8) * Real.log (1 / H (Real.exp (-σ))) := by
    have := psiOf_exp H hC (Real.log s)
    rw [Real.exp_log hspos] at this
    exact this
  rw [hpsi, le_div_iff₀ hlogpos]
  nlinarith [mul_le_mul_of_nonneg_left hσhalf hM'0, mul_le_mul_of_nonneg_right hM' hlogpos.le]

lemma sqrt_exp_eq (a : ℝ) : Real.sqrt (Real.exp a) = Real.exp (a / 2) := by
  have e : Real.exp a = Real.exp (a / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e]
  exact Real.sqrt_sq (Real.exp_pos _).le

lemma sqrt_sqrt_eq {H : ℝ → ℝ} (hH_pos : ∀ r, 0 < r → 0 < H r) {C : ℝ} (hC : 0 < C) {s : ℝ}
    (hs : 0 < s) : Real.sqrt (Real.sqrt (H (C / s))) = Real.exp (-psiOf H C s) ^ 2 := by
  have hx : 0 < H (C / s) := hH_pos _ (div_pos hC hs)
  have e : H (C / s) = Real.exp (Real.log (H (C / s))) := (Real.exp_log hx).symm
  have hl : Real.log (1 / H (C / s)) = -Real.log (H (C / s)) := by
    rw [one_div, Real.log_inv]
  have hpsi : psiOf H C s = -(1 / 8) * Real.log (H (C / s)) := by
    unfold psiOf
    rw [hl]
    ring
  rw [hpsi, ← Real.exp_nat_mul]
  conv_lhs => rw [e, sqrt_exp_eq, sqrt_exp_eq]
  congr 1
  push_cast
  ring

lemma psi_absorb {H : ℝ → ℝ} (hH_pos : ∀ r, 0 < r → 0 < H r)
    (hH_mono : MonotoneOn H (Set.Ioi 0)) (hH : RegularProfile H) {C : ℝ} (hC : 0 < C)
    (d : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ Cu : ℝ, ∀ s : ℝ, 1 ≤ s →
      K * s ^ d * Real.sqrt (Real.sqrt (H (C / s))) ≤ Cu * Real.exp (-psiOf H C s) := by
  obtain ⟨S₁, hS₁⟩ := eventually_atTop.1
    (((psiOf_log hH hC).eventually (eventually_ge_atTop (d : ℝ))).and (eventually_gt_atTop 1))
  set S : ℝ := max S₁ 1 with hS_def
  set Cu : ℝ := K + K * S ^ d * Real.exp (-psiOf H C 1) with hCu_def
  refine ⟨Cu, fun s hs => ?_⟩
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  rw [sqrt_sqrt_eq hH_pos hC hspos]
  have hE : 0 < Real.exp (-psiOf H C s) := Real.exp_pos _
  have hKS : 0 ≤ K * S ^ d * Real.exp (-psiOf H C 1) := by
    have : 0 ≤ S := le_trans zero_le_one (le_max_right _ _)
    positivity
  by_cases hsS : S₁ ≤ s
  · obtain ⟨hd, hs1⟩ := hS₁ s hsS
    have hlog : 0 < Real.log s := Real.log_pos hs1
    rw [le_div_iff₀ hlog] at hd
    have h1 : s ^ d * Real.exp (-psiOf H C s) ≤ 1 := by
      have e : s ^ d = Real.exp (d * Real.log s) := by
        rw [Real.exp_nat_mul, Real.exp_log hspos]
      rw [e, ← Real.exp_add]
      exact Real.exp_le_one_iff.2 (by linarith)
    calc K * s ^ d * Real.exp (-psiOf H C s) ^ 2
        = K * (s ^ d * Real.exp (-psiOf H C s)) * Real.exp (-psiOf H C s) := by ring
      _ ≤ K * 1 * Real.exp (-psiOf H C s) := by gcongr
      _ ≤ Cu * Real.exp (-psiOf H C s) := by
        gcongr
        rw [hCu_def]
        linarith
  · have hsS' : s ≤ S := le_trans (le_of_lt (not_le.1 hsS)) (le_max_left _ _)
    have h1 : s ^ d ≤ S ^ d := pow_le_pow_left₀ hspos.le hsS' d
    have h2 : Real.exp (-psiOf H C s) ≤ Real.exp (-psiOf H C 1) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      exact psiOf_mono hH_pos hH_mono hC (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 hspos) hs
    calc K * s ^ d * Real.exp (-psiOf H C s) ^ 2
        = K * s ^ d * Real.exp (-psiOf H C s) * Real.exp (-psiOf H C s) := by ring
      _ ≤ K * S ^ d * Real.exp (-psiOf H C 1) * Real.exp (-psiOf H C s) := by gcongr
      _ ≤ Cu * Real.exp (-psiOf H C s) := by
        gcongr
        rw [hCu_def]
        linarith

lemma psiOf_not_integrable {ρ : ℝ} (hρ : 0 < ρ) (h H : ℝ → ℝ)
    (hh_pos : ∀ r ∈ Set.Ioo 0 ρ, 0 < h r) (hh_mono : MonotoneOn h (Set.Ioo 0 ρ))
    (hHh : ∀ r, 0 < r → r ≤ ρ / 2 → H r = h r) {C : ℝ} (hC : 0 < C)
    (hlog : Tendsto (fun ε => ∫ r in ε..(ρ / 2), Real.log (h r)) (𝓝[>] 0) atBot) :
    ¬ IntegrableOn (fun s => psiOf H C s / s ^ 2) (Set.Ici 1) := by
  intro hint
  set f : ℝ → ℝ := fun s => psiOf H C s / s ^ 2 with hf_def
  set M : ℝ := ∫ s in Set.Ici (1 : ℝ), |f s| with hM_def
  set S₀ : ℝ := max 1 (2 * C / ρ) with hS₀_def
  have hS₀1 : 1 ≤ S₀ := le_max_left _ _
  have hS₀pos : 0 < S₀ := lt_of_lt_of_le one_pos hS₀1
  set c₀ : ℝ := C / S₀ with hc₀_def
  have hc₀pos : 0 < c₀ := div_pos hC hS₀pos
  have hc₀ρ : c₀ ≤ ρ / 2 := by
    rw [hc₀_def, div_le_iff₀ hS₀pos]
    have : 2 * C / ρ ≤ S₀ := le_max_right _ _
    rw [div_le_iff₀ hρ] at this
    linarith
  -- `log ∘ h` is monotone on `(0, ρ)`, hence interval integrable on compact subintervals
  have hmono_log : MonotoneOn (fun r => Real.log (h r)) (Set.Ioo 0 ρ) := by
    intro a ha b hb hab
    exact Real.log_le_log (hh_pos a ha) (hh_mono ha hb hab)
  have hII : ∀ a b : ℝ, 0 < a → a ≤ b → b < ρ →
      IntervalIntegrable (fun r => Real.log (h r)) volume a b := by
    intro a b ha hab hb
    apply MonotoneOn.intervalIntegrable
    apply hmono_log.mono
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  set K₀ : ℝ := ∫ r in c₀..(ρ / 2), Real.log (h r) with hK₀_def
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ r in ε..(ρ / 2), Real.log (h r)) ≤ -(8 * C * M) + K₀ - 1 :=
    tendsto_atBot.1 hlog _
  obtain ⟨ε, hεle, hε⟩ := (hev.and (Ioo_mem_nhdsGT hc₀pos)).exists
  obtain ⟨hε0, hεc₀⟩ := hε
  have hsplit : ∫ r in ε..(ρ / 2), Real.log (h r) = (∫ r in ε..c₀, Real.log (h r)) + K₀ :=
    (intervalIntegral.integral_add_adjacent_intervals (hII ε c₀ hε0 hεc₀.le (by linarith))
      (hII c₀ (ρ / 2) hc₀pos hc₀ρ (by linarith))).symm
  -- the change of variables `r = C / s`
  have himg : (fun s => C / s) '' Set.Ioo S₀ (C / ε) = Set.Ioo ε c₀ := by
    ext r
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      have hspos : 0 < s := lt_trans hS₀pos hs1
      constructor
      · rw [lt_div_iff₀ hspos]
        rw [lt_div_iff₀ hε0] at hs2
        linarith
      · exact div_lt_div_of_pos_left hC hS₀pos hs1
    · rintro ⟨hr1, hr2⟩
      have hrpos : 0 < r := lt_trans hε0 hr1
      refine ⟨C / r, ⟨?_, ?_⟩, ?_⟩
      · rw [lt_div_iff₀ hrpos]
        rw [hc₀_def, lt_div_iff₀ hS₀pos] at hr2
        linarith
      · exact div_lt_div_of_pos_left hC hε0 hr1
      · exact div_div_cancel₀ hC.ne'
  have hderiv : ∀ s ∈ Set.Ioo S₀ (C / ε),
      HasDerivWithinAt (fun s => C / s) (C * -(s ^ 2)⁻¹) (Set.Ioo S₀ (C / ε)) s := by
    intro s hs
    have hspos : 0 < s := lt_trans hS₀pos hs.1
    have := (hasDerivAt_inv hspos.ne').const_mul C
    simp only [div_eq_mul_inv]
    exact this.hasDerivWithinAt
  have hinj : Set.InjOn (fun s => C / s) (Set.Ioo S₀ (C / ε)) := by
    intro a ha b hb hab
    have hapos : 0 < a := lt_trans hS₀pos ha.1
    have hbpos : 0 < b := lt_trans hS₀pos hb.1
    simp only at hab
    rw [div_eq_div_iff hapos.ne' hbpos.ne'] at hab
    exact (mul_left_cancel₀ hC.ne' hab).symm
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun r => Real.log (h r))
  rw [himg] at hcv
  have hpt : Set.EqOn (fun s => |C * -(s ^ 2)⁻¹| • Real.log (h (C / s)))
      (fun s => -(8 * C) * f s) (Set.Ioo S₀ (C / ε)) := by
    intro s hs
    have hspos : 0 < s := lt_trans hS₀pos hs.1
    have hCs : 0 < C / s := div_pos hC hspos
    have hCs2 : C / s ≤ ρ / 2 :=
      le_trans (div_le_div_of_nonneg_left hC.le hS₀pos hs.1.le) hc₀ρ
    simp only [hf_def, psiOf, smul_eq_mul]
    rw [hHh _ hCs hCs2, one_div (h (C / s)), Real.log_inv, abs_mul, abs_neg, abs_of_pos hC,
      abs_of_pos (by positivity : (0 : ℝ) < (s ^ 2)⁻¹)]
    ring
  have hcov : ∫ r in ε..c₀, Real.log (h r) = -(8 * C) * ∫ s in Set.Ioo S₀ (C / ε), f s := by
    rw [intervalIntegral.integral_of_le hεc₀.le, integral_Ioc_eq_integral_Ioo, hcv,
      setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul]
  -- the bound by `M`
  have hbound : ∫ s in Set.Ioo S₀ (C / ε), f s ≤ M := by
    have hsub : Set.Ioo S₀ (C / ε) ⊆ Set.Ici 1 := fun s hs => le_trans hS₀1 hs.1.le
    calc ∫ s in Set.Ioo S₀ (C / ε), f s ≤ |∫ s in Set.Ioo S₀ (C / ε), f s| := le_abs_self _
      _ ≤ ∫ s in Set.Ioo S₀ (C / ε), |f s| := abs_integral_le_integral_abs
      _ ≤ M := setIntegral_mono_set hint.abs (ae_of_all _ (fun s => abs_nonneg _))
          hsub.eventuallySubset
  have h8 : -(8 * C * M) ≤ -(8 * C) * ∫ s in Set.Ioo S₀ (C / ε), f s := by
    have := mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℝ) ≤ 8 * C)
    linarith
  linarith

/-! ### `L²` bounds -/

lemma L2_bound_u (S : HalfBallSolution n) {Γ : (Fin n → ℝ) → ℝ} {ρ κ : ℝ} (hκ : 1 ≤ κ)
    (u : Space n → ℝ)
    (hFL2 : ∀ r ∈ Set.Ioc 0 S.R,
      ∫ x in domain Γ ρ ∩ Metric.ball 0 (r / κ), u x ^ 2 ≤ κ * ∫ X in halfBall n r, S.v X ^ 2)
    (g : ℝ → ℝ) {Cd r₀ : ℝ} (_hr₀ : 0 < r₀)
    (hdecay : ∀ r ∈ Set.Ioc 0 r₀,
      ∫ x in halfBall n r, (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2) ≤ Cd * Real.sqrt (g (Cd * r))) :
    ∀ s ∈ Set.Ioc 0 (min r₀ (S.R / 2) / κ),
      ∫ x in domain Γ ρ ∩ Metric.ball 0 s, u x ^ 2 ≤ κ * (Cd * Real.sqrt (g (Cd * (κ * s)))) := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ
  have hSR := S.R_pos
  have hr0 : 0 < κ * s := mul_pos hκpos hs0
  have hrm : κ * s ≤ min r₀ (S.R / 2) := by
    rw [le_div_iff₀ hκpos, mul_comm] at hs1
    exact hs1
  have hrr₀ : κ * s ≤ r₀ := le_trans hrm (min_le_left _ _)
  have hrR : κ * s < S.R := lt_of_le_of_lt (le_trans hrm (min_le_right _ _)) (by linarith)
  have h1 := hFL2 (κ * s) ⟨hr0, hrR.le⟩
  have hrκ : κ * s / κ = s := by field_simp
  rw [hrκ] at h1
  have h2 : ∫ X in halfBall n (κ * s), S.v X ^ 2
      ≤ ∫ X in halfBall n (κ * s), (S.v X ^ 2 + (κ * s) ^ 2 * ‖S.Dv X‖ ^ 2) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun X => by simp only [Pi.zero_apply]; positivity)
    · exact integrableOn_halfBall S hrR ((κ * s) ^ 2)
    · exact Filter.Eventually.of_forall (fun X => le_add_of_nonneg_right (by positivity))
  have h3 := hdecay (κ * s) ⟨hr0, hrr₀⟩
  calc ∫ x in domain Γ ρ ∩ Metric.ball 0 s, u x ^ 2
      ≤ κ * ∫ X in halfBall n (κ * s), S.v X ^ 2 := h1
    _ ≤ κ * (Cd * Real.sqrt (g (Cd * (κ * s)))) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) hκpos.le

/-- `harmonic_abs_le_L2` with a nonnegative constant. -/
lemma harmonic_abs_le_L2' (n : ℕ) : ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (u : Space n → ℝ) (x : Space n) (r : ℝ),
    0 < r → HarmonicOnNhd u (Metric.closedBall x r) →
      |u x| ≤ Cn * r ^ (-((n + 1 : ℝ) / 2)) * Real.sqrt (∫ y in Metric.ball x r, u y ^ 2) := by
  obtain ⟨Cn, hCn⟩ := harmonic_abs_le_L2 n
  refine ⟨max Cn 0, le_max_right _ _, fun u x r hr hu => (hCn u x r hr hu).trans ?_⟩
  have h1 : 0 ≤ r ^ (-((n + 1 : ℝ) / 2)) := Real.rpow_nonneg hr.le _
  have h2 : 0 ≤ Real.sqrt (∫ y in Metric.ball x r, u y ^ 2) := Real.sqrt_nonneg _
  have h3 : Cn ≤ max Cn 0 := le_max_left _ _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 h1) h2

/-- `(s⁻² / 8)^{-(n+1)/2} = (√8 s)^{n+1}`. -/
lemma rpow_radius (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (s⁻¹ ^ 2 / 8) ^ (-((n + 1 : ℝ) / 2)) = (Real.sqrt 8 * s) ^ (n + 1) := by
  have h8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have e : s⁻¹ ^ 2 / 8 = ((Real.sqrt 8 * s) ^ 2)⁻¹ := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    field_simp
  rw [e, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
    ← Real.rpow_natCast (Real.sqrt 8 * s) 2, ← Real.rpow_mul (by positivity)]
  rw [show ((2 : ℕ) : ℝ) * ((n + 1 : ℝ) / 2) = ((n + 1 : ℕ) : ℝ) by push_cast; ring]
  exact Real.rpow_natCast _ _

/-- Pointwise bound for the Kelvin transform from the `L²` bound near `0`. -/
lemma kelvin_bound {Γ : (Fin n → ℝ) → ℝ} (hΓc : Continuous Γ) {ρ : ℝ} (u : Space n → ℝ)
    (hu : HarmonicOnNhd u (domain Γ ρ)) (hu_cont : ContinuousOn u (domainWithBoundary Γ ρ))
    {ν : Space n} (hν : ‖ν‖ = 1) {R : ℝ} (hR : 0 < R) (hR2 : R ≤ 1 / 2)
    (hball : Metric.ball (R • ν) R ⊆ domain Γ ρ)
    (H : ℝ → ℝ) {C₁ C₂ s₁ : ℝ} (hC₁ : 0 ≤ C₁) (hs₁ρ : s₁ < ρ) (hRs₁ : 4 * R ≤ s₁)
    (hL2 : ∀ s ∈ Set.Ioc 0 s₁,
      ∫ x in domain Γ ρ ∩ Metric.ball 0 s, u x ^ 2 ≤ C₁ * Real.sqrt (H (C₂ * s))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Space n, 1 / (2 * R) + 1 < ⟪y, ν⟫_ℝ →
      |‖y‖ ^ (1 - (n : ℝ)) * u (‖y‖⁻¹ ^ 2 • y)|
        ≤ K * ‖y‖ ^ 2 * Real.sqrt (Real.sqrt (H (2 * C₂ / ‖y‖))) := by
  obtain ⟨Cn, hCn0, hCn⟩ := harmonic_abs_le_L2' n
  refine ⟨Cn * Real.sqrt 8 ^ (n + 1) * Real.sqrt C₁, by positivity, fun y hy => ?_⟩
  have hp : ⟪y, ν⟫_ℝ ≤ ‖y‖ := by
    have := real_inner_le_norm y ν
    rwa [hν, mul_one] at this
  have hlam : 1 ≤ 1 / (2 * R) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hs1 : 1 / (2 * R) + 1 < ‖y‖ := lt_of_lt_of_le hy hp
  have hspos : 0 < ‖y‖ := by linarith
  have h2s : 2 / ‖y‖ < 4 * R := by
    rw [div_lt_iff₀ hspos]
    have h1 := mul_lt_mul_of_pos_left hs1 (by positivity : (0 : ℝ) < 2 * R)
    have h2 : 2 * R * (1 / (2 * R)) = 1 := by field_simp
    rw [mul_add, h2] at h1
    linarith
  set r : ℝ := ‖y‖⁻¹ ^ 2 / 8 with hr_def
  have hr : 0 < r := by positivity
  have hsub : Metric.closedBall (kinv y) r ⊆ domain Γ ρ :=
    (closedBall_subset_tangentBall hν hR hR2 y hy).trans hball
  have hharm : HarmonicOnNhd u (Metric.closedBall (kinv y) r) := hu.mono hsub
  have h1 := hCn u (kinv y) r hr hharm
  have hsub2 : Metric.ball (kinv y) r ⊆ domain Γ ρ ∩ Metric.ball 0 (2 / ‖y‖) := by
    intro x hx
    refine ⟨hsub (Metric.ball_subset_closedBall hx), ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hx2 := norm_le_insert' x (kinv y)
    rw [norm_kinv] at hx2
    have ht1 : ‖y‖⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hspos]
      linarith
    have htpos : 0 < ‖y‖⁻¹ := inv_pos.2 hspos
    have hr2 : r < ‖y‖⁻¹ := by
      rw [hr_def]
      nlinarith
    rw [div_eq_mul_inv]
    linarith
  have h2sρ : 2 / ‖y‖ < ρ := by linarith
  have hint := integrableOn_u_sq hΓc u hu_cont h2sρ
  have hI : ∫ x in Metric.ball (kinv y) r, u x ^ 2 ≤ C₁ * Real.sqrt (H (C₂ * (2 / ‖y‖))) := by
    refine le_trans ?_ (hL2 (2 / ‖y‖) ⟨by positivity, by linarith⟩)
    exact setIntegral_mono_set hint (ae_of_all _ (fun x => sq_nonneg (u x)))
      hsub2.eventuallySubset
  have hsq : Real.sqrt (∫ x in Metric.ball (kinv y) r, u x ^ 2)
      ≤ Real.sqrt C₁ * Real.sqrt (Real.sqrt (H (2 * C₂ / ‖y‖))) := by
    rw [← Real.sqrt_mul hC₁, show 2 * C₂ / ‖y‖ = C₂ * (2 / ‖y‖) by ring]
    exact Real.sqrt_le_sqrt hI
  have hrp : r ^ (-((n + 1 : ℝ) / 2)) = (Real.sqrt 8 * ‖y‖) ^ (n + 1) := rpow_radius n hspos
  have hu_le : |u (kinv y)| ≤ Cn * (Real.sqrt 8 * ‖y‖) ^ (n + 1) *
      (Real.sqrt C₁ * Real.sqrt (Real.sqrt (H (2 * C₂ / ‖y‖)))) := by
    rw [← hrp]
    refine h1.trans ?_
    have : 0 ≤ Cn * r ^ (-((n + 1 : ℝ) / 2)) :=
      mul_nonneg hCn0 (Real.rpow_nonneg hr.le _)
    exact mul_le_mul_of_nonneg_left hsq this
  have hpow : ‖y‖ ^ (1 - (n : ℝ)) * ‖y‖ ^ (n + 1) = ‖y‖ ^ 2 := by
    rw [← Real.rpow_natCast ‖y‖ (n + 1), ← Real.rpow_add hspos]
    rw [show (1 - (n : ℝ)) + ((n + 1 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast _ _
  have hpos : 0 < ‖y‖ ^ (1 - (n : ℝ)) := Real.rpow_pos_of_pos hspos _
  calc |‖y‖ ^ (1 - (n : ℝ)) * u (‖y‖⁻¹ ^ 2 • y)|
      = ‖y‖ ^ (1 - (n : ℝ)) * |u (kinv y)| := by
        rw [abs_mul, abs_of_pos hpos]
        rfl
    _ ≤ ‖y‖ ^ (1 - (n : ℝ)) * (Cn * (Real.sqrt 8 * ‖y‖) ^ (n + 1) *
        (Real.sqrt C₁ * Real.sqrt (Real.sqrt (H (2 * C₂ / ‖y‖))))) :=
        mul_le_mul_of_nonneg_left hu_le hpos.le
    _ = Cn * Real.sqrt 8 ^ (n + 1) * Real.sqrt C₁ * (‖y‖ ^ (1 - (n : ℝ)) * ‖y‖ ^ (n + 1)) *
        Real.sqrt (Real.sqrt (H (2 * C₂ / ‖y‖))) := by ring
    _ = Cn * Real.sqrt 8 ^ (n + 1) * Real.sqrt C₁ * ‖y‖ ^ 2 *
        Real.sqrt (Real.sqrt (H (2 * C₂ / ‖y‖))) := by rw [hpow]

end MainBAux

open MainBAux in
/-- **Theorem I(b).** Let `u` be harmonic in the domain above the graph of a smooth `Γ`, with `u`
and `∇u` (written `Du`) continuous up to the graph. Suppose the Dirichlet data vanish to infinite
order at `0` and the normal derivative is bounded by `h(|x|)` on the graph. Assume `h` is positive
and nondecreasing on `(0, ρ)`, and that `Λ(σ) = log(1/h(e^{-σ}))` satisfies `Λ(σ)/σ → ∞`, is convex
for large `σ`, and has at most exponential growth `Λ(σ + t) ≤ e^{C t} Λ(σ)` (that is, `Λ' ≤ C Λ`).
If `∫₀ log h = -∞` (stated on `(0, ρ/2)`), then `u = 0` near `0`. -/
theorem mainB {n : ℕ} (hn : 0 < n)
    (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ) (hΓ0 : Γ 0 = 0) (ρ : ℝ) (hρ : 0 < ρ)
    (u : Space n → ℝ) (Du : Space n → Space n)
    (hu : HarmonicOnNhd u (domain Γ ρ))
    (hu_cont : ContinuousOn u (domainWithBoundary Γ ρ))
    (hDu_cont : ContinuousOn Du (domainWithBoundary Γ ρ))
    (hDu : ∀ x ∈ domain Γ ρ, gradient u x = Du x)
    (hDir : ∀ N : ℕ, ∃ C : ℝ, ∀ x ∈ boundaryPiece Γ ρ, |u x| ≤ C * ‖x‖ ^ N)
    (h : ℝ → ℝ)
    (hNeu : ∀ x ∈ boundaryPiece Γ ρ, |⟪Du x, outerNormal Γ x⟫_ℝ| ≤ h ‖x‖)
    (hh_pos : ∀ r ∈ Set.Ioo 0 ρ, 0 < h r)
    (hh_mono : MonotoneOn h (Set.Ioo 0 ρ))
    (hΛ_super : Tendsto (fun σ => Real.log (1 / h (Real.exp (-σ))) / σ) atTop atTop)
    (hΛ_convex : ∃ σ₀ : ℝ,
      ConvexOn ℝ (Set.Ici σ₀) (fun σ => Real.log (1 / h (Real.exp (-σ)))))
    (hΛ_growth : ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ t ≥ 0,
      Real.log (1 / h (Real.exp (-(σ + t))))
        ≤ Real.exp (C * t) * Real.log (1 / h (Real.exp (-σ))))
    (hlog : Tendsto (fun ε => ∫ r in ε..(ρ / 2), Real.log (h r)) (𝓝[>] 0) atBot) :
    ∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → u x = 0 := by
  classical
  have hΓc : Continuous Γ := hΓ.continuous
  /- Step 0: the equation in divergence form, with `a = id`, `b = 0`, `c = 0`. -/
  have hL : ∀ x ∈ domain Γ ρ,
      divergence (fun y => (fun _ : Space n => ContinuousLinearMap.id ℝ (Space n)) y
          (gradient u y)) x
        + ⟪(fun _ : Space n => (0 : Space n)) x, gradient u x⟫_ℝ
        + (fun _ : Space n => (0 : ℝ)) x * u x = 0 := by
    intro x hx
    have h0 := divergence_gradient_eq_zero hu x hx
    simp only [ContinuousLinearMap.id_apply, inner_zero_left, zero_mul, add_zero]
    exact h0
  /- Step 1: the collar. -/
  obtain ⟨κ, hκ, hcol⟩ := collar_reduction hn Γ hΓ hΓ0 ρ hρ
    (fun _ => ContinuousLinearMap.id ℝ (Space n)) contDiff_const (fun _ _ _ => rfl)
    ⟨1, one_pos, fun _ ξ => by simp⟩
    (fun _ => 0) continuous_const (fun _ => 0) continuous_const u Du hu.contDiffOn hu_cont
    hDu_cont hDu hL hDir
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ
  obtain ⟨S, F, hSR, hFv, hFflat, hFcover, hFopen, hFL2⟩ := hcol (ρ / (2 * κ)) (by positivity)
  /- Step 2: the extension `H` of `h` and the profile `g` for the half-ball solution. -/
  set H : ℝ → ℝ := hExt h ρ with hH_def
  have hH_pos : ∀ r, 0 < r → 0 < H r := hExt_pos hρ h hh_pos
  have hH_mono : MonotoneOn H (Set.Ioi 0) := hExt_mono hρ h hh_mono
  have hH_eq : ∀ r, 0 < r → r ≤ ρ / 2 → H r = h r := fun r _ hr => hExt_eq h ρ hr
  have hH_reg : RegularProfile H := hExt_regular hρ h hΛ_super hΛ_convex hΛ_growth
  set g : ℝ → ℝ := fun r => κ * H (κ * r) with hg_def
  have hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖ := by
    intro X hX hX0
    obtain ⟨hFX, hFX1, hFX2, hFX3⟩ := hFflat X hX
    have hXpos : 0 < ‖X‖ := norm_pos_iff.2 hX0
    have hFXpos : 0 < ‖F X‖ := by
      by_contra hcon
      have : ‖F X‖ = 0 := le_antisymm (not_lt.1 hcon) (norm_nonneg _)
      rw [this, mul_zero] at hFX2
      linarith
    have hXR : ‖X‖ < S.R := hX.1
    have hκX : κ * ‖X‖ < ρ / 2 := by
      calc κ * ‖X‖ < κ * (ρ / (2 * κ)) := by
            gcongr
            exact lt_of_lt_of_le hXR hSR
        _ = ρ / 2 := by field_simp
    have h1 : |⟪S.A X (S.Dv X), ed n⟫_ℝ| ≤ κ * |⟪Du (F X), outerNormal Γ (F X)⟫_ℝ| := hFX3
    have h2 : |⟪Du (F X), outerNormal Γ (F X)⟫_ℝ| ≤ h ‖F X‖ := hNeu (F X) hFX
    have h3 : h ‖F X‖ ≤ h (κ * ‖X‖) :=
      hh_mono ⟨hFXpos, by linarith⟩ ⟨by positivity, by linarith⟩ hFX1
    have h4 : H (κ * ‖X‖) = h (κ * ‖X‖) := hH_eq _ (by positivity) hκX.le
    calc |⟪S.A X (S.Dv X), ed n⟫_ℝ| ≤ κ * |⟪Du (F X), outerNormal Γ (F X)⟫_ℝ| := h1
      _ ≤ κ * h (κ * ‖X‖) := by gcongr; exact h2.trans h3
      _ = g ‖X‖ := by rw [hg_def]; dsimp only; rw [h4]
  have hg_pos : ∀ r, 0 < r → 0 < g r := fun r hr => mul_pos hκpos (hH_pos _ (mul_pos hκpos hr))
  have hg_mono : MonotoneOn g (Set.Ioi 0) := by
    intro r hr s hs hrs
    have hr' : (0 : ℝ) < r := hr
    have hs' : (0 : ℝ) < s := hs
    exact mul_le_mul_of_nonneg_left
      (hH_mono (mul_pos hκpos hr') (mul_pos hκpos hs') (mul_le_mul_of_nonneg_left hrs hκpos.le))
      hκpos.le
  have hg_reg : RegularProfile g := RegularProfile.scale H κ hκ hH_pos hH_mono hH_reg
  /- Step 3: interior decay and the `L²` bound for `u` near `0`. -/
  obtain ⟨Cd, r₀, hCd, hr₀, hdecay⟩ := S.interior_decay hn g hneu hg_pos hg_mono hg_reg
  have hSRpos := S.R_pos
  set s₁ : ℝ := min r₀ (S.R / 2) / κ with hs₁_def
  have hs₁ : 0 < s₁ := by positivity
  have hs₁ρ : s₁ < ρ := by
    have e1 : s₁ ≤ S.R / 2 / κ := div_le_div_of_nonneg_right (min_le_right _ _) hκpos.le
    have e2 : S.R / 2 / κ ≤ S.R / 2 := div_le_self (by positivity) hκ
    have e3 : S.R ≤ ρ / 2 := by
      calc S.R ≤ ρ / (2 * κ) := hSR
        _ ≤ ρ / 2 := div_le_div_of_nonneg_left hρ.le (by norm_num) (by linarith)
    linarith
  set C₁ : ℝ := κ * Cd * Real.sqrt κ with hC₁_def
  set C₂ : ℝ := κ * Cd * κ with hC₂_def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 < C₂ := by positivity
  have hL2 : ∀ s ∈ Set.Ioc 0 s₁,
      ∫ x in domain Γ ρ ∩ Metric.ball 0 s, u x ^ 2 ≤ C₁ * Real.sqrt (H (C₂ * s)) := by
    intro s hs
    have := L2_bound_u S hκ u hFL2 g hr₀ hdecay s hs
    have e : g (Cd * (κ * s)) = κ * H (C₂ * s) := by
      rw [hg_def, hC₂_def]; dsimp only; ring_nf
    rw [e, Real.sqrt_mul hκpos.le] at this
    calc ∫ x in domain Γ ρ ∩ Metric.ball 0 s, u x ^ 2
        ≤ κ * (Cd * (Real.sqrt κ * Real.sqrt (H (C₂ * s)))) := this
      _ = C₁ * Real.sqrt (H (C₂ * s)) := by rw [hC₁_def]; ring
  /- Step 4: the tangent ball and the Kelvin transform. -/
  obtain ⟨R₀, hR₀, hball⟩ := tangent_ball_subset_domain hn Γ hΓ hΓ0 ρ hρ
  set ν : Space n := innerNormalZero Γ with hν_def
  have hν : ‖ν‖ = 1 := norm_innerNormalZero_eq_one hΓ0 hR₀ (hball R₀ ⟨hR₀, le_rfl⟩)
  set R : ℝ := min (min R₀ (1 / 2)) (s₁ / 4) with hR_def
  have hR : 0 < R := by positivity
  have hRR₀ : R ≤ R₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR2 : R ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRs : 4 * R ≤ s₁ := by
    have := min_le_right (min R₀ (1 / 2)) (s₁ / 4)
    linarith
  have hballR : Metric.ball (R • ν) R ⊆ domain Γ ρ := hball R ⟨hR, hRR₀⟩
  set lam : ℝ := 1 / (2 * R) with hlam_def
  have hlam1 : 1 ≤ lam := by
    rw [hlam_def, le_div_iff₀ (by positivity)]
    linarith
  set U : Space n → ℝ := fun y => ‖y‖ ^ (1 - (n : ℝ)) * u (‖y‖⁻¹ ^ 2 • y) with hU_def
  have hUharm : HarmonicOnNhd U {y | lam < ⟪y, ν⟫_ℝ} := by
    have h0 : (0 : Space n) ∉ Metric.ball (R • ν) R := fun h0 =>
      ((mem_tangentBall_iff hν hR 0).1 h0).1 rfl
    have hk := kelvin_harmonicOnNhd Metric.isOpen_ball h0 u (hu.mono hballR)
    refine hk.mono ?_
    intro y hy
    have hy' : lam < ⟪y, ν⟫_ℝ := hy
    have hlam0 : 0 < lam := by positivity
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy'
      linarith
    refine ⟨hy0, ?_⟩
    have hk0 : kinv y ≠ 0 := by
      intro hk0
      have := norm_kinv y
      rw [hk0, norm_zero] at this
      exact hy0 (norm_eq_zero.1 (inv_eq_zero.1 this.symm))
    have := (mem_tangentBall_iff hν hR (kinv y)).2 ⟨hk0, by rw [kinv_kinv]; exact hy'⟩
    exact this
  /- Step 5: decay of the Kelvin transform. -/
  obtain ⟨K, hK0, hKbound⟩ :=
    kelvin_bound hΓc u hu hu_cont hν hR hR2 hballR H hC₁ hs₁ρ hRs hL2
  set C₃ : ℝ := 2 * C₂ with hC₃_def
  have hC₃ : 0 < C₃ := by positivity
  set ψ : ℝ → ℝ := psiOf H C₃ with hψ_def
  obtain ⟨Cu, hCu⟩ := psi_absorb hH_pos hH_mono hH_reg hC₃ 2 K hK0
  have hdecayU : ∀ y, lam + 1 < ⟪y, ν⟫_ℝ → |U y| ≤ Cu * Real.exp (-ψ ‖y‖) := by
    intro y hy
    have hy1 : 1 ≤ ‖y‖ := by
      have := real_inner_le_norm y ν
      rw [hν, mul_one] at this
      linarith
    exact (hKbound y hy).trans (hCu ‖y‖ hy1)
  have hψ_mono : MonotoneOn ψ (Set.Ici 1) :=
    (psiOf_mono hH_pos hH_mono hC₃).mono (fun s hs => lt_of_lt_of_le one_pos hs)
  have hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop := psiOf_log hH_reg hC₃
  have hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)) :=
    psiOf_convex hH_reg hC₃
  have hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1) :=
    psiOf_not_integrable hρ h H hh_pos hh_mono hH_eq hC₃ hlog
  /- Step 6: Lemma DC. -/
  have hU0 := harmonic_halfSpace_eq_zero hn ν hν (lam + 1) (by linarith) U
    (hUharm.mono (fun y (hy : lam + 1 < ⟪y, ν⟫_ℝ) => show lam < ⟪y, ν⟫_ℝ by linarith))
    ψ Cu hdecayU hψ_mono hψ_log hψ_convex hψ_div
  /- Step 7: `u = 0` on a smaller tangent ball. -/
  set R' : ℝ := 1 / (2 * (lam + 2)) with hR'_def
  have hlam0 : 0 < lam := by positivity
  have hR' : 0 < R' := by positivity
  have hR'R : R' ≤ R := by
    rw [hR'_def, div_le_iff₀ (by positivity), hlam_def]
    field_simp
    nlinarith
  have hu0 : ∀ x ∈ Metric.ball (R' • ν) R', u x = 0 := by
    intro x hx
    obtain ⟨hx0, hxin⟩ := (mem_tangentBall_iff hν hR' x).1 hx
    have e : 1 / (2 * R') = lam + 2 := by
      rw [hR'_def]; field_simp
    rw [e] at hxin
    have hUx := hU0 (kinv x) (by linarith)
    simp only [hU_def] at hUx
    have hpos : 0 < ‖kinv x‖ ^ (1 - (n : ℝ)) := by
      apply Real.rpow_pos_of_pos
      rw [norm_kinv]
      exact inv_pos.2 (norm_pos_iff.2 hx0)
    have : u (‖kinv x‖⁻¹ ^ 2 • kinv x) = 0 := by
      rcases mul_eq_zero.1 hUx with h' | h'
      · exact absurd h' hpos.ne'
      · exact h'
    have e2 : ‖kinv x‖⁻¹ ^ 2 • kinv x = x := kinv_kinv x
    rwa [e2] at this
  /- Step 8: weak unique continuation in collar coordinates. -/
  obtain ⟨ε, hε, hcover⟩ := hFcover
  have hW : (Metric.ball (R' • ν) R' ∩ F '' halfBall n S.R).Nonempty := by
    set t : ℝ := min R' (ε / 2) with ht_def
    have ht : 0 < t := by positivity
    have htR' : t ≤ R' := min_le_left _ _
    have htε : t < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hmem : t • ν ∈ Metric.ball (R' • ν) R' := by
      rw [Metric.mem_ball, dist_eq_norm, ← sub_smul, norm_smul, hν, mul_one, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      linarith
    have hdom : t • ν ∈ domain Γ ρ := hball R' ⟨hR', le_trans hR'R hRR₀⟩ hmem
    have hnorm : ‖t • ν‖ < ε := by
      rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos ht]
      exact htε
    obtain ⟨X, hX, hFX⟩ := hcover (t • ν) hdom hnorm
    exact ⟨t • ν, hmem, X, hX, hFX⟩
  obtain ⟨V, hVopen, hVne, hVsub, hVF⟩ := hFopen _ Metric.isOpen_ball hW
  obtain ⟨X₀, hX₀⟩ := hVne
  have hvV : ∀ X ∈ V, S.v X = 0 := by
    intro X hX
    rw [(hFv X (hVsub hX)).2]
    exact hu0 _ (hVF X hX)
  have hucp := weak_ucp (isOpen_halfBall S.R) (convex_halfBall S.R).isPreconnected
    S.A S.B S.C S.coeffs.contDiff_A.contDiffOn (fun x _ => S.coeffs.symm x)
    (fun x _ ξ hξ => by
      have h1 := S.coeffs.ell x ξ
      have h2 : 0 < S.lam * ‖ξ‖ ^ 2 := mul_pos S.coeffs.lam_pos (by positivity)
      linarith)
    S.coeffs.cont_B.continuousOn S.coeffs.cont_C.continuousOn S.v S.v_contDiffOn S.eqn
    X₀ (hVsub hX₀) (Filter.eventually_of_mem (hVopen.mem_nhds hX₀) hvV)
  refine ⟨ε, hε, fun x hx hxε => ?_⟩
  obtain ⟨X, hX, hFX⟩ := hcover x hx hxε
  rw [← hFX, ← (hFv X hX).2]
  exact hucp X hX

end MazyaRefinedCauchy
