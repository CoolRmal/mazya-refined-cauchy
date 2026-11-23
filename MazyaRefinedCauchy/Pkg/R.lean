module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F1
public import MazyaRefinedCauchy.Pkg.F2
public import MazyaRefinedCauchy.Pkg.F5
public import MazyaRefinedCauchy.Pkg.R1
public import MazyaRefinedCauchy.Pkg.G

@[expose] public section

/-!
# Work package R

The theorems stated in this file are the frozen contract of package R (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## Plan of the proof of Proposition R (Euclidean form of the note's proof)

Write `ρ = ‖x‖`, `d = n + 1`, `m = (d - 2) / 2`. The half-cylinder `(ds² + g_S)` of the note is
`B⁺ \ {0}` with the metric `ρ⁻² dx²`, so we work in `x` coordinates with the density
`μ = ρ^{-d}` (`muR`), the matrix field `B = ρ² A` (`BR`) and the weight
`φ = G(-log ρ) = -log ρ + ε ρ` (`phiR`), `G(s) = s + ε e^{-s}` (`GR`). The cylinder operator is
`P₀ f = div_μ(B ∇f) - m² f` (`P0R`), applied to `f = ψ ρ^m v` for a cutoff `ψ`.

* `step2` — the choice of `τ` (`2τ + 1 = Λ'(s₂)`), pure real analysis (proved).
* `flat_of_regular` — a regular profile is flat at `0` (proved).
* `caccioppoli` — Caccioppoli's inequality up to the flat boundary.
* `grad_infinite_order` — `∫_{B⁺_r} (v² + |∇v|²) = O(r^M)` from Lemma R1 and Caccioppoli.
* `carleman` — Lemma R2 in `x` coordinates.
* `transfer` — the equation for `v` gives a bound for `P₀(ψ ρ^m v)`.
* `step1` — the inequality (eq:Rmain) of the note, in `x` coordinates.
* `HalfBallSolution.interior_decay` — assembled from `step1`, `step2` and `caccioppoli`.

The contract assumes `0 < n`: for `n = 0` it is false (see the comment in the proof of
`HalfBallSolution.interior_decay`).

## Status (end of round 1)

Proved: `step2`, `flat_of_regular`, `l2_decay`, the contract theorem for `0 < n` (modulo the
items below), `caccioppoli`, `grad_infinite_order`, `step1` (the limit `δ → 0`), the reduction
`step1_fixed_delta` ⇐ (`carleman`, `transfer`, cutoff lemmas), `fS_carleman_hyps`,
`P0_fS_bound`, `fS_lhs_lower`, `fS_bdry_upper`, `FS_upper`, `gradient_hS`,
`psiS_deriv_eq_zero`.

Open: `carleman`, `transfer`, `psiS_deriv_bound` (Hessian of `ψ_δ`), and the case `n = 0` of
the contract theorem (false).

* `psiS_deriv_bound`: `∇ψ = a(x) x` (`gradient_psiS`), so `D∇ψ = a I + x ⊗ ∇a`; `∇a` involves
  `Θ_in''`; on the supports `ρ ≤ δ` resp. `ρ ≤ r₁` this gives `ρ²‖D∇ψ‖ ≤ C`.
* `transfer`: with `h = ψ ρ^m`, `div_μ(B∇(h v)) = ρ²h div(A∇v) + 2ρ²⟪A∇h,∇v⟫ + (2-d)h⟪Ax,∇v⟫
  + v div_μ(B∇h)`; the `⟪Ax,∇v⟫` terms cancel (`2 - d = -2m`), and
  `div_μ(B∇ρ^m) - m²ρ^m = m ρ^m (div(Ax) - d - (m+2)(⟪Ax̂,x̂⟫ - 1)) = O(ρ^{m+1})`
  (`|A - I| ≤ Kρ`, `|DA| ≤ K`). The equation gives `div(A∇v) = -⟪B,∇v⟫ - Cv`.
* `carleman` (Lemma R2): `w = e^{τφ} f`, `Dw = e^{τφ}(Df + τ f ∇φ)`, `∇φ = -(1-ερ) x/ρ²`,
  `V = carlV (BR A) φ = -(1-ερ) A x`, `q = (1-ερ)² ⟪Ax,x⟫/ρ²`; on `{t = 0}`,
  `⟪V, e_d⟫ = 0` and `⟪A∇φ, e_d⟫ = 0` (conormal + symmetry). Steps:
  (i) `F2.carleman_conj_of_symm'`: `e^{τφ}(P₀f + m² f) = S w + T w`;
  (ii) `carleman_pointwise` + `integral_divergence_halfSpace_of_continuousOn` with the flux
  written with `Dw` (continuous up to `t = 0`); `S w` is bounded via the `P₀` hypothesis, so the
  divergence is integrable; (iii) `w T w μ = -τ div(w² μ V)`, no boundary term;
  (iv) `J ≥ …`: the `G''` terms give `4τ G'' ⟪Ax,∇w⟫² μ ≥ 0` and
  `2τ³ μ ⟪V,∇q⟫ w² ≥ 2τ³ μ ρ ((3/4)ε - CK) w²`; the `∇div_μ V` term is integrated by parts
  along `A x` (tangent to `{t = 0}`); (v) `carleman_gradient_pointwise` with `ϱ = ρ`;
  (vi) every boundary term contains `⟪B∇w, e_d⟫ = ρ² e^{τφ} ⟪A Df, e_d⟫`.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

namespace RPkg

/-! ### Real analysis: supporting lines of convex functions

Adapted from the project's scouting prototypes (`scratchpad/wf1/analysis/Proto.lean`). -/

/-- Supporting line at an interior point, with slope the right derivative. -/
theorem convex_add_rightDeriv_mul_le {S : Set ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) (hy : y ∈ S) :
    f x + derivWithin f (Set.Ioi x) x * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at h
    linarith
  · simp
  · have h1 := hf.slope_le_leftDeriv_of_mem_interior hy hx hyx
    have h2 := hf.leftDeriv_le_rightDeriv_of_mem_interior hx
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at h1
    nlinarith

/-- Chord slope from the left is below the right derivative. -/
theorem convex_slope_le_rightDeriv {S : Set ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hf : ConvexOn ℝ S f) (hy : y ∈ S) (hx : x ∈ interior S) (hyx : y < x) :
    (f x - f y) / (x - y) ≤ derivWithin f (Set.Ioi x) x := by
  have h1 := hf.slope_le_leftDeriv_of_mem_interior hy hx hyx
  rw [slope_def_field] at h1
  exact h1.trans (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)

/-- Bound on the right derivative from the integrated growth condition. -/
theorem convex_rightDeriv_le_of_growth {f : ℝ → ℝ} {a x C : ℝ}
    (hf : ConvexOn ℝ (Set.Ici a) f) (hx : a < x) (hg : f (x + 1) ≤ Real.exp C * f x) :
    derivWithin f (Set.Ioi x) x ≤ (Real.exp C - 1) * f x := by
  have hxi : x ∈ interior (Set.Ici a) := by rw [interior_Ici]; exact hx
  have h := hf.rightDeriv_le_slope_of_mem_interior hxi (show x + 1 ∈ Set.Ici a from by
    simp only [Set.mem_Ici]; linarith) (by linarith)
  rw [slope_def_field] at h
  simp only [add_sub_cancel_left, div_one] at h
  linarith

/-- The right derivative of a superlinear convex function tends to `+∞`. -/
theorem convex_tendsto_rightDeriv_atTop {f : ℝ → ℝ} {a : ℝ} (hf : ConvexOn ℝ (Set.Ici a) f)
    (hsup : Tendsto (fun x => f x / x) atTop atTop) :
    Tendsto (fun x => derivWithin f (Set.Ioi x) x) atTop atTop := by
  have key : ∀ x, a < x → (f x - f a) / (x - a) ≤ derivWithin f (Set.Ioi x) x := fun x hx =>
    convex_slope_le_rightDeriv hf Set.self_mem_Ici (by rw [interior_Ici]; exact hx) hx
  have hlow : Tendsto (fun x => f x / x / 2 - |f a|) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hsup.atTop_div_const two_pos)
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [eventually_gt_atTop a, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (-a), eventually_ge_atTop (1 : ℝ),
    hsup.eventually_ge_atTop (|f a| + 1)] with x hxa hx0 hxa' hx1 hfx
  refine le_trans ?_ (key x hxa)
  have hxa0 : 0 < x - a := sub_pos.mpr hxa
  have hfx' : x * (|f a| + 1) ≤ f x := by rwa [le_div_iff₀ hx0, mul_comm] at hfx
  have hfa : f a ≤ |f a| := le_abs_self _
  have h1 : |f a| ≤ x * (|f a| + 1) := by nlinarith [abs_nonneg (f a)]
  have hnum : 0 ≤ f x - f a := by linarith
  have hden : x - a ≤ 2 * x := by linarith
  calc f x / x / 2 - |f a| ≤ (f x - f a) / (2 * x) := by
        rw [div_div, mul_comm x 2, sub_div]
        gcongr
        rw [div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg (f a)]
    _ ≤ (f x - f a) / (x - a) := div_le_div_of_nonneg_left hnum hxa0 hden

/-! ### The weight profile `G(s) = s + ε e^{-s}` and the choice of `τ` -/

/-- `G(s) = s + ε e^{-s}`. -/
noncomputable def GR (ε s : ℝ) : ℝ := s + ε * Real.exp (-s)

theorem GR_ge (ε s : ℝ) (hε : 0 ≤ ε) : s ≤ GR ε s := by
  unfold GR
  have := Real.exp_pos (-s)
  nlinarith

theorem GR_le_of_ge {ε s s₁ : ℝ} (hε : 0 ≤ ε) (hs : s₁ ≤ s) :
    GR ε s ≤ s + ε * Real.exp (-s₁) := by
  unfold GR
  have : Real.exp (-s) ≤ Real.exp (-s₁) := Real.exp_le_exp.2 (by linarith)
  nlinarith

/-- `G` is nondecreasing on `[a, ∞)` as soon as `ε e^{-a} ≤ 1`. -/
theorem GR_mono {ε a b c : ℝ} (hε : 0 ≤ ε) (ha : ε * Real.exp (-a) ≤ 1) (hab : a ≤ b)
    (hbc : b ≤ c) : GR ε b ≤ GR ε c := by
  unfold GR
  have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
  -- `e^{-b} - e^{-c} = e^{-b} (1 - e^{-(c-b)}) ≤ e^{-b} (c - b)`
  have h2 : 1 - Real.exp (-(c - b)) ≤ c - b := by
    have := Real.add_one_le_exp (-(c - b))
    linarith
  have h3 : Real.exp (-c) = Real.exp (-b) * Real.exp (-(c - b)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-b) - Real.exp (-c) ≤ Real.exp (-b) * (c - b) := by
    rw [h3]
    have := Real.exp_pos (-b)
    nlinarith
  have h5 : ε * Real.exp (-b) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left h1 hε) ha
  have h6 : ε * (Real.exp (-b) - Real.exp (-c)) ≤ c - b := by
    calc ε * (Real.exp (-b) - Real.exp (-c)) ≤ ε * (Real.exp (-b) * (c - b)) :=
          mul_le_mul_of_nonneg_left h4 hε
      _ = (ε * Real.exp (-b)) * (c - b) := by ring
      _ ≤ 1 * (c - b) := mul_le_mul_of_nonneg_right h5 (by linarith)
      _ = c - b := one_mul _
  nlinarith

/-- **Step 2 of the proof of Proposition R: the choice of `τ`.** Let `Λ` be convex on
`[σ₀, ∞)`, superlinear, with `Λ(σ + t) ≤ e^{Ct} Λ(σ)`. If a quantity `I(s₂)` satisfies the
Carleman inequality (eq:Rmain) of the note for every `τ ≥ τ₀` and every bound `Bd` of
`e^{2τ G(s) - Λ(s)}` on `[s₁, ∞)`, then `I(s₂) ≤ e^{-Λ(s₂)/2}` for large `s₂`. The threshold
for `s₁` depends only on `ε`, `σ₀` and `C`. -/
theorem step2 (Λ : ℝ → ℝ) (σ₀ : ℝ) (hconv : ConvexOn ℝ (Set.Ici σ₀) Λ)
    (hsuper : Tendsto (fun σ => Λ σ / σ) atTop atTop) (C σ₁ : ℝ)
    (hgrowth : ∀ σ ≥ σ₁, ∀ t ≥ 0, Λ (σ + t) ≤ Real.exp (C * t) * Λ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ smin : ℝ, ∀ s₁ ≥ smin, ∀ C₀ τ₀ : ℝ, 0 < C₀ → 0 < τ₀ → ∀ I : ℝ → ℝ,
      (∀ τ ≥ τ₀, ∀ s₂ ≥ s₁ + 2, ∀ Bd : ℝ,
        (∀ s ≥ s₁, Real.exp (2 * τ * GR ε s - Λ s) ≤ Bd) →
        τ ^ 3 * Real.exp (2 * τ * GR ε s₂) * I s₂
          ≤ C₀ * Real.exp (2 * τ * GR ε (s₁ + 1)) + C₀ * τ ^ 2 * Bd) →
      ∀ᶠ s₂ in atTop, I s₂ ≤ Real.exp (-Λ s₂ / 2) := by
  set D : ℝ := Real.exp |C| with hD
  have hD1 : 1 ≤ D := Real.one_le_exp (abs_nonneg C)
  have hCD : Real.exp C - 1 ≤ D := by
    have : Real.exp C ≤ Real.exp |C| := Real.exp_le_exp.2 (le_abs_self C)
    linarith
  refine ⟨max (max σ₀ 0) (Real.log (4 * ε * D)), fun s₁ hs₁ C₀ τ₀ hC₀ hτ₀ I hI => ?_⟩
  have hs₁σ₀ : σ₀ ≤ s₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs₁
  have hs₁0 : 0 ≤ s₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs₁
  have hs₁D : Real.log (4 * ε * D) ≤ s₁ := le_trans (le_max_right _ _) hs₁
  have hes : 0 < Real.exp (-s₁) := Real.exp_pos _
  -- `ε D e^{-s₁} ≤ 1/4`
  have hεD : ε * D * Real.exp (-s₁) ≤ 1 / 4 := by
    have h4 : 4 * ε * D ≤ Real.exp s₁ := by
      calc 4 * ε * D = Real.exp (Real.log (4 * ε * D)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp s₁ := Real.exp_le_exp.2 hs₁D
    have e : Real.exp (-s₁) * Real.exp s₁ = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hεs : ε * Real.exp (-s₁) ≤ 1 / 4 := by
    have h1 : ε * Real.exp (-s₁) * 1 ≤ ε * Real.exp (-s₁) * D :=
      mul_le_mul_of_nonneg_left hD1 (by positivity)
    have e : ε * D * Real.exp (-s₁) = ε * Real.exp (-s₁) * D := by ring
    linarith
  -- right derivative and its growth
  have hk_top : Tendsto (fun x => derivWithin Λ (Set.Ioi x) x) atTop atTop :=
    convex_tendsto_rightDeriv_atTop hconv hsuper
  set L₁ : ℝ := |Real.log (2 * C₀ / τ₀ ^ 3)| + |Λ (s₁ + 2)| with hL₁
  set L₂ : ℝ := |Real.log (2 * C₀ / τ₀)| with hL₂
  have hev5 : ∀ᶠ s₂ in atTop, 5 * s₂ ≤ Λ s₂ := by
    filter_upwards [hsuper.eventually (eventually_ge_atTop 5), eventually_gt_atTop 0]
      with s h1 h2
    rwa [le_div_iff₀ h2] at h1
  filter_upwards [hev5, hk_top.eventually (eventually_ge_atTop (2 * τ₀ + 1)),
    eventually_ge_atTop (s₁ + 2), eventually_gt_atTop σ₀, eventually_ge_atTop σ₁,
    eventually_ge_atTop L₁, eventually_ge_atTop (4 * L₂), eventually_ge_atTop 0]
    with s₂ h5 hk2 hs₂ hs₂σ₀ hs₂σ₁ hs₂L₁ hs₂L₂ hs₂0
  set k : ℝ := derivWithin Λ (Set.Ioi s₂) s₂ with hk
  set τ : ℝ := (k - 1) / 2 with hτ
  have hτ₀τ : τ₀ ≤ τ := by rw [hτ]; linarith
  have hτpos : 0 < τ := lt_of_lt_of_le hτ₀ hτ₀τ
  have hΛ0 : 0 ≤ Λ s₂ := by linarith
  have hint : s₂ ∈ interior (Set.Ici σ₀) := by rw [interior_Ici]; exact hs₂σ₀
  have hsupp : ∀ y, σ₀ ≤ y → Λ s₂ + k * (y - s₂) ≤ Λ y := fun y hy =>
    convex_add_rightDeriv_mul_le hconv hint hy
  have hkbound : k ≤ (Real.exp C - 1) * Λ s₂ := by
    have hg1 := hgrowth s₂ hs₂σ₁ 1 zero_le_one
    rw [mul_one] at hg1
    exact convex_rightDeriv_le_of_growth hconv hs₂σ₀ hg1
  have hkD : k ≤ D * Λ s₂ := le_trans hkbound (mul_le_mul_of_nonneg_right hCD hΛ0)
  have hk' : k = 2 * τ + 1 := by rw [hτ]; ring
  -- the bound `Bd`
  set Bd : ℝ := Real.exp (2 * τ * (ε * Real.exp (-s₁)) + 2 * τ * s₂ - Λ s₂ + s₂ - s₁) with hBd
  have hBdprop : ∀ s ≥ s₁, Real.exp (2 * τ * GR ε s - Λ s) ≤ Bd := by
    intro s hs
    apply Real.exp_le_exp.2
    have hG := GR_le_of_ge hε.le hs
    have hL := hsupp s (le_trans hs₁σ₀ hs)
    have h1 : 2 * τ * GR ε s ≤ 2 * τ * (s + ε * Real.exp (-s₁)) :=
      mul_le_mul_of_nonneg_left hG (by linarith)
    rw [hk'] at hL
    nlinarith
  have hmain := hI τ hτ₀τ s₂ hs₂ Bd hBdprop
  -- positivity of the prefactor
  set E : ℝ := Real.exp (2 * τ * GR ε s₂) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (2 * τ * s₂) ≤ E :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (GR_ge ε s₂ hε.le) (by linarith))
  have hP : 0 < τ ^ 3 * E := by positivity
  -- term A
  have hTA : C₀ * Real.exp (2 * τ * GR ε (s₁ + 1)) ≤ τ ^ 3 * E * Real.exp (-Λ s₂ / 2) / 2 := by
    have hG1 : GR ε (s₁ + 1) ≤ s₁ + 2 := by
      have := GR_le_of_ge hε.le (show s₁ ≤ s₁ + 1 by linarith)
      linarith
    have hexpA : Real.exp (2 * τ * GR ε (s₁ + 1)) ≤ Real.exp (2 * τ * (s₁ + 2)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hG1 (by linarith))
    -- the exponent `X_A = 2τ(s₂ - s₁ - 2) - Λ/2`
    have hLs := hsupp (s₁ + 2) (by linarith)
    have hXA : Real.log (2 * C₀ / τ₀ ^ 3) ≤ 2 * τ * (s₂ - (s₁ + 2)) - Λ s₂ / 2 := by
      have h1 : Real.log (2 * C₀ / τ₀ ^ 3) ≤ |Real.log (2 * C₀ / τ₀ ^ 3)| := le_abs_self _
      have h2 : Λ (s₁ + 2) ≤ |Λ (s₁ + 2)| := le_abs_self _
      rw [hk'] at hLs
      nlinarith
    have hexpXA : 2 * C₀ / τ₀ ^ 3 ≤ Real.exp (2 * τ * (s₂ - (s₁ + 2)) - Λ s₂ / 2) := by
      calc 2 * C₀ / τ₀ ^ 3 = Real.exp (Real.log (2 * C₀ / τ₀ ^ 3)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.2 hXA
    have hτ3 : τ₀ ^ 3 ≤ τ ^ 3 := pow_le_pow_left₀ hτ₀.le hτ₀τ 3
    have hC₀le : C₀ ≤ τ ^ 3 / 2 * Real.exp (2 * τ * (s₂ - (s₁ + 2)) - Λ s₂ / 2) := by
      have h1 : C₀ = τ₀ ^ 3 / 2 * (2 * C₀ / τ₀ ^ 3) := by field_simp
      rw [h1]
      apply mul_le_mul (by linarith) hexpXA (by positivity) (by positivity)
    have hsplit : Real.exp (2 * τ * s₂) * Real.exp (-Λ s₂ / 2)
        = Real.exp (2 * τ * (s₁ + 2)) * Real.exp (2 * τ * (s₂ - (s₁ + 2)) - Λ s₂ / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc C₀ * Real.exp (2 * τ * GR ε (s₁ + 1))
        ≤ C₀ * Real.exp (2 * τ * (s₁ + 2)) := mul_le_mul_of_nonneg_left hexpA hC₀.le
      _ ≤ (τ ^ 3 / 2 * Real.exp (2 * τ * (s₂ - (s₁ + 2)) - Λ s₂ / 2)) *
            Real.exp (2 * τ * (s₁ + 2)) := mul_le_mul_of_nonneg_right hC₀le (Real.exp_pos _).le
      _ = τ ^ 3 * (Real.exp (2 * τ * s₂) * Real.exp (-Λ s₂ / 2)) / 2 := by rw [hsplit]; ring
      _ ≤ τ ^ 3 * (E * Real.exp (-Λ s₂ / 2)) / 2 := by
          gcongr
      _ = τ ^ 3 * E * Real.exp (-Λ s₂ / 2) / 2 := by ring
  -- term B
  have hTB : C₀ * τ ^ 2 * Bd ≤ τ ^ 3 * E * Real.exp (-Λ s₂ / 2) / 2 := by
    have h2τ : 2 * τ * (ε * Real.exp (-s₁)) ≤ Λ s₂ / 4 := by
      have h1 : 2 * τ ≤ D * Λ s₂ := by linarith
      have h2 : 2 * τ * (ε * Real.exp (-s₁)) ≤ D * Λ s₂ * (ε * Real.exp (-s₁)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : D * Λ s₂ * (ε * Real.exp (-s₁)) = Λ s₂ * (ε * D * Real.exp (-s₁)) := by ring
      have h4 : Λ s₂ * (ε * D * Real.exp (-s₁)) ≤ Λ s₂ * (1 / 4) :=
        mul_le_mul_of_nonneg_left hεD hΛ0
      linarith
    have hBd_le : Bd ≤ Real.exp (2 * τ * s₂ - 3 / 4 * Λ s₂ + s₂) :=
      Real.exp_le_exp.2 (by linarith)
    have hXB : Real.log (2 * C₀ / τ₀) ≤ Λ s₂ / 4 - s₂ := by
      have h1 : Real.log (2 * C₀ / τ₀) ≤ |Real.log (2 * C₀ / τ₀)| := le_abs_self _
      linarith
    have hexpXB : 2 * C₀ / τ₀ ≤ Real.exp (Λ s₂ / 4 - s₂) := by
      calc 2 * C₀ / τ₀ = Real.exp (Real.log (2 * C₀ / τ₀)) := (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.2 hXB
    have hC₀le : C₀ ≤ τ / 2 * Real.exp (Λ s₂ / 4 - s₂) := by
      have h1 : C₀ = τ₀ / 2 * (2 * C₀ / τ₀) := by field_simp
      rw [h1]
      exact mul_le_mul (by linarith) hexpXB (by positivity) (by positivity)
    have hsplit : Real.exp (2 * τ * s₂) * Real.exp (-Λ s₂ / 2)
        = Real.exp (2 * τ * s₂ - 3 / 4 * Λ s₂ + s₂) * Real.exp (Λ s₂ / 4 - s₂) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc C₀ * τ ^ 2 * Bd ≤ C₀ * τ ^ 2 * Real.exp (2 * τ * s₂ - 3 / 4 * Λ s₂ + s₂) :=
          mul_le_mul_of_nonneg_left hBd_le (by positivity)
      _ ≤ (τ / 2 * Real.exp (Λ s₂ / 4 - s₂)) * τ ^ 2 *
            Real.exp (2 * τ * s₂ - 3 / 4 * Λ s₂ + s₂) := by gcongr
      _ = τ ^ 3 * (Real.exp (2 * τ * s₂) * Real.exp (-Λ s₂ / 2)) / 2 := by rw [hsplit]; ring
      _ ≤ τ ^ 3 * (E * Real.exp (-Λ s₂ / 2)) / 2 := by gcongr
      _ = τ ^ 3 * E * Real.exp (-Λ s₂ / 2) / 2 := by ring
  have hfin : τ ^ 3 * E * I s₂ ≤ τ ^ 3 * E * Real.exp (-Λ s₂ / 2) := by
    have := add_le_add hTA hTB
    linarith
  exact le_of_mul_le_mul_left hfin hP

/-! ### Regular profiles are flat -/

/-- A positive nondecreasing regular profile is flat at `0`: `g(r) = O(r^N)` for every `N`. -/
theorem flat_of_regular (g : ℝ → ℝ) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (hg_mono : MonotoneOn g (Set.Ioi 0)) (hg : RegularProfile g) (R : ℝ) (hR : 0 < R) :
    ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 R, g r ≤ Cg * r ^ N := by
  intro N
  obtain ⟨σN, hσN⟩ := eventually_atTop.1
    ((hg.super.eventually (eventually_ge_atTop (N : ℝ))).and (eventually_gt_atTop (0 : ℝ)))
  set σ' : ℝ := max σN 1 with hσ'
  refine ⟨max 1 (g R * Real.exp (N * σ')), fun r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  by_cases hrs : r ≤ Real.exp (-σ')
  · have hσ : σ' ≤ -Real.log r := by
      have : Real.log r ≤ Real.log (Real.exp (-σ')) := Real.log_le_log hr0 hrs
      rw [Real.log_exp] at this
      linarith
    obtain ⟨h1, h2⟩ := hσN (-Real.log r) (le_trans (le_max_left _ _) hσ)
    rw [neg_neg, Real.exp_log hr0, le_div_iff₀ h2] at h1
    have hgr := hg_pos r hr0
    have hgle : g r ≤ r ^ N := by
      rw [one_div, Real.log_inv] at h1
      have h3 : Real.log (g r) ≤ Real.log (r ^ N) := by rw [Real.log_pow]; linarith
      exact (Real.log_le_log_iff hgr (pow_pos hr0 N)).1 h3
    calc g r ≤ r ^ N := hgle
      _ ≤ max 1 (g R * Real.exp (N * σ')) * r ^ N :=
          le_mul_of_one_le_left (pow_nonneg hr0.le N) (le_max_left _ _)
  · push Not at hrs
    have h1 : g r ≤ g R := hg_mono (Set.mem_Ioi.2 hr0) (Set.mem_Ioi.2 hR) hr.2.le
    have h2 : Real.exp (-(N * σ')) ≤ r ^ N := by
      calc Real.exp (-(N * σ')) = Real.exp (-σ') ^ N := by
            rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ r ^ N := pow_le_pow_left₀ (Real.exp_pos _).le hrs.le N
    have hgR := hg_pos R hR
    calc g r ≤ g R := h1
      _ = g R * Real.exp (N * σ') * Real.exp (-(N * σ')) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ g R * Real.exp (N * σ') * r ^ N :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ max 1 (g R * Real.exp (N * σ')) * r ^ N :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hr0.le N)

/-! ### Integrability on half-balls -/

theorem halfBall_subset_closedHalfBall {r R : ℝ} (hr : r < R) :
    {x : Space n | ‖x‖ ≤ r ∧ 0 ≤ vcoord x} ⊆ closedHalfBall n R :=
  fun _ hx => ⟨lt_of_le_of_lt hx.1 hr, hx.2⟩

/-- Continuous functions up to the flat boundary are integrable on smaller half-balls. -/
theorem integrableOn_halfBall_of_continuousOn {f : Space n → ℝ} {r R : ℝ} (hr : r < R)
    (hf : ContinuousOn f (closedHalfBall n R)) : IntegrableOn f (halfBall n r) := by
  have hK : IsCompact {x : Space n | ‖x‖ ≤ r ∧ 0 ≤ vcoord x} := by
    have e : {x : Space n | ‖x‖ ≤ r ∧ 0 ≤ vcoord x}
        = Metric.closedBall 0 r ∩ {x | 0 ≤ vcoord x} := by
      ext x
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [e]
    exact (isCompact_closedBall 0 r).inter_right
      (isClosed_le continuous_const F1.continuous_vcoord)
  have h1 : IntegrableOn f {x : Space n | ‖x‖ ≤ r ∧ 0 ≤ vcoord x} :=
    (hf.mono (halfBall_subset_closedHalfBall hr)).integrableOn_compact hK
  exact h1.mono_set fun x hx => ⟨hx.1.le, hx.2.le⟩

/-! ### Half-space helpers -/

theorem isOpen_halfBall (R : ℝ) : IsOpen (halfBall n R) := by
  have e : halfBall n R = Metric.ball (0 : Space n) R ∩ {x | 0 < vcoord x} := by
    ext x
    simp [halfBall, Metric.mem_ball, dist_zero_right]
  rw [e]
  exact Metric.isOpen_ball.inter (isOpen_lt continuous_const F1.continuous_vcoord)

theorem hasCompactSupport_of_norm_ge {E : Type*} [NormedAddCommGroup E] {F : Space n → E}
    {ρ₀ : ℝ} (hz : ∀ x, ρ₀ ≤ ‖x‖ → F x = 0) : HasCompactSupport F := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space n) ρ₀) fun x hx => hz x ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  exact hx.le

theorem eventuallyEq_zero_of_norm_ge {E : Type*} [Zero E] {F : Space n → E} {ρ₀ : ℝ}
    (hz : ∀ x, ρ₀ ≤ ‖x‖ → F x = 0) {x : Space n} (hx : ρ₀ < ‖x‖) :
    F =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact hz y (le_of_lt hy)

/-- A field continuous up to the flat boundary of `B⁺_R` and vanishing for `‖x‖ ≥ ρ₀ < R` is
continuous on the closed half-space. -/
theorem continuousOn_halfSpace_of_closedHalfBall {E : Type*} [TopologicalSpace E] [Zero E]
    {F : Space n → E} {ρ₀ R : ℝ} (hρ₀ : ρ₀ < R) (hF : ContinuousOn F (closedHalfBall n R))
    (hz : ∀ x, ρ₀ ≤ ‖x‖ → F x = 0) : ContinuousOn F {x | 0 ≤ vcoord x} := by
  intro x hx
  by_cases hxR : ‖x‖ < R
  · have hmem : closedHalfBall n R ∈ 𝓝[{x | 0 ≤ vcoord x}] x := by
      have hsub : {x : Space n | 0 ≤ vcoord x} ∩ Metric.ball (0 : Space n) R
          ⊆ closedHalfBall n R := fun y hy =>
        ⟨by simpa [Metric.mem_ball, dist_zero_right] using hy.2, hy.1⟩
      apply Filter.mem_of_superset _ hsub
      exact inter_mem_nhdsWithin _
        (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hxR))
    exact (hF x ⟨hxR, hx⟩).mono_of_mem_nhdsWithin hmem
  · push Not at hxR
    have hev : F =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show ρ₀ < ‖x‖ by linarith)] with y hy
      exact hz y hy.le
    exact (continuousAt_const.congr hev.symm).continuousWithinAt

/-- A function continuous up to the flat boundary of `B⁺_R` and vanishing for `‖x‖ ≥ ρ₀ < R`
is integrable on the open half-space. -/
theorem integrableOn_halfSpace_of_closedHalfBall {f : Space n → ℝ} {ρ₀ R : ℝ} (hρ₀ : ρ₀ < R)
    (hf : ContinuousOn f (closedHalfBall n R)) (hz : ∀ x, ρ₀ ≤ ‖x‖ → f x = 0) :
    IntegrableOn f {x | 0 < vcoord x} := by
  have hK : IsCompact {x : Space n | ‖x‖ ≤ ρ₀ ∧ 0 ≤ vcoord x} := by
    have e : {x : Space n | ‖x‖ ≤ ρ₀ ∧ 0 ≤ vcoord x}
        = Metric.closedBall 0 ρ₀ ∩ {x | 0 ≤ vcoord x} := by
      ext x
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [e]
    exact (isCompact_closedBall 0 ρ₀).inter_right
      (isClosed_le continuous_const F1.continuous_vcoord)
  have h1 : IntegrableOn f {x : Space n | ‖x‖ ≤ ρ₀ ∧ 0 ≤ vcoord x} :=
    (hf.mono (halfBall_subset_closedHalfBall hρ₀)).integrableOn_compact hK
  refine h1.of_forall_sdiff_eq_zero (F1.measurableSet_halfSpace 0) fun x hx => hz x ?_
  by_contra h
  push Not at h
  exact hx.2 ⟨h.le, le_of_lt hx.1⟩

/-! ### Smooth cutoffs -/

theorem smoothTransition_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases h0 : t < 0
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h0] with s hs
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
    rw [heq.deriv_eq, deriv_const, abs_zero]
    exact le_max_right _ _
  by_cases h1 : 1 < t
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h1] with s hs
      exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
    rw [heq.deriv_eq, deriv_const, abs_zero]
    exact le_max_right _ _
  push Not at h0 h1
  have := hC t ⟨h0, h1⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- `Θ(t) = 1 - S((t - 1) / 2)`: equal to `1` for `t ≤ 1` and to `0` for `t ≥ 3`. -/
noncomputable def thetaC (t : ℝ) : ℝ := 1 - Real.smoothTransition ((t - 1) / 2)

theorem thetaC_contDiff : ContDiff ℝ ∞ thetaC := by
  unfold thetaC
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const 2))

theorem thetaC_eq_one {t : ℝ} (ht : t ≤ 1) : thetaC t = 1 := by
  unfold thetaC
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem thetaC_eq_zero {t : ℝ} (ht : 3 ≤ t) : thetaC t = 0 := by
  unfold thetaC
  rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem thetaC_nonneg (t : ℝ) : 0 ≤ thetaC t := by
  unfold thetaC
  linarith [Real.smoothTransition.le_one ((t - 1) / 2)]

theorem thetaC_le_one (t : ℝ) : thetaC t ≤ 1 := by
  unfold thetaC
  linarith [Real.smoothTransition.nonneg ((t - 1) / 2)]

theorem deriv_thetaC_eq_zero {t : ℝ} (ht : 3 < t) : deriv thetaC t = 0 := by
  have heq : thetaC =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact thetaC_eq_zero (le_of_lt hs)
  rw [heq.deriv_eq, deriv_const]

theorem deriv_thetaC_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv thetaC t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := smoothTransition_deriv_bound
  refine ⟨C / 2, by positivity, fun t => ?_⟩
  have hd : HasDerivAt thetaC (-(deriv Real.smoothTransition ((t - 1) / 2) * (1 / 2))) t := by
    have h1 : HasDerivAt (fun t : ℝ => (t - 1) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).sub_const 1).div_const 2
    have h2 := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
      ((t - 1) / 2)).hasDerivAt.comp t h1
    exact (h2.const_sub 1)
  rw [hd.deriv, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := hC ((t - 1) / 2)
  linarith

/-- The cutoff `ζ_r(x) = Θ(‖x‖² / r²)`: `1` on `B_r`, `0` outside `B_{2r}`. -/
noncomputable def zetaC (r : ℝ) (x : Space n) : ℝ := thetaC (‖x‖ ^ 2 / r ^ 2)

theorem zetaC_contDiff (r : ℝ) : ContDiff ℝ ∞ (zetaC (n := n) r) := by
  unfold zetaC
  exact thetaC_contDiff.comp ((contDiff_norm_sq ℝ).div_const _)

theorem zetaC_eq_one {r : ℝ} (hr : 0 < r) {x : Space n} (hx : ‖x‖ ≤ r) : zetaC r x = 1 := by
  unfold zetaC
  apply thetaC_eq_one
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

theorem zetaC_eq_zero {r : ℝ} (hr : 0 < r) {x : Space n} (hx : 2 * r ≤ ‖x‖) : zetaC r x = 0 := by
  unfold zetaC
  apply thetaC_eq_zero
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem zetaC_nonneg (r : ℝ) (x : Space n) : 0 ≤ zetaC r x := thetaC_nonneg _

theorem zetaC_le_one (r : ℝ) (x : Space n) : zetaC r x ≤ 1 := thetaC_le_one _

theorem hasFDerivAt_zetaC (r : ℝ) (x : Space n) :
    HasFDerivAt (zetaC r) ((deriv thetaC (‖x‖ ^ 2 / r ^ 2) * (2 / r ^ 2)) • innerSL ℝ x) x := by
  have hd : DifferentiableAt ℝ thetaC (‖x‖ ^ 2 / r ^ 2) :=
    (thetaC_contDiff.differentiable (by simp)) _
  have h1 : HasFDerivAt (fun y : Space n => ‖y‖ ^ 2 / r ^ 2) ((1 / r ^ 2) • (2 • innerSL ℝ x)) x :=
    by simpa [div_eq_mul_inv, mul_comm] using
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const ((r ^ 2)⁻¹)
  have h := hd.hasDerivAt.comp_hasFDerivAt x h1
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem gradient_zetaC (r : ℝ) (x : Space n) :
    gradient (zetaC r) x = (deriv thetaC (‖x‖ ^ 2 / r ^ 2) * (2 / r ^ 2)) • x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, (hasFDerivAt_zetaC r x).fderiv]
  simp [real_inner_smul_left]

theorem gradient_zetaC_eq_zero {r : ℝ} (hr : 0 < r) {x : Space n} (hx : 2 * r ≤ ‖x‖) :
    gradient (zetaC r) x = 0 := by
  rw [gradient_zetaC, deriv_thetaC_eq_zero (by rw [lt_div_iff₀ (by positivity)]; nlinarith),
    zero_mul, zero_smul]

theorem continuous_gradient_zetaC (r : ℝ) : Continuous (gradient (zetaC (n := n) r)) := by
  have h : gradient (zetaC (n := n) r)
      = fun x => (deriv thetaC (‖x‖ ^ 2 / r ^ 2) * (2 / r ^ 2)) • x := by
    funext x; exact gradient_zetaC r x
  rw [h]
  exact (((thetaC_contDiff.continuous_deriv (by simp)).comp
    ((continuous_norm.pow 2).div_const _)).mul continuous_const).smul continuous_id

/-- `|∇ζ_r| ≤ C / r`. -/
theorem norm_gradient_zetaC_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ x : Space n,
    ‖gradient (zetaC r) x‖ ≤ C / r := by
  obtain ⟨C, hC0, hC⟩ := deriv_thetaC_bound
  refine ⟨4 * C, by positivity, fun r hr x => ?_⟩
  rw [gradient_zetaC, norm_smul, Real.norm_eq_abs]
  by_cases hx : 2 * r < ‖x‖
  · rw [deriv_thetaC_eq_zero (by rw [lt_div_iff₀ (by positivity)]; nlinarith)]
    simp only [zero_mul, abs_zero]
    positivity
  · push Not at hx
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 / r ^ 2 by positivity)]
    have h1 := hC (‖x‖ ^ 2 / r ^ 2)
    calc |deriv thetaC (‖x‖ ^ 2 / r ^ 2)| * (2 / r ^ 2) * ‖x‖
        ≤ C * (2 / r ^ 2) * (2 * r) := by gcongr
      _ = 4 * C / r := by field_simp; ring

/-! ### Young-type inequalities -/

theorem young_two_mul {lam a b : ℝ} (hlam : 0 < lam) :
    2 * a * b ≤ lam / 4 * a ^ 2 + 4 / lam * b ^ 2 := by
  have h := sq_nonneg (lam / 4 * a - b)
  have hl : 0 < lam / 4 := by positivity
  have e : (lam / 4 * a ^ 2 + 4 / lam * b ^ 2) * (lam / 4) = (lam / 4 * a) ^ 2 + b ^ 2 := by
    field_simp
  have h2 : 2 * a * b * (lam / 4) ≤ (lam / 4 * a ^ 2 + 4 / lam * b ^ 2) * (lam / 4) := by
    rw [e]; nlinarith
  exact le_of_mul_le_mul_right h2 hl

theorem young_mul {lam a c : ℝ} (hlam : 0 < lam) :
    a * c ≤ lam / 4 * a ^ 2 + 1 / lam * c ^ 2 := by
  have h := sq_nonneg (lam / 2 * a - c)
  have hl : 0 < lam / 4 := by positivity
  have e : (lam / 4 * a ^ 2 + 1 / lam * c ^ 2) * (lam / 4) = (lam / 4 * a) ^ 2 + c ^ 2 / 4 := by
    field_simp
  have h2 : a * c * (lam / 4) ≤ (lam / 4 * a ^ 2 + 1 / lam * c ^ 2) * (lam / 4) := by
    rw [e]; nlinarith
  exact le_of_mul_le_mul_right h2 hl

/-- The pointwise inequality behind Caccioppoli's estimate. -/
theorem cacc_pointwise_real {lam K z v D G I₂ Ib c : ℝ} (hlam : 0 < lam) (_hK : 0 ≤ K)
    (_hD : 0 ≤ D) (_hG : 0 ≤ G) (hI₂ : |I₂| ≤ G * (K * D)) (hIb : |Ib| ≤ K * D) (hc : |c| ≤ K) :
    -(2 * z * v * I₂) + z ^ 2 * v * (Ib + c * v)
      ≤ lam / 2 * (z ^ 2 * D ^ 2)
        + (4 * K ^ 2 / lam * (v ^ 2 * G ^ 2) + (K ^ 2 / lam + K) * (z ^ 2 * v ^ 2)) := by
  have hzs : |z| ^ 2 = z ^ 2 := sq_abs z
  have hvs : |v| ^ 2 = v ^ 2 := sq_abs v
  have e2 : -(2 * z * v * I₂) ≤ 2 * (|z| * D) * (K * |v| * G) := by
    have h1 : -(2 * z * v * I₂) ≤ |2 * z * v * I₂| := neg_le_abs _
    have h2 : |2 * z * v * I₂| = 2 * |z| * |v| * |I₂| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
    have h3 : 2 * |z| * |v| * |I₂| ≤ 2 * |z| * |v| * (G * (K * D)) :=
      mul_le_mul_of_nonneg_left hI₂ (by positivity)
    have h4 : 2 * |z| * |v| * (G * (K * D)) = 2 * (|z| * D) * (K * |v| * G) := by ring
    linarith
  have e3 : z ^ 2 * v * (Ib + c * v) ≤ (|z| * D) * (K * |z| * |v|) + K * (z ^ 2 * v ^ 2) := by
    have h1 : z ^ 2 * v * (Ib + c * v) ≤ |z ^ 2 * v * (Ib + c * v)| := le_abs_self _
    have h2 : |z ^ 2 * v * (Ib + c * v)| = z ^ 2 * |v| * |Ib + c * v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg z)]
    have h3 : |Ib + c * v| ≤ K * D + K * |v| := by
      refine (abs_add_le _ _).trans (add_le_add hIb ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    have h4 : z ^ 2 * |v| * |Ib + c * v| ≤ z ^ 2 * |v| * (K * D + K * |v|) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : z ^ 2 * |v| * (K * D + K * |v|)
        = (|z| * D) * (K * |z| * |v|) + K * (z ^ 2 * |v| ^ 2) := by
      rw [← hzs]; ring
    rw [hvs] at h5
    linarith
  have y1 := young_two_mul (a := |z| * D) (b := K * |v| * G) hlam
  have y2 := young_mul (a := |z| * D) (c := K * |z| * |v|) hlam
  have ea : (|z| * D) ^ 2 = z ^ 2 * D ^ 2 := by rw [mul_pow, hzs]
  have eb : (K * |v| * G) ^ 2 = K ^ 2 * (v ^ 2 * G ^ 2) := by rw [mul_pow, mul_pow, hvs]; ring
  have ec : (K * |z| * |v|) ^ 2 = K ^ 2 * (z ^ 2 * v ^ 2) := by
    rw [mul_pow, mul_pow, hzs, hvs]; ring
  rw [ea, eb] at y1
  rw [ea, ec] at y2
  have f1 : 4 / lam * (K ^ 2 * (v ^ 2 * G ^ 2)) = 4 * K ^ 2 / lam * (v ^ 2 * G ^ 2) := by ring
  have f2 : 1 / lam * (K ^ 2 * (z ^ 2 * v ^ 2)) = K ^ 2 / lam * (z ^ 2 * v ^ 2) := by ring
  linarith

/-! ### Caccioppoli's inequality up to the flat boundary -/

/-- The Caccioppoli field `Φ = ζ_r² v A Dv`. -/
noncomputable def caccField (S : HalfBallSolution n) (r : ℝ) (x : Space n) : Space n :=
  (zetaC r x ^ 2 * S.v x) • S.A x (S.Dv x)

/-- `ζ² ⟪Dv, A Dv⟫`. -/
noncomputable def caccH₁ (S : HalfBallSolution n) (r : ℝ) (x : Space n) : ℝ :=
  zetaC r x ^ 2 * ⟪S.Dv x, S.A x (S.Dv x)⟫_ℝ

/-- `2 ζ v ⟪∇ζ, A Dv⟫`. -/
noncomputable def caccH₂ (S : HalfBallSolution n) (r : ℝ) (x : Space n) : ℝ :=
  2 * zetaC r x * S.v x * ⟪gradient (zetaC r) x, S.A x (S.Dv x)⟫_ℝ

/-- `ζ² v (⟪B, Dv⟫ + C v)`. -/
noncomputable def caccH₃ (S : HalfBallSolution n) (r : ℝ) (x : Space n) : ℝ :=
  zetaC r x ^ 2 * S.v x * (⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x)

theorem caccField_eq_zero (S : HalfBallSolution n) {r : ℝ} (hr : 0 < r) :
    ∀ x : Space n, 2 * r ≤ ‖x‖ → caccField S r x = 0 := fun x hx => by
  simp [caccField, zetaC_eq_zero hr hx]

theorem caccH_eq_zero (S : HalfBallSolution n) {r : ℝ} (hr : 0 < r) (x : Space n)
    (hx : 2 * r ≤ ‖x‖) : caccH₁ S r x = 0 ∧ caccH₂ S r x = 0 ∧ caccH₃ S r x = 0 := by
  simp [caccH₁, caccH₂, caccH₃, zetaC_eq_zero hr hx]

theorem caccH_continuousOn (S : HalfBallSolution n) (r : ℝ) :
    ContinuousOn (caccH₁ S r) (closedHalfBall n S.R) ∧
      ContinuousOn (caccH₂ S r) (closedHalfBall n S.R) ∧
      ContinuousOn (caccH₃ S r) (closedHalfBall n S.R) := by
  have hvc := S.v_continuousOn
  have hDvc := S.Dv_continuousOn
  have hADv : ContinuousOn (fun x => S.A x (S.Dv x)) (closedHalfBall n S.R) :=
    S.coeffs.contDiff_A.continuous.continuousOn.clm_apply hDvc
  have hζ : Continuous (zetaC (n := n) r) := (zetaC_contDiff r).continuous
  have hgζ : Continuous (gradient (zetaC (n := n) r)) := continuous_gradient_zetaC r
  refine ⟨(hζ.continuousOn.pow 2).mul (hDvc.inner hADv), ?_, ?_⟩
  · exact ((continuousOn_const.mul hζ.continuousOn).mul hvc).mul (hgζ.continuousOn.inner hADv)
  · exact ((hζ.continuousOn.pow 2).mul hvc).mul
      ((S.coeffs.cont_B.continuousOn.inner hDvc).add (S.coeffs.cont_C.continuousOn.mul hvc))

theorem caccH_integrableOn (S : HalfBallSolution n) {r : ℝ} (hr : 0 < r) (h2r : 2 * r < S.R) :
    IntegrableOn (caccH₁ S r) {x | 0 < vcoord x} ∧
      IntegrableOn (caccH₂ S r) {x | 0 < vcoord x} ∧
      IntegrableOn (caccH₃ S r) {x | 0 < vcoord x} := by
  obtain ⟨h1, h2, h3⟩ := caccH_continuousOn S r
  exact ⟨integrableOn_halfSpace_of_closedHalfBall h2r h1 fun x hx => (caccH_eq_zero S hr x hx).1,
    integrableOn_halfSpace_of_closedHalfBall h2r h2 fun x hx => (caccH_eq_zero S hr x hx).2.1,
    integrableOn_halfSpace_of_closedHalfBall h2r h3 fun x hx => (caccH_eq_zero S hr x hx).2.2⟩

/-- The divergence of the Caccioppoli field, computed with the equation. -/
theorem divergence_caccField (S : HalfBallSolution n) {r : ℝ} (hr : 0 < r) (h2r : 2 * r < S.R)
    (x : Space n) (hx : 0 < vcoord x) :
    divergence (caccField S r) x = caccH₁ S r x + caccH₂ S r x - caccH₃ S r x := by
  have hζc : ContDiff ℝ ∞ (zetaC (n := n) r) := zetaC_contDiff r
  by_cases hxR : ‖x‖ < S.R
  · have hxU : x ∈ halfBall n S.R := ⟨hxR, hx⟩
    have hUn : halfBall n S.R ∈ 𝓝 x := (isOpen_halfBall S.R).mem_nhds hxU
    have hv2 : ContDiffAt ℝ 2 S.v x := S.v_contDiffOn.contDiffAt hUn
    have hgv : gradient S.v =ᶠ[𝓝 x] S.Dv := by
      filter_upwards [hUn] with y hy using S.gradient_eq y hy
    have hev : caccField S r =ᶠ[𝓝 x]
        fun y => (zetaC r y ^ 2 * S.v y) • S.A y (gradient S.v y) := by
      filter_upwards [hgv] with y hy
      simp only [caccField, hy]
    have hvd : DifferentiableAt ℝ S.v x := hv2.differentiableAt (by simp)
    have hζd : DifferentiableAt ℝ (zetaC (n := n) r) x := (hζc.differentiable (by simp)) x
    have hfd : DifferentiableAt ℝ (fun y => zetaC r y ^ 2 * S.v y) x := (hζd.pow 2).mul hvd
    have hWd : DifferentiableAt ℝ (fun y => S.A y (gradient S.v y)) x :=
      ((S.coeffs.contDiff_A.differentiable (by simp)) x).clm_apply
        (F2.differentiableAt_gradient hv2)
    rw [F2.divergence_congr hev, F2.divergence_smul hfd hWd]
    have heqn := S.eqn x hxU
    simp only [ellOp] at heqn
    have hfder : fderiv ℝ (fun y => zetaC r y ^ 2 * S.v y) x
        = zetaC r x ^ 2 • fderiv ℝ S.v x + S.v x • ((2 * zetaC r x) • fderiv ℝ (zetaC r) x) := by
      have h1 : HasFDerivAt (fun y => zetaC (n := n) r y ^ 2)
          ((2 * zetaC r x) • fderiv ℝ (zetaC r) x) x := by
        have := (hζd.hasFDerivAt.pow 2)
        simpa [pow_one, mul_comm] using this
      exact (h1.mul hvd.hasFDerivAt).fderiv
    rw [hfder]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ← inner_gradient_left]
    have hg : gradient S.v x = S.Dv x := S.gradient_eq x hxU
    rw [hg] at heqn ⊢
    simp only [caccH₁, caccH₂, caccH₃]
    have hdivW : divergence (fun y => S.A y (gradient S.v y)) x
        = -(⟪S.B x, S.Dv x⟫_ℝ + S.C x * S.v x) := by linarith
    rw [hdivW]
    ring
  · push Not at hxR
    have hev : caccField S r =ᶠ[𝓝 x] fun _ => 0 :=
      eventuallyEq_zero_of_norm_ge (caccField_eq_zero S hr) (by linarith)
    rw [F2.divergence_congr hev]
    have h0 : divergence (fun _ : Space n => (0 : Space n)) x = 0 := by
      simp [divergence]
    obtain ⟨e1, e2, e3⟩ := caccH_eq_zero S hr x (by linarith)
    rw [h0, e1, e2, e3]
    ring

theorem contDiffAt_caccField (S : HalfBallSolution n) {r : ℝ} (hr : 0 < r) (h2r : 2 * r < S.R)
    (x : Space n) (hx : 0 < vcoord x) : ContDiffAt ℝ 1 (caccField S r) x := by
  have hζc : ContDiff ℝ ∞ (zetaC (n := n) r) := zetaC_contDiff r
  by_cases hxR : ‖x‖ < S.R
  · have hxU : x ∈ halfBall n S.R := ⟨hxR, hx⟩
    have hUn : halfBall n S.R ∈ 𝓝 x := (isOpen_halfBall S.R).mem_nhds hxU
    have hv2 : ContDiffAt ℝ 2 S.v x := S.v_contDiffOn.contDiffAt hUn
    have hgv : gradient S.v =ᶠ[𝓝 x] S.Dv := by
      filter_upwards [hUn] with y hy using S.gradient_eq y hy
    have hev : caccField S r =ᶠ[𝓝 x]
        fun y => (zetaC r y ^ 2 * S.v y) • S.A y (gradient S.v y) := by
      filter_upwards [hgv] with y hy
      simp only [caccField, hy]
    have hζ1 : ContDiffAt ℝ 1 (zetaC (n := n) r) x := (hζc.of_le (by simp)).contDiffAt
    have hv1 : ContDiffAt ℝ 1 S.v x := hv2.of_le (by norm_num)
    have hA1 : ContDiffAt ℝ 1 S.A x := (S.coeffs.contDiff_A.of_le (by norm_num)).contDiffAt
    have hg1 : ContDiffAt ℝ 1 (gradient S.v) x := F2.contDiffAt_gradient hv2 (by norm_num)
    exact (((hζ1.pow 2).mul hv1).smul (hA1.clm_apply hg1)).congr_of_eventuallyEq hev
  · push Not at hxR
    have hev : caccField S r =ᶠ[𝓝 x] fun _ => 0 :=
      eventuallyEq_zero_of_norm_ge (caccField_eq_zero S hr) (by linarith)
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The integrated identity behind Caccioppoli's inequality. -/
theorem cacc_identity (S : HalfBallSolution n) {r : ℝ} (hr : 0 < r) (h2r : 2 * r < S.R) :
    (∫ x in {x : Space n | 0 < vcoord x}, caccH₁ S r x)
        + (∫ x in {x : Space n | 0 < vcoord x}, caccH₂ S r x)
        - (∫ x in {x : Space n | 0 < vcoord x}, caccH₃ S r x)
      = -∫ y : EuclideanSpace ℝ (Fin n), ⟪caccField S r (lift y 0), ed n⟫_ℝ := by
  obtain ⟨hH₁i, hH₂i, hH₃i⟩ := caccH_integrableOn S hr h2r
  have hvc := S.v_continuousOn
  have hADv : ContinuousOn (fun x => S.A x (S.Dv x)) (closedHalfBall n S.R) :=
    S.coeffs.contDiff_A.continuous.continuousOn.clm_apply S.Dv_continuousOn
  have hζ : Continuous (zetaC (n := n) r) := (zetaC_contDiff r).continuous
  have hΦcont : ContinuousOn (caccField S r) {x | 0 ≤ vcoord x} :=
    continuousOn_halfSpace_of_closedHalfBall h2r
      (((hζ.continuousOn.pow 2).mul hvc).smul hADv) (caccField_eq_zero S hr)
  have hΦsupp : HasCompactSupport (caccField S r) :=
    hasCompactSupport_of_norm_ge (caccField_eq_zero S hr)
  have h12 : IntegrableOn (fun x => caccH₁ S r x + caccH₂ S r x) {x | 0 < vcoord x} :=
    hH₁i.add hH₂i
  have hHi : IntegrableOn (fun x => caccH₁ S r x + caccH₂ S r x - caccH₃ S r x)
      {x | 0 < vcoord x} := h12.sub hH₃i
  have hdivi : IntegrableOn (divergence (caccField S r)) {x | 0 < vcoord x} :=
    hHi.congr_fun (fun x hx => (divergence_caccField S hr h2r x hx).symm)
      (F1.measurableSet_halfSpace 0)
  have hIBP := integral_divergence_halfSpace_of_continuousOn (caccField S r)
    (contDiffAt_caccField S hr h2r) hΦcont hΦsupp hdivi
  rw [setIntegral_congr_fun (F1.measurableSet_halfSpace 0) (divergence_caccField S hr h2r),
    integral_sub h12 hH₃i, integral_add hH₁i hH₂i] at hIBP
  exact hIBP

theorem norm_lift_zero (y : EuclideanSpace ℝ (Fin n)) : ‖lift y 0‖ = ‖y‖ := by
  have h := norm_lift_sq y 0
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The boundary term of Caccioppoli's identity contains the conormal datum. -/
theorem cacc_boundary (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ r : ℝ, 0 < r → 2 * r < S.R →
      -(∫ y : EuclideanSpace ℝ (Fin n), ⟪caccField S r (lift y 0), ed n⟫_ℝ)
        ≤ Cb * g (2 * r) * r ^ n := by
  obtain ⟨C0, hC0⟩ := S.dirichlet_flat 0
  obtain ⟨C1, hC1⟩ := S.dirichlet_flat 1
  set V₁ : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hV₁
  have hV₁0 : 0 ≤ V₁ := ENNReal.toReal_nonneg
  refine ⟨|C0| * V₁ * 2 ^ n, by positivity, fun r hr h2r => ?_⟩
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n), ‖⟪caccField S r (lift y 0), ed n⟫_ℝ‖
      ≤ (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r)).indicator
          (fun _ => |C0| * g (2 * r)) y := by
    intro y
    by_cases hy : ‖y‖ < 2 * r
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_ball, dist_zero_right] using hy)]
      have hxn : ‖lift y 0‖ < 2 * r := by rw [norm_lift_zero]; exact hy
      have hxflat : lift y 0 ∈ flatPiece n S.R := ⟨by linarith, by rw [vcoord_lift]⟩
      have hinner : ⟪caccField S r (lift y 0), ed n⟫_ℝ
          = zetaC r (lift y 0) ^ 2 * S.v (lift y 0) *
              ⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ := by
        simp only [caccField, real_inner_smul_left]
      rw [hinner, Real.norm_eq_abs]
      by_cases hx0 : lift y 0 = 0
      · have hv0 : S.v (lift y 0) = 0 := by
          have := hC1 _ hxflat
          rw [hx0, norm_zero, pow_one, mul_zero] at this
          rw [hx0]
          exact abs_nonpos_iff.1 this
        rw [hv0]
        simp only [mul_zero, zero_mul, abs_zero]
        exact mul_nonneg (abs_nonneg _) (hg_pos _ (by linarith)).le
      · have hxpos : 0 < ‖lift y 0‖ := norm_pos_iff.2 hx0
        have hvb : |S.v (lift y 0)| ≤ |C0| := by
          have := hC0 _ hxflat
          rw [pow_zero, mul_one] at this
          exact this.trans (le_abs_self _)
        have hnb : |⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ| ≤ g (2 * r) :=
          (hneu _ hxflat hx0).trans
            (hg_mono (Set.mem_Ioi.2 hxpos) (Set.mem_Ioi.2 (by linarith)) hxn.le)
        have hζb : zetaC r (lift y 0) ^ 2 ≤ 1 := by
          have h0 := zetaC_nonneg r (lift y 0)
          have h1 := zetaC_le_one r (lift y 0)
          nlinarith
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc zetaC r (lift y 0) ^ 2 * |S.v (lift y 0)| *
              |⟪S.A (lift y 0) (S.Dv (lift y 0)), ed n⟫_ℝ|
            ≤ 1 * |C0| * g (2 * r) := by gcongr
          _ = |C0| * g (2 * r) := by ring
    · rw [Set.indicator_of_notMem (by simpa [Metric.mem_ball, dist_zero_right] using hy)]
      have hx : 2 * r ≤ ‖lift y 0‖ := by rw [norm_lift_zero]; linarith
      rw [caccField_eq_zero S hr _ hx, inner_zero_left, norm_zero]
  have hint_ind : Integrable ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r)).indicator
      (fun _ => |C0| * g (2 * r))) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator
      Metric.isOpen_ball.measurableSet
  have h1 := norm_integral_le_of_norm_le hint_ind (Eventually.of_forall hpt)
  rw [integral_indicator_const _ Metric.isOpen_ball.measurableSet] at h1
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))).real
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r)) = (2 * r) ^ n * V₁ := by
    rw [Measure.real, Measure.addHaar_ball_of_pos _ _ (by linarith : (0 : ℝ) < 2 * r),
      finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [hvol, smul_eq_mul] at h1
  set bd := ∫ y : EuclideanSpace ℝ (Fin n), ⟪caccField S r (lift y 0), ed n⟫_ℝ
  have h2 : -bd ≤ ‖bd‖ := by rw [Real.norm_eq_abs]; exact neg_le_abs bd
  calc -bd ≤ (2 * r) ^ n * V₁ * (|C0| * g (2 * r)) := h2.trans h1
    _ = |C0| * V₁ * 2 ^ n * g (2 * r) * r ^ n := by rw [mul_pow]; ring

/-- The pointwise bound of the zeroth order terms. -/
theorem cacc_Q_real {K lam Cθ r v G z : ℝ} (hK : 0 ≤ K) (hlam : 0 < lam) (hr : 0 < r)
    (hr1 : r ≤ 1) (hG0 : 0 ≤ G) (hG : G ≤ Cθ / r) (hz : z ^ 2 ≤ 1) :
    4 * K ^ 2 / lam * (v ^ 2 * G ^ 2) + (K ^ 2 / lam + K) * (z ^ 2 * v ^ 2)
      ≤ (4 * K ^ 2 / lam * Cθ ^ 2 + (K ^ 2 / lam + K)) / r ^ 2 * v ^ 2 := by
  have hr2pos : 0 < r ^ 2 := by positivity
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
  have hG2 : G ^ 2 ≤ Cθ ^ 2 / r ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ hG0 hG 2
  have hone : 1 ≤ 1 / r ^ 2 := by rw [le_div_iff₀ hr2pos]; linarith
  have hv := sq_nonneg v
  have t1 : 4 * K ^ 2 / lam * (v ^ 2 * G ^ 2) ≤ 4 * K ^ 2 / lam * (v ^ 2 * (Cθ ^ 2 / r ^ 2)) := by
    gcongr
  have t2 : (K ^ 2 / lam + K) * (z ^ 2 * v ^ 2) ≤ (K ^ 2 / lam + K) * (v ^ 2 * (1 / r ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have t3 : 4 * K ^ 2 / lam * (v ^ 2 * (Cθ ^ 2 / r ^ 2)) + (K ^ 2 / lam + K) * (v ^ 2 * (1 / r ^ 2))
      = (4 * K ^ 2 / lam * Cθ ^ 2 + (K ^ 2 / lam + K)) / r ^ 2 * v ^ 2 := by
    field_simp
  linarith

/-- The final algebra of Caccioppoli's inequality. -/
theorem cacc_final_real {lam X W Y C₁ Cb gr r : ℝ} (n : ℕ) (hlam : 0 < lam) (hr : 0 < r)
    (hWX : W ≤ X) (hY : 0 ≤ Y) (hgr : 0 ≤ gr) (hC₁ : 0 ≤ C₁) (hCb : 0 ≤ Cb)
    (h : lam / 2 * X ≤ Cb * gr * r ^ n + C₁ / r ^ 2 * Y) :
    r ^ 2 * W ≤ (2 / lam * (C₁ + Cb) + 1) * (Y + r ^ (n + 2) * gr) := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hX : X ≤ 2 / lam * (Cb * gr * r ^ n + C₁ / r ^ 2 * Y) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    linarith
  have e : r ^ 2 * (2 / lam * (Cb * gr * r ^ n + C₁ / r ^ 2 * Y))
      = 2 / lam * (Cb * (r ^ (n + 2) * gr) + C₁ * Y) := by
    rw [pow_add]; field_simp
  have h1 : 0 ≤ r ^ (n + 2) * gr := by positivity
  have h2 : 0 ≤ 2 / lam := by positivity
  calc r ^ 2 * W ≤ r ^ 2 * X := mul_le_mul_of_nonneg_left hWX hr2.le
    _ ≤ r ^ 2 * (2 / lam * (Cb * gr * r ^ n + C₁ / r ^ 2 * Y)) :=
        mul_le_mul_of_nonneg_left hX hr2.le
    _ = 2 / lam * (Cb * (r ^ (n + 2) * gr) + C₁ * Y) := e
    _ ≤ (2 / lam * (C₁ + Cb) + 1) * (Y + r ^ (n + 2) * gr) := by
        nlinarith [mul_nonneg h2 (mul_nonneg hCb hY), mul_nonneg h2 (mul_nonneg hC₁ h1)]

/-- **Caccioppoli's inequality up to the flat boundary.** The boundary term contains the
conormal datum, which is bounded by `g(2r)` (and `v(0) = 0`). -/
theorem caccioppoli (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0)) :
    ∃ Cc rc : ℝ, 0 < Cc ∧ 0 < rc ∧ ∀ r ∈ Set.Ioc 0 rc,
      r ^ 2 * ∫ x in halfBall n r, ‖S.Dv x‖ ^ 2
        ≤ Cc * ((∫ x in halfBall n (2 * r), S.v x ^ 2) + r ^ (n + 2) * g (2 * r)) := by
  obtain ⟨Cθ, hCθ0, hCθ⟩ := norm_gradient_zetaC_le (n := n)
  obtain ⟨Cb, hCb0, hCb⟩ := cacc_boundary S g hneu hg_pos hg_mono
  have hlam : 0 < S.lam := S.coeffs.lam_pos
  have hK : 0 ≤ S.K := le_trans (norm_nonneg _) (S.coeffs.bound_A 0)
  have hRpos := S.R_pos
  set C₁ : ℝ := 4 * S.K ^ 2 / S.lam * Cθ ^ 2 + (S.K ^ 2 / S.lam + S.K) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨2 / S.lam * (C₁ + Cb) + 1, min (S.R / 4) 1, by positivity,
    lt_min (by linarith) one_pos, fun r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  have hrR : r ≤ S.R / 4 := hr.2.trans (min_le_left _ _)
  have hr1 : r ≤ 1 := hr.2.trans (min_le_right _ _)
  have h2rR : 2 * r < S.R := by linarith
  obtain ⟨hH₁i, hH₂i, hH₃i⟩ := caccH_integrableOn S hr0 h2rR
  have hid := cacc_identity S hr0 h2rR
  have hbd := hCb r hr0 h2rR
  -- the quadratic term
  have hζc : Continuous (zetaC (n := n) r) := (zetaC_contDiff r).continuous
  have hX_i : IntegrableOn (fun x => zetaC r x ^ 2 * ‖S.Dv x‖ ^ 2) {x | 0 < vcoord x} :=
    integrableOn_halfSpace_of_closedHalfBall h2rR
      ((hζc.continuousOn.pow 2).mul (S.Dv_continuousOn.norm.pow 2))
      (fun x hx => by simp [zetaC_eq_zero hr0 hx])
  have hpt1 : ∀ x ∈ {x : Space n | 0 < vcoord x},
      S.lam * (zetaC r x ^ 2 * ‖S.Dv x‖ ^ 2) ≤ caccH₁ S r x := by
    intro x _
    have := S.coeffs.ell x (S.Dv x)
    simp only [caccH₁]
    rw [real_inner_comm]
    nlinarith [sq_nonneg (zetaC r x)]
  have hI1 : S.lam * ∫ x in {x : Space n | 0 < vcoord x}, zetaC r x ^ 2 * ‖S.Dv x‖ ^ 2
      ≤ ∫ x in {x : Space n | 0 < vcoord x}, caccH₁ S r x := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hX_i.const_mul _) hH₁i (F1.measurableSet_halfSpace 0) hpt1
  -- the cross terms
  set Q : Space n → ℝ := fun x =>
    4 * S.K ^ 2 / S.lam * (S.v x ^ 2 * ‖gradient (zetaC r) x‖ ^ 2) + (S.K ^ 2 / S.lam + S.K) *
      (zetaC r x ^ 2 * S.v x ^ 2) with hQ
  have hpt2 : ∀ x ∈ {x : Space n | 0 < vcoord x},
      -caccH₂ S r x + caccH₃ S r x ≤ S.lam / 2 * (zetaC r x ^ 2 * ‖S.Dv x‖ ^ 2) + Q x := by
    intro x _
    have hA : ‖S.A x (S.Dv x)‖ ≤ S.K * ‖S.Dv x‖ :=
      ((S.A x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (S.coeffs.bound_A x)
        (norm_nonneg _))
    have i1 : |⟪gradient (zetaC r) x, S.A x (S.Dv x)⟫_ℝ|
        ≤ ‖gradient (zetaC r) x‖ * (S.K * ‖S.Dv x‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
    have i2 : |⟪S.B x, S.Dv x⟫_ℝ| ≤ S.K * ‖S.Dv x‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (S.coeffs.bound_B x) (norm_nonneg _))
    have key := cacc_pointwise_real (z := zetaC r x) (v := S.v x) hlam hK
      (norm_nonneg (S.Dv x)) (norm_nonneg (gradient (zetaC r) x)) i1 i2 (S.coeffs.bound_C x)
    simpa only [caccH₂, caccH₃, hQ] using key
  have hQc : ContinuousOn Q (closedHalfBall n S.R) :=
    (continuousOn_const.mul ((S.v_continuousOn.pow 2).mul
      ((continuous_gradient_zetaC r).continuousOn.norm.pow 2))).add
      (continuousOn_const.mul ((hζc.continuousOn.pow 2).mul (S.v_continuousOn.pow 2)))
  have hQz : ∀ x : Space n, 2 * r ≤ ‖x‖ → Q x = 0 := fun x hx => by
    simp only [hQ, zetaC_eq_zero hr0 hx, gradient_zetaC_eq_zero hr0 hx, norm_zero]; ring
  have hQi := integrableOn_halfSpace_of_closedHalfBall h2rR hQc hQz
  have hnegH₂ : IntegrableOn (fun x => -caccH₂ S r x) {x | 0 < vcoord x} := hH₂i.neg
  have hXc : IntegrableOn (fun x => S.lam / 2 * (zetaC r x ^ 2 * ‖S.Dv x‖ ^ 2))
      {x | 0 < vcoord x} := hX_i.const_mul _
  have hI2 : ∫ x in {x : Space n | 0 < vcoord x}, (-caccH₂ S r x + caccH₃ S r x)
      ≤ ∫ x in {x : Space n | 0 < vcoord x},
          (S.lam / 2 * (zetaC r x ^ 2 * ‖S.Dv x‖ ^ 2) + Q x) :=
    setIntegral_mono_on (hnegH₂.add hH₃i) (hXc.add hQi) (F1.measurableSet_halfSpace 0) hpt2
  rw [integral_add hnegH₂ hH₃i, integral_neg, integral_add hXc hQi,
    integral_const_mul] at hI2
  -- `∫ Q ≤ C₁ r⁻² ∫_{B⁺_{2r}} v²`
  have hsub : halfBall n (2 * r) ⊆ {x : Space n | 0 < vcoord x} := fun x hx => hx.2
  have hvi : IntegrableOn (fun x => S.v x ^ 2) (halfBall n (2 * r)) :=
    integrableOn_halfBall_of_continuousOn h2rR (S.v_continuousOn.pow 2)
  have hQbd : ∫ x in {x : Space n | 0 < vcoord x}, Q x
      ≤ C₁ / r ^ 2 * ∫ x in halfBall n (2 * r), S.v x ^ 2 := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (F1.measurableSet_halfSpace 0) hsub
      (fun x hx => hQz x (by
        by_contra h
        push Not at h
        exact hx.2 ⟨h, hx.1⟩)), ← integral_const_mul]
    refine setIntegral_mono_on (hQi.mono_set hsub) (hvi.const_mul _)
      (isOpen_halfBall _).measurableSet fun x _ => ?_
    have hζ2 : zetaC r x ^ 2 ≤ 1 := by
      have h0 := zetaC_nonneg r x
      have h1 := zetaC_le_one r x
      nlinarith
    exact cacc_Q_real hK hlam hr0 hr1 (norm_nonneg _) (hCθ r hr0 x) hζ2
  -- `∫_{B⁺_r} |Dv|² ≤ ∫ ζ² |Dv|²`
  have hlow : ∫ x in halfBall n r, ‖S.Dv x‖ ^ 2
      ≤ ∫ x in {x : Space n | 0 < vcoord x}, zetaC r x ^ 2 * ‖S.Dv x‖ ^ 2 := by
    have e : ∫ x in halfBall n r, ‖S.Dv x‖ ^ 2
        = ∫ x in halfBall n r, zetaC r x ^ 2 * ‖S.Dv x‖ ^ 2 := by
      refine setIntegral_congr_fun (isOpen_halfBall _).measurableSet fun x hx => ?_
      simp only [zetaC_eq_one hr0 hx.1.le]; ring
    rw [e]
    refine setIntegral_mono_set hX_i ?_ (Eventually.of_forall fun x hx => hx.2)
    exact (ae_restrict_iff' (F1.measurableSet_halfSpace 0)).2
      (Eventually.of_forall fun x _ => by positivity)
  have hY0 : 0 ≤ ∫ x in halfBall n (2 * r), S.v x ^ 2 :=
    setIntegral_nonneg (isOpen_halfBall _).measurableSet (fun x _ => sq_nonneg _)
  have hg2r : 0 < g (2 * r) := hg_pos _ (by linarith)
  refine cacc_final_real n hlam hr0 hlow hY0 hg2r.le hC₁0 hCb0 ?_
  linarith

/-- Infinite order vanishing of `v` and `∇v` in `L²`, from Lemma R1 and Caccioppoli. -/
theorem grad_infinite_order (S : HalfBallSolution n) (hn : 0 < n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg_flat : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) :
    ∀ M : ℕ, ∃ Cm rm : ℝ, 0 < rm ∧ ∀ r ∈ Set.Ioc 0 rm,
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cm * r ^ M := by
  intro M
  obtain ⟨Cm, hCm⟩ := S.integral_sq_le_pow hn g hneu hg_flat (M + 2)
  obtain ⟨Cc, rc, hCc, hrc, hcacc⟩ := caccioppoli S g hneu hg_pos hg_mono
  obtain ⟨Cg, hCg⟩ := hg_flat (M + 2)
  have hRpos := S.R_pos
  refine ⟨|Cm| + Cc * (|Cm| * 2 ^ (M + 2) + |Cg| * 2 ^ (M + 2)), min rc (min (S.R / 4) 1),
    lt_min hrc (lt_min (by linarith) one_pos), fun r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  have hrc' : r ≤ rc := hr.2.trans (min_le_left _ _)
  have hrR : r ≤ S.R / 4 := hr.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r ≤ 1 := hr.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hv := hCm r ⟨hr0, by linarith⟩
  have hv2 := hCm (2 * r) ⟨by linarith, by linarith⟩
  have hg2 := hCg (2 * r) ⟨by linarith, by linarith⟩
  have hc := hcacc r ⟨hr0, hrc'⟩
  have hint1 : IntegrableOn (fun x => S.v x ^ 2) (halfBall n r) :=
    integrableOn_halfBall_of_continuousOn (by linarith) (S.v_continuousOn.pow 2)
  have hint2 : IntegrableOn (fun x => ‖S.Dv x‖ ^ 2) (halfBall n r) :=
    integrableOn_halfBall_of_continuousOn (by linarith) (S.Dv_continuousOn.norm.pow 2)
  rw [integral_add hint1 hint2]
  have hpow : r ^ (M + 2) = r ^ M * r ^ 2 := pow_add r M 2
  have h2pow : (2 * r) ^ (M + 2) = 2 ^ (M + 2) * (r ^ M * r ^ 2) := by rw [mul_pow, hpow]
  have hrM : 0 ≤ r ^ M := pow_nonneg hr0.le M
  have hr2 : 0 < r ^ 2 := by positivity
  have hr2le : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
  have hrn : r ^ (n + 2) ≤ 1 := pow_le_one₀ hr0.le hr1
  have h2M : (0 : ℝ) < 2 ^ (M + 2) := by positivity
  -- the `v²` part
  have hA : ∫ x in halfBall n r, S.v x ^ 2 ≤ |Cm| * r ^ M := by
    calc ∫ x in halfBall n r, S.v x ^ 2 ≤ Cm * r ^ (M + 2) := hv
      _ ≤ |Cm| * (r ^ M * r ^ 2) := by
          rw [hpow]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cm| * (r ^ M * 1) := by gcongr
      _ = |Cm| * r ^ M := by ring
  -- the gradient part
  have hB : r ^ 2 * ∫ x in halfBall n r, ‖S.Dv x‖ ^ 2
      ≤ r ^ 2 * (Cc * (|Cm| * 2 ^ (M + 2) + |Cg| * 2 ^ (M + 2)) * r ^ M) := by
    have e1 : ∫ x in halfBall n (2 * r), S.v x ^ 2 ≤ |Cm| * 2 ^ (M + 2) * r ^ M * r ^ 2 := by
      calc ∫ x in halfBall n (2 * r), S.v x ^ 2 ≤ Cm * (2 * r) ^ (M + 2) := hv2
        _ ≤ |Cm| * (2 * r) ^ (M + 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = |Cm| * 2 ^ (M + 2) * r ^ M * r ^ 2 := by rw [h2pow]; ring
    have e2 : r ^ (n + 2) * g (2 * r) ≤ |Cg| * 2 ^ (M + 2) * r ^ M * r ^ 2 := by
      have hg2' : g (2 * r) ≤ |Cg| * 2 ^ (M + 2) * r ^ M * r ^ 2 := by
        calc g (2 * r) ≤ Cg * (2 * r) ^ (M + 2) := hg2
          _ ≤ |Cg| * (2 * r) ^ (M + 2) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ = |Cg| * 2 ^ (M + 2) * r ^ M * r ^ 2 := by rw [h2pow]; ring
      have hgpos : 0 < g (2 * r) := hg_pos _ (by linarith)
      calc r ^ (n + 2) * g (2 * r) ≤ 1 * g (2 * r) :=
            mul_le_mul_of_nonneg_right hrn hgpos.le
        _ ≤ |Cg| * 2 ^ (M + 2) * r ^ M * r ^ 2 := by linarith
    calc r ^ 2 * ∫ x in halfBall n r, ‖S.Dv x‖ ^ 2
        ≤ Cc * ((∫ x in halfBall n (2 * r), S.v x ^ 2) + r ^ (n + 2) * g (2 * r)) := hc
      _ ≤ Cc * (|Cm| * 2 ^ (M + 2) * r ^ M * r ^ 2 + |Cg| * 2 ^ (M + 2) * r ^ M * r ^ 2) := by
          gcongr
      _ = r ^ 2 * (Cc * (|Cm| * 2 ^ (M + 2) + |Cg| * 2 ^ (M + 2)) * r ^ M) := by ring
  have hB' := le_of_mul_le_mul_left hB hr2
  calc (∫ x in halfBall n r, S.v x ^ 2) + ∫ x in halfBall n r, ‖S.Dv x‖ ^ 2
      ≤ |Cm| * r ^ M + Cc * (|Cm| * 2 ^ (M + 2) + |Cg| * 2 ^ (M + 2)) * r ^ M := by linarith
    _ = (|Cm| + Cc * (|Cm| * 2 ^ (M + 2) + |Cg| * 2 ^ (M + 2))) * r ^ M := by ring

/-! ### The Carleman weights in `x` coordinates -/

/-- The density `μ = ρ^{-d}` of the cylinder volume. -/
noncomputable def muR (n : ℕ) (x : Space n) : ℝ := (‖x‖ ^ (n + 1))⁻¹

/-- The matrix field `B = ρ² A` (the cylinder `A` acting on Euclidean gradients). -/
noncomputable def BR (A : Space n → Space n →L[ℝ] Space n) (x : Space n) :
    Space n →L[ℝ] Space n :=
  (‖x‖ ^ 2) • A x

/-- The weight `φ = G(-log ρ) = -log ρ + ε ρ`. -/
noncomputable def phiR (ε : ℝ) (x : Space n) : ℝ := -Real.log ‖x‖ + ε * ‖x‖

/-- `m = (d - 2) / 2`. -/
noncomputable def mR (n : ℕ) : ℝ := ((n : ℝ) - 1) / 2

/-- The cylinder operator `P₀ f = div_μ(B ∇f) - m² f`. -/
noncomputable def P0R (A : Space n → Space n →L[ℝ] Space n) (f : Space n → ℝ) (x : Space n) :
    ℝ :=
  divMu (muR n) (fun y => BR A y (gradient f y)) x - mR n ^ 2 * f x

namespace W_R_carleman

/-! ### Helpers for `RPkg.carleman`

**Status (end of round 2).** `RPkg.carleman` is proved from `core`, and `core` is proved from
`main_lower`, `grad_control`, `back_to_f` and the real-number lemma `core_algebra` (with
`C_J = 16 K² + 1`, `ε = 2 (5 K² + 2 C_J K / λ + 1)`, `rs = min(1/(4ε), 1/(4(K+1)), R/2, 1)`).
Fully proved: `back_to_f`, `grad_control` (via `gc_pointwise`, `gc_div_integrable`,
`gc_boundary`, `gc_pointwise_bound`), the weight calculus (`gradient_phiR`, `carlV_eq`,
`inner_carlV_ed`, `inner_BR_WC_ed`, `carlQ_le`, `gradient_wC`, `conj_eq`), the `L²` bound
`integrableOn_SpC_sq`, `main_lower` from its pieces, `ml_pointwise`, `ml_boundaryM` and
`ml_boundary` (from `ml_boundaryC` and `ml_boundaryM`).

**Remaining sorries** (all in the `main_lower` block, all believed true):
* `ml_J_lower` — the pointwise lower bound of `carlJ` (calculus of `V = -(1-ερ) A x`,
  `q = (1-ερ)² ⟪A x, x⟫/ρ²`, `DV`, `DB`, and a bound `C_h` for `∇ div_μ V` on `0 < ρ ≤ rs`;
  see its docstring for the three estimates and constants).
* `ml_div_integrable` — copy the proof of `gc_div_integrable`, using `ml_pointwise` (needs
  continuity away from `0` of `gradient carlQ`, `fderiv carlV`, `fderiv BR`,
  `gradient (divMu μ V)`, all from `C²` of `A`; and the formula for `div MFlux` proved inside
  `ml_pointwise`).
* `ml_boundaryC` — copy the proof of `gc_boundary` with the flux `CFlux` (regularity and
  support exactly as for `GFlux`/`MFlux`); on `t = 0` the integrand is
  `μ ρ² e^{τφ} ⟪A Df, e_d⟫ (-4τ ⟪V, W⟫ - 2τ (div_μ V) w)` (the `V`-terms vanish by
  `inner_carlV_ed`), bounded with `|V| ≤ K ρ` (`carlV_eq`), `ρ |W| ≤ e^{τφ} (ρ |Df| + τ |f|)`
  and a bound `|div_μ V| ≤ C_h0` on `0 < ρ ≤ rs` (e.g. `C_h0 = sup` of the continuous function
  `ρ⁻¹ div_μ V`, or an explicit formula `div_μ V = (1-ερ)(d ⟪Ax,x⟫/ρ² - tr A - tr(DA(·)x))
  + ε ⟪Ax,x⟫/ρ`). Then `CB = 4K + 2 C_h0` works for `τ ≥ 1`. -/

open RPkg

theorem continuousAt_muR {x : Space n} (hx : x ≠ 0) : ContinuousAt (muR n) x := by
  unfold muR
  exact ((continuous_norm.pow (n + 1)).continuousAt).inv₀
    (pow_ne_zero _ (norm_ne_zero_iff.2 hx))

theorem continuousAt_phiR (ε : ℝ) {x : Space n} (hx : x ≠ 0) : ContinuousAt (phiR ε) x := by
  unfold phiR
  exact ((Real.continuousAt_log (norm_ne_zero_iff.2 hx)).comp
    continuous_norm.continuousAt).neg.add (continuous_const.mul continuous_norm).continuousAt

theorem muR_nonneg (x : Space n) : 0 ≤ muR n x := by unfold muR; positivity

/-- The weight `μ e^{2τφ}` is continuous away from `0`. -/
theorem continuousAt_weight (ε τ : ℝ) {x : Space n} (hx : x ≠ 0) :
    ContinuousAt (fun y => muR n y * Real.exp (2 * τ * phiR ε y)) x :=
  (continuousAt_muR hx).mul (Real.continuous_exp.continuousAt.comp
    (continuousAt_const.mul (continuousAt_phiR ε hx)))

/-- A function supported in the closed annulus `δ ≤ ‖x‖ ≤ rs`, continuous (within the closed
half-space) at every nonzero point of the closed half-space, is integrable on the open
half-space. -/
theorem integrableOn_of_annulus {g : Space n → ℝ} {δ rs : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ x, g x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs)
    (hc : ∀ x, 0 ≤ vcoord x → x ≠ 0 → ContinuousWithinAt g {x | 0 ≤ vcoord x} x) :
    IntegrableOn g {x | 0 < vcoord x} := by
  have hcont : ContinuousOn g {x | 0 ≤ vcoord x} := by
    intro x hx
    by_cases hx0 : x = 0
    · have hev : g =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
        by_contra hne
        have := (hsupp y hne).1
        rw [Metric.mem_ball, hx0, dist_zero_right] at hy
        linarith
      exact (continuousAt_const.congr hev.symm).continuousWithinAt
    · exact hc x hx hx0
  have hK : IsCompact {x : Space n | ‖x‖ ≤ rs ∧ 0 ≤ vcoord x} := by
    have e : {x : Space n | ‖x‖ ≤ rs ∧ 0 ≤ vcoord x}
        = Metric.closedBall 0 rs ∩ {x | 0 ≤ vcoord x} := by
      ext x
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [e]
    exact (isCompact_closedBall 0 rs).inter_right
      (isClosed_le continuous_const F1.continuous_vcoord)
  have h1 : IntegrableOn g {x : Space n | ‖x‖ ≤ rs ∧ 0 ≤ vcoord x} :=
    (hcont.mono fun x (hx : x ∈ {x : Space n | ‖x‖ ≤ rs ∧ 0 ≤ vcoord x}) => hx.2).integrableOn_compact hK
  refine h1.of_forall_sdiff_eq_zero (F1.measurableSet_halfSpace 0) fun x
    (hx : x ∈ {x : Space n | 0 < vcoord x} \ {x : Space n | ‖x‖ ≤ rs ∧ 0 ≤ vcoord x}) => ?_
  by_contra h
  exact hx.2 ⟨(hsupp x h).2, le_of_lt hx.1⟩

theorem contDiffAt_muR {x : Space n} (hx : x ≠ 0) {k : ℕ∞ω} : ContDiffAt ℝ k (muR n) x := by
  unfold muR
  exact ((contDiffAt_norm ℝ hx).pow (n + 1)).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hx))

theorem muR_ne_zero {x : Space n} (hx : x ≠ 0) : muR n x ≠ 0 := by
  unfold muR
  exact inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hx))

theorem BR_eq (A : Space n → Space n →L[ℝ] Space n) : BR A = fun x => (‖x‖ ^ 2) • A x := rfl

theorem contDiff_BR (S : HalfBallSolution n) : ContDiff ℝ 2 (BR S.A) := by
  rw [BR_eq]
  exact (contDiff_norm_sq ℝ).smul S.coeffs.contDiff_A

theorem ne_zero_of_vcoord_pos {x : Space n} (hx : 0 < vcoord x) : x ≠ 0 := by
  rintro rfl
  simp [vcoord] at hx

/-- `P₀ f` is continuous on the open half-space when `f` is `C²` there. -/
theorem continuousOn_P0R (S : HalfBallSolution n) {f : Space n → ℝ}
    (hf : ∀ x, 0 < vcoord x → ContDiffAt ℝ 2 f x) :
    ContinuousOn (P0R S.A f) {x | 0 < vcoord x} := by
  intro x hx
  have hx0 : x ≠ 0 := ne_zero_of_vcoord_pos hx
  have hG : ContDiffAt ℝ 1 (fun y => muR n y • BR S.A y (gradient f y)) x :=
    (contDiffAt_muR hx0).smul (((contDiff_BR S).contDiffAt.of_le (by norm_num)).clm_apply
      (F2.contDiffAt_gradient (m := 1) (hf x hx) (by norm_num)))
  have h1 : ContinuousAt (fderiv ℝ (fun y => muR n y • BR S.A y (gradient f y))) x :=
    (hG.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hdiv : ContinuousAt
      (fun y => divergence (fun y => muR n y • BR S.A y (gradient f y)) y) x :=
    (F2.traceCLM (n := n)).continuous.continuousAt.comp h1
  have hfc : ContinuousAt f x := (hf x hx).continuousAt
  have hP : P0R S.A f = fun y => (muR n y)⁻¹ *
      divergence (fun y => muR n y • BR S.A y (gradient f y)) y - mR n ^ 2 * f y := rfl
  rw [hP]
  exact ((((continuousAt_muR hx0).inv₀ (muR_ne_zero hx0)).mul hdiv).sub
    (continuousAt_const.mul hfc)).continuousWithinAt

/-- The pointwise absorption inequality. -/
theorem ptwise_real {P Fa ρ D fv K₁ : ℝ} (hρ : 0 ≤ ρ) (hK : 0 ≤ K₁) (hD : 0 ≤ D)
    (hP : |P| ≤ |Fa| + K₁ * ρ * (ρ * D + |fv|)) (h1 : ρ ^ 4 * D ^ 2 ≤ ρ ^ 3 * D ^ 2)
    (h2 : ρ ^ 2 * fv ^ 2 ≤ ρ * fv ^ 2) :
    P ^ 2 ≤ 2 * Fa ^ 2 + 4 * K₁ ^ 2 * (ρ ^ 3 * D ^ 2) + 4 * K₁ ^ 2 * (ρ * fv ^ 2) := by
  set b := K₁ * ρ * (ρ * D + |fv|) with hb
  have hb0 : 0 ≤ b := by positivity
  have hsq : P ^ 2 ≤ (|Fa| + b) ^ 2 := by
    rw [← sq_abs P]
    exact pow_le_pow_left₀ (abs_nonneg _) hP 2
  have e1 : (|Fa| + b) ^ 2 ≤ 2 * Fa ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (|Fa| - b), sq_abs Fa]
  have e2 : b ^ 2 ≤ 2 * K₁ ^ 2 * (ρ ^ 4 * D ^ 2 + ρ ^ 2 * fv ^ 2) := by
    have h3 : (ρ * D + |fv|) ^ 2 ≤ 2 * (ρ ^ 2 * D ^ 2 + fv ^ 2) := by
      nlinarith [sq_nonneg (ρ * D - |fv|), sq_abs fv]
    calc b ^ 2 = K₁ ^ 2 * ρ ^ 2 * (ρ * D + |fv|) ^ 2 := by rw [hb]; ring
      _ ≤ K₁ ^ 2 * ρ ^ 2 * (2 * (ρ ^ 2 * D ^ 2 + fv ^ 2)) := by gcongr
      _ = 2 * K₁ ^ 2 * (ρ ^ 4 * D ^ 2 + ρ ^ 2 * fv ^ 2) := by ring
  have e3 : 2 * K₁ ^ 2 * (ρ ^ 4 * D ^ 2 + ρ ^ 2 * fv ^ 2)
      ≤ 2 * K₁ ^ 2 * (ρ ^ 3 * D ^ 2 + ρ * fv ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
  linarith

/-- The final absorption of the perturbation terms. -/
theorem final_algebra {τ C K₁ X Y Fi P Bd : ℝ} (hτ1 : 1 ≤ τ) (hτK : 8 * C * K₁ ^ 2 + 1 ≤ τ)
    (hC : 0 < C) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hBd : 0 ≤ Bd)
    (hcore : τ ^ 3 * X + τ * Y ≤ C * P + C * τ ^ 2 * Bd)
    (hP : P ≤ 2 * Fi + 4 * K₁ ^ 2 * Y + 4 * K₁ ^ 2 * X) :
    τ ^ 3 * X + τ * Y ≤ 4 * C * Fi + 4 * C * τ ^ 2 * Bd := by
  have h1 : C * P ≤ C * (2 * Fi + 4 * K₁ ^ 2 * Y + 4 * K₁ ^ 2 * X) :=
    mul_le_mul_of_nonneg_left hP hC.le
  have hτ3 : τ ≤ τ ^ 3 := by nlinarith
  have hk : 4 * C * K₁ ^ 2 ≤ τ / 2 := by nlinarith [sq_nonneg K₁]
  have h2 : 4 * C * K₁ ^ 2 * X ≤ τ ^ 3 / 2 * X := mul_le_mul_of_nonneg_right (by linarith) hX
  have h3 : 4 * C * K₁ ^ 2 * Y ≤ τ / 2 * Y := mul_le_mul_of_nonneg_right hk hY
  have h4 : 0 ≤ C * τ ^ 2 * Bd := by positivity
  nlinarith

/-! ### The objects of the Carleman argument -/

/-- `∇φ = -(1 - ερ) x / ρ²` (the gradient of `phiR ε` away from `0`). -/
noncomputable def gradPhi (ε : ℝ) (x : Space n) : Space n := (-(1 - ε * ‖x‖) / ‖x‖ ^ 2) • x

/-- The conjugated function `w = e^{τφ} f`. -/
noncomputable def wC (ε τ : ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp (τ * phiR ε x) * f x

/-- The gradient of `w`, written with `Df` (continuous up to `t = 0`):
`W = e^{τφ} (Df + τ f ∇φ)`. -/
noncomputable def WC (ε τ : ℝ) (f : Space n → ℝ) (Df : Space n → Space n) (x : Space n) :
    Space n :=
  Real.exp (τ * phiR ε x) • (Df x + (τ * f x) • gradPhi ε x)

/-- `S' w = S w - m² w`, the symmetric part of `e^{τφ} P₀ e^{-τφ}`. -/
noncomputable def SpC (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  carlS (muR n) (BR S.A) (phiR ε) τ (wC ε τ f) x - mR n ^ 2 * wC ε τ f x

/-- The standing hypotheses on `f` and `Df` in Lemma R2. -/
structure Admissible (rs δ : ℝ) (f : Space n → ℝ) (Df : Space n → Space n) : Prop where
  pos : 0 < δ
  supp : ∀ x, f x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs
  Dsupp : ∀ x, Df x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs
  c2 : ∀ x, 0 < vcoord x → ContDiffAt ℝ 2 f x
  grad : ∀ x, 0 < vcoord x → gradient f x = Df x
  cont : ContinuousOn f {x | 0 ≤ vcoord x}
  Dcont : ContinuousOn Df {x | 0 ≤ vcoord x}

/-- `X = ∫ ρ μ w²`. -/
noncomputable def IX (ε τ : ℝ) (f : Space n → ℝ) : ℝ :=
  ∫ x in {x : Space n | 0 < vcoord x}, ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2

/-- `Y_f = ∫ ρ³ μ e^{2τφ} |Df|²`. -/
noncomputable def IYf (ε τ : ℝ) (Df : Space n → Space n) : ℝ :=
  ∫ x in {x : Space n | 0 < vcoord x}, ‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2

/-- `Y = ∫ ρ³ μ |∇w|²`. -/
noncomputable def IY (ε τ : ℝ) (f : Space n → ℝ) (Df : Space n → Space n) : ℝ :=
  ∫ x in {x : Space n | 0 < vcoord x}, ‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2

/-- `Σ = ∫ μ (S' w)²`. -/
noncomputable def ISg (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ) : ℝ :=
  ∫ x in {x : Space n | 0 < vcoord x}, muR n x * SpC S ε τ f x ^ 2

/-- `‖e^{τφ} P₀ f‖² = ∫ μ e^{2τφ} (P₀ f)²`. -/
noncomputable def IPP (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ) : ℝ :=
  ∫ x in {x : Space n | 0 < vcoord x}, muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2

/-- The boundary integral of Lemma R2. -/
noncomputable def IBd (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ)
    (Df : Space n → Space n) : ℝ :=
  ∫ y : EuclideanSpace ℝ (Fin n),
    ‖lift y 0‖ ^ 2 * muR n (lift y 0) * Real.exp (2 * τ * phiR ε (lift y 0)) *
      (|⟪S.A (lift y 0) (Df (lift y 0)), ed n⟫_ℝ| *
        (‖lift y 0‖ * ‖Df (lift y 0)‖ + |f (lift y 0)|))


/-! ### Calculus of the weights (infrastructure for `grad_control` and `main_lower`) -/

/-- The derivative of the norm away from `0`. -/
theorem hasFDerivAt_norm' {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Space n => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hpos : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.2 hx
    positivity
  have h2 := (Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt x h1
  have hρ : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  convert h2 using 1
  · funext y
    simp [Function.comp, Real.sqrt_sq (norm_nonneg y)]
  rw [Real.sqrt_sq (norm_nonneg x)]
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Function.comp_apply]
  field_simp
  push_cast
  ring

/-- The gradient of the norm away from `0`: `∇ρ = x / ρ`. -/
theorem gradient_norm' {x : Space n} (hx : x ≠ 0) :
    gradient (fun y : Space n => ‖y‖) x = ‖x‖⁻¹ • x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, (hasFDerivAt_norm' hx).fderiv]
  simp [real_inner_smul_left]

/-- The derivative of `φ = -log ρ + ε ρ` away from `0`. -/
theorem hasFDerivAt_phiR (ε : ℝ) {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (phiR ε) ((-(1 - ε * ‖x‖) / ‖x‖ ^ 2) • innerSL ℝ x) x := by
  have hρ : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hn := hasFDerivAt_norm' hx
  have hlog := (Real.hasDerivAt_log hρ).comp_hasFDerivAt x hn
  have h := hlog.neg.add (hn.const_mul ε)
  have e : phiR ε = fun y : Space n => -Real.log ‖y‖ + ε * ‖y‖ := rfl
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  field_simp
  ring

/-- `∇φ = gradPhi`. -/
theorem gradient_phiR (ε : ℝ) {x : Space n} (hx : x ≠ 0) :
    gradient (phiR ε) x = gradPhi ε x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, (hasFDerivAt_phiR ε hx).fderiv]
  simp [gradPhi, real_inner_smul_left]

/-- `φ` is smooth away from `0`. -/
theorem contDiffAt_phiR (ε : ℝ) {x : Space n} (hx : x ≠ 0) {k : ℕ∞ω} :
    ContDiffAt ℝ k (phiR ε) x := by
  have hρ : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have e : phiR ε = fun y : Space n => -Real.log ‖y‖ + ε * ‖y‖ := rfl
  rw [e]
  exact ((Real.contDiffAt_log.2 hρ).comp x (contDiffAt_norm ℝ hx)).neg.add
    (contDiffAt_const.mul (contDiffAt_norm ℝ hx))

/-- `V = B ∇φ = -(1 - ερ) A x`. -/
theorem carlV_eq (S : HalfBallSolution n) (ε : ℝ) {x : Space n} (hx : x ≠ 0) :
    carlV (BR S.A) (phiR ε) x = (-(1 - ε * ‖x‖)) • S.A x x := by
  have hρ : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  simp only [carlV, gradient_phiR ε hx, gradPhi, BR, ContinuousLinearMap.smul_apply, map_smul,
    smul_smul]
  congr 1
  field_simp

/-- On the flat boundary, `⟪V, e_d⟫ = 0` (conormal condition and symmetry of `A`). -/
theorem inner_carlV_ed (S : HalfBallSolution n) (ε : ℝ) {x : Space n} (hx : x ≠ 0)
    (hxf : x ∈ flatPiece n S.R) : ⟪carlV (BR S.A) (phiR ε) x, ed n⟫_ℝ = 0 := by
  obtain ⟨c, hc⟩ := S.conormal x hxf
  have h0 : vcoord x = 0 := hxf.2
  simp only [vcoord] at h0
  rw [carlV_eq S ε hx, real_inner_smul_left, S.coeffs.symm, hc, real_inner_smul_right,
    F1.inner_ed]
  simp [h0]

/-- On the flat boundary, `⟪A ∇φ, e_d⟫ = 0`, hence `⟪B W, e_d⟫ = ρ² e^{τφ} ⟪A Df, e_d⟫`. -/
theorem inner_BR_WC_ed (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ)
    (Df : Space n → Space n) {x : Space n} (hx : x ≠ 0) (hxf : x ∈ flatPiece n S.R) :
    ⟪BR S.A x (WC ε τ f Df x), ed n⟫_ℝ
      = ‖x‖ ^ 2 * Real.exp (τ * phiR ε x) * ⟪S.A x (Df x), ed n⟫_ℝ := by
  obtain ⟨c, hc⟩ := S.conormal x hxf
  have hx0 : x (Fin.last n) = 0 := hxf.2
  have hg : ⟪S.A x (gradPhi ε x), ed n⟫_ℝ = 0 := by
    rw [S.coeffs.symm, hc, real_inner_smul_right]
    simp only [gradPhi, real_inner_smul_left]
    rw [F1.inner_ed, hx0]
    ring
  simp only [BR, WC, ContinuousLinearMap.smul_apply, map_smul, map_add, inner_smul_left,
    inner_add_left, hg]
  simp [real_inner_smul_left]
  ring


/-- `B = ρ² A` is symmetric. -/
theorem BR_symm (S : HalfBallSolution n) (x ξ η : Space n) :
    ⟪BR S.A x ξ, η⟫_ℝ = ⟪ξ, BR S.A x η⟫_ℝ := by
  simp only [BR, ContinuousLinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
    S.coeffs.symm]

/-- `w = e^{τφ} f` is `C²` in the open half-space. -/
theorem contDiffAt_wC {ε τ rs δ : ℝ} {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 < vcoord x) :
    ContDiffAt ℝ 2 (wC ε τ f) x := by
  have hx0 := ne_zero_of_vcoord_pos hx
  have e : wC ε τ f = fun z => Real.exp (τ * phiR ε z) * f z := rfl
  rw [e]
  exact ((contDiffAt_const.mul (contDiffAt_phiR ε hx0)).exp).mul (hadm.c2 x hx)

/-- In the open half-space, `∇w = W`. -/
theorem gradient_wC {ε τ rs δ : ℝ} {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 < vcoord x) :
    gradient (wC ε τ f) x = WC ε τ f Df x := by
  have hx0 := ne_zero_of_vcoord_pos hx
  have hE : HasFDerivAt (fun z => Real.exp (τ * phiR ε z))
      (Real.exp (τ * phiR ε x) • (τ • ((-(1 - ε * ‖x‖) / ‖x‖ ^ 2) • innerSL ℝ x))) x :=
    ((hasFDerivAt_phiR ε hx0).const_mul τ).exp
  have hfd : HasFDerivAt f (fderiv ℝ f x) x :=
    ((hadm.c2 x hx).differentiableAt (by norm_num)).hasFDerivAt
  have hw : HasFDerivAt (fun z => Real.exp (τ * phiR ε z) * f z) _ x := hE.mul hfd
  have e : wC ε τ f = fun z => Real.exp (τ * phiR ε z) * f z := rfl
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, e, hw.fderiv]
  have hg : fderiv ℝ f x v = ⟪Df x, v⟫_ℝ := by
    rw [← hadm.grad x hx, inner_gradient_left]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply, hg, WC, gradPhi, inner_smul_left, inner_add_left,
    real_inner_smul_left, RCLike.conj_to_real]
  ring

/-- The conjugation identity: `e^{τφ} P₀ f = S' w + T w` in the open half-space. -/
theorem conj_eq (S : HalfBallSolution n) (ε τ : ℝ) {rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 < vcoord x) :
    Real.exp (τ * phiR ε x) * P0R S.A f x
      = SpC S ε τ f x + carlT (muR n) (BR S.A) (phiR ε) τ (wC ε τ f) x := by
  have hx0 := ne_zero_of_vcoord_pos hx
  have key := F2.carleman_conj_of_symm' (muR n) (BR S.A) (phiR ε) τ f x (contDiffAt_muR hx0)
    (muR_ne_zero hx0) ((contDiff_BR S).contDiffAt.of_le (by norm_num)) (BR_symm S x)
    (contDiffAt_phiR ε hx0) (hadm.c2 x hx)
  have e : (fun z => Real.exp (τ * phiR ε z) * f z) = wC ε τ f := rfl
  rw [e] at key
  simp only [P0R, SpC, wC] at key ⊢
  rw [mul_sub, key]
  ring


/-! ### Continuity, supports and the square-integrability of `S' w` -/

theorem continuousAt_gradPhi (ε : ℝ) {x : Space n} (hx0 : x ≠ 0) :
    ContinuousAt (gradPhi ε) x := by
  have e : gradPhi ε = fun y : Space n => (-(1 - ε * ‖y‖) / ‖y‖ ^ 2) • y := rfl
  rw [e]
  exact (((continuous_const.sub (continuous_const.mul continuous_norm)).neg.continuousAt).div
    (continuous_norm.pow 2).continuousAt
    (pow_ne_zero 2 (norm_ne_zero_iff.2 hx0))).smul continuousAt_id

theorem continuousAt_expPhi (ε τ : ℝ) {x : Space n} (hx0 : x ≠ 0) :
    ContinuousAt (fun y => Real.exp (τ * phiR ε y)) x :=
  Real.continuous_exp.continuousAt.comp (continuousAt_const.mul (continuousAt_phiR ε hx0))

theorem continuousWithinAt_WC {ε τ rs δ : ℝ} {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 ≤ vcoord x) (hx0 : x ≠ 0) :
    ContinuousWithinAt (WC ε τ f Df) {x | 0 ≤ vcoord x} x :=
  (continuousAt_expPhi ε τ hx0).continuousWithinAt.smul ((hadm.Dcont x hx).add
    ((continuousWithinAt_const.mul (hadm.cont x hx)).smul
      (continuousAt_gradPhi ε hx0).continuousWithinAt))

theorem continuousWithinAt_wC {ε τ rs δ : ℝ} {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 ≤ vcoord x) (hx0 : x ≠ 0) :
    ContinuousWithinAt (wC ε τ f) {x | 0 ≤ vcoord x} x :=
  (continuousAt_expPhi ε τ hx0).continuousWithinAt.mul (hadm.cont x hx)

theorem WC_supp {ε τ rs δ : ℝ} {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) (x : Space n) (hx : WC ε τ f Df x ≠ 0) :
    δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs := by
  by_contra hcon
  apply hx
  have hf0 : f x = 0 := by
    by_contra h; exact hcon (hadm.supp x h)
  have hD0 : Df x = 0 := by
    by_contra h; exact hcon (hadm.Dsupp x h)
  simp [WC, hf0, hD0]

theorem wC_supp {ε τ rs δ : ℝ} {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) (x : Space n) (hx : wC ε τ f x ≠ 0) :
    δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs := by
  have : f x ≠ 0 := by
    intro h; apply hx; simp [wC, h]
  exact hadm.supp x this

/-- `V` is `C¹` away from `0`. -/
theorem contDiffAt_carlV (S : HalfBallSolution n) (ε : ℝ) {x : Space n} (hx0 : x ≠ 0) :
    ContDiffAt ℝ 1 (carlV (BR S.A) (phiR ε)) x :=
  ((contDiff_BR S).contDiffAt.of_le (by norm_num)).clm_apply
    (F2.contDiffAt_gradient (m := 1) (contDiffAt_phiR ε hx0 (k := 2)) (by norm_num))

/-- `div_μ V` is continuous away from `0`. -/
theorem continuousAt_divMuV (S : HalfBallSolution n) (ε : ℝ) {x : Space n} (hx0 : x ≠ 0) :
    ContinuousAt (divMu (muR n) (carlV (BR S.A) (phiR ε))) x := by
  have hG : ContDiffAt ℝ 1 (fun y => muR n y • carlV (BR S.A) (phiR ε) y) x :=
    (contDiffAt_muR hx0).smul (contDiffAt_carlV S ε hx0)
  have h1 : ContinuousAt (fderiv ℝ (fun y => muR n y • carlV (BR S.A) (phiR ε) y)) x :=
    (hG.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hdiv : ContinuousAt
      (fun y => divergence (fun y => muR n y • carlV (BR S.A) (phiR ε) y) y) x :=
    (F2.traceCLM (n := n)).continuous.continuousAt.comp h1
  exact ((continuousAt_muR hx0).inv₀ (muR_ne_zero hx0)).mul hdiv

/-- `T w`, written with `W` (continuous up to `t = 0`). -/
noncomputable def TWC (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ)
    (Df : Space n → Space n) (x : Space n) : ℝ :=
  -2 * τ * ⟪carlV (BR S.A) (phiR ε) x, WC ε τ f Df x⟫_ℝ
    - τ * divMu (muR n) (carlV (BR S.A) (phiR ε)) x * wC ε τ f x

theorem carlT_eq (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 < vcoord x) :
    carlT (muR n) (BR S.A) (phiR ε) τ (wC ε τ f) x = TWC S ε τ f Df x := by
  simp only [carlT, TWC, gradient_wC hadm hx]

theorem continuousWithinAt_TWC (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 ≤ vcoord x)
    (hx0 : x ≠ 0) : ContinuousWithinAt (TWC S ε τ f Df) {x | 0 ≤ vcoord x} x := by
  have hV := (contDiffAt_carlV S ε hx0).continuousAt.continuousWithinAt
    (s := {x : Space n | 0 ≤ vcoord x})
  have hW := continuousWithinAt_WC (ε := ε) (τ := τ) hadm hx hx0
  have hw := continuousWithinAt_wC (ε := ε) (τ := τ) hadm hx hx0
  have hh := (continuousAt_divMuV S ε hx0).continuousWithinAt (s := {x : Space n | 0 ≤ vcoord x})
  exact (continuousWithinAt_const.mul (hV.inner hW)).sub
    ((continuousWithinAt_const.mul hh).mul hw)

theorem TWC_supp (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) (x : Space n)
    (hx : TWC S ε τ f Df x ≠ 0) : δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs := by
  by_cases hW : WC ε τ f Df x = 0
  · by_cases hw : wC ε τ f x = 0
    · exfalso; apply hx; simp [TWC, hW, hw]
    · exact wC_supp hadm x hw
  · exact WC_supp hadm x hW

/-- **`S' w ∈ L²(μ)`** on the open half-space: `S' w = e^{τφ} P₀ f - T w` there, the first term
is in `L²(μ)` by hypothesis and `T w` is continuous with compact support away from `0`. -/
theorem integrableOn_SpC_sq (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df)
    (hPi : IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
      {x | 0 < vcoord x}) :
    IntegrableOn (fun x => muR n x * SpC S ε τ f x ^ 2) {x | 0 < vcoord x} := by
  have hΩm : MeasurableSet {x : Space n | 0 < vcoord x} := F1.measurableSet_halfSpace 0
  -- `μ T² ` is integrable
  have hTi : IntegrableOn (fun x => muR n x * TWC S ε τ f Df x ^ 2) {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => ?_) fun x hx hx0 => ?_
    · have : TWC S ε τ f Df x ≠ 0 := by
        intro h; apply hx; simp [h]
      exact TWC_supp S hadm x this
    · exact (continuousAt_muR hx0).continuousWithinAt.mul
        ((continuousWithinAt_TWC S hadm hx hx0).pow 2)
  -- the identity `S' w = e^{τφ} P₀ f - T w`
  have hid : ∀ x ∈ {x : Space n | 0 < vcoord x},
      SpC S ε τ f x = Real.exp (τ * phiR ε x) * P0R S.A f x - TWC S ε τ f Df x := by
    intro x hx
    rw [conj_eq S ε τ hadm hx, carlT_eq S hadm hx]
    ring
  -- continuity on the open half-space
  have hcont : ContinuousOn (fun x => muR n x * SpC S ε τ f x ^ 2) {x | 0 < vcoord x} := by
    intro x hx
    have hx0 := ne_zero_of_vcoord_pos hx
    have hU : {x : Space n | 0 < vcoord x} ∈ 𝓝 x :=
      (isOpen_lt continuous_const F1.continuous_vcoord).mem_nhds hx
    have h1 : ContinuousWithinAt
        (fun y => Real.exp (τ * phiR ε y) * P0R S.A f y - TWC S ε τ f Df y)
        {x | 0 < vcoord x} x :=
      ((continuousAt_expPhi ε τ hx0).continuousWithinAt.mul
        (continuousOn_P0R S hadm.c2 x hx)).sub
        ((continuousWithinAt_TWC S hadm (le_of_lt hx) hx0).mono
          fun y (hy : 0 < vcoord y) => (le_of_lt hy : 0 ≤ vcoord y))
    have h2 : ContinuousWithinAt (SpC S ε τ f) {x | 0 < vcoord x} x :=
      h1.congr (fun y hy => hid y hy) (hid x hx)
    exact (continuousAt_muR hx0).continuousWithinAt.mul (h2.pow 2)
  -- domination
  have hdom : IntegrableOn (fun x =>
      2 * (muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
        + 2 * (muR n x * TWC S ε τ f Df x ^ 2)) {x | 0 < vcoord x} :=
    (hPi.const_mul 2).add (hTi.const_mul 2)
  refine Integrable.mono' hdom (hcont.aestronglyMeasurable hΩm) ?_
  refine (ae_restrict_iff' hΩm).2 (Eventually.of_forall fun x hx => ?_)
  have hμ := muR_nonneg x
  have h0 : 0 ≤ muR n x * SpC S ε τ f x ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0, hid x hx]
  have hE2 : Real.exp (2 * τ * phiR ε x) = Real.exp (τ * phiR ε x) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [hE2]
  have key : (Real.exp (τ * phiR ε x) * P0R S.A f x - TWC S ε τ f Df x) ^ 2
      ≤ 2 * (Real.exp (τ * phiR ε x) ^ 2 * P0R S.A f x ^ 2) + 2 * TWC S ε τ f Df x ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (τ * phiR ε x) * P0R S.A f x + TWC S ε τ f Df x)]
  have := mul_le_mul_of_nonneg_left key hμ
  nlinarith


/-! ### Pieces of `grad_control` -/

theorem integrableOn_X {ε τ rs δ : ℝ} {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) :
    IntegrableOn (fun x => ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      {x | 0 < vcoord x} := by
  refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => ?_) fun x hx hx0 => ?_
  · have : f x ≠ 0 := by
      intro h; apply hx; simp [h]
    exact hadm.supp x this
  · have h1 : ContinuousAt (fun y : Space n => ‖y‖ * (muR n y * Real.exp (2 * τ * phiR ε y)))
        x := continuous_norm.continuousAt.mul (continuousAt_weight ε τ hx0)
    have h2 := h1.continuousWithinAt (s := {x : Space n | 0 ≤ vcoord x}).mul
      ((hadm.cont x hx).pow 2)
    refine h2.congr (fun y _ => ?_) ?_
    · simp only [Pi.mul_apply, Pi.pow_apply]
      ring
    · simp only [Pi.mul_apply, Pi.pow_apply]
      ring

theorem integrableOn_Y {ε τ rs δ : ℝ} {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) :
    IntegrableOn (fun x => ‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2) {x | 0 < vcoord x} := by
  refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => ?_) fun x hx hx0 => ?_
  · have : WC ε τ f Df x ≠ 0 := by
      intro h; apply hx; simp [h]
    exact WC_supp hadm x this
  · have h1 : ContinuousAt (fun y : Space n => ‖y‖ ^ 3 * muR n y) x :=
      (continuous_norm.continuousAt.pow 3).mul (continuousAt_muR hx0)
    exact h1.continuousWithinAt.mul ((continuousWithinAt_WC hadm hx hx0).norm.pow 2)

/-- The flux of the gradient identity, written with `W`: `μ ρ w B W`. -/
noncomputable def GFlux (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ)
    (Df : Space n → Space n) (y : Space n) : Space n :=
  (muR n y * ‖y‖ * wC ε τ f y) • BR S.A y (WC ε τ f Df y)

/-- **(GC1)** The pointwise gradient identity (`F2.carleman_gradient_pointwise` with `ϱ = ρ`),
rewritten with `∇w = W`, `∇ρ = x/ρ` and `S w = S' w + m² w`; the flux `GFlux` agrees with the
flux of `F2` near every point of the open half-space. -/
theorem gc_pointwise (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 < vcoord x) :
    ‖x‖ * muR n x * ⟪BR S.A x (WC ε τ f Df x), WC ε τ f Df x⟫_ℝ
      = -(SpC S ε τ f x * ‖x‖ * wC ε τ f x * muR n x)
        - mR n ^ 2 * (‖x‖ * muR n x * wC ε τ f x ^ 2)
        + τ ^ 2 * carlQ (BR S.A) (phiR ε) x * ‖x‖ * wC ε τ f x ^ 2 * muR n x
        - muR n x * wC ε τ f x * ⟪BR S.A x (WC ε τ f Df x), ‖x‖⁻¹ • x⟫_ℝ
        + divergence (GFlux S ε τ f Df) x := by
  have hx0 := ne_zero_of_vcoord_pos hx
  have hU : {x : Space n | 0 < vcoord x} ∈ 𝓝 x :=
    (isOpen_lt continuous_const F1.continuous_vcoord).mem_nhds hx
  have key := MazyaRefinedCauchy.carleman_gradient_pointwise (muR n) (BR S.A) (phiR ε) τ (wC ε τ f)
    (fun y => ‖y‖) x (contDiffAt_muR hx0) (muR_ne_zero hx0)
    ((contDiff_BR S).contDiffAt.of_le (by norm_num)) (contDiffAt_wC hadm hx)
    (contDiffAt_norm ℝ hx0)
  beta_reduce at key
  have hev : (fun y => (muR n y * ‖y‖ * wC ε τ f y) • BR S.A y (gradient (wC ε τ f) y))
      =ᶠ[𝓝 x] GFlux S ε τ f Df := by
    filter_upwards [hU] with y hy
    simp only [GFlux, gradient_wC hadm hy]
  rw [F2.divergence_congr hev, gradient_wC hadm hx, gradient_norm' hx0] at key
  have hS : carlS (muR n) (BR S.A) (phiR ε) τ (wC ε τ f) x
      = SpC S ε τ f x + mR n ^ 2 * wC ε τ f x := by
    simp only [SpC]; ring
  rw [hS] at key
  rw [key]
  ring

/-- **(GC2)** `div GFlux` is integrable on the open half-space (by `gc_pointwise` it is a sum of
integrable terms: use `integrableOn_SpC_sq`, `integrableOn_X`, `integrableOn_Y`, continuity of
`carlQ` away from `0`, and `|S'w ρ w μ| ≤ (μ S'w² + μ ρ² w²)/2`). -/
theorem gc_div_integrable (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) (hrsR : rs < S.R)
    (hPi : IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
      {x | 0 < vcoord x}) :
    IntegrableOn (divergence (GFlux S ε τ f Df)) {x | 0 < vcoord x} := by
  have hΩm : MeasurableSet {x : Space n | 0 < vcoord x} := F1.measurableSet_halfSpace 0
  have hSi := integrableOn_SpC_sq S hadm hPi
  have hwS : ∀ x, wC ε τ f x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs := wC_supp hadm
  have hWS : ∀ x, WC ε τ f Df x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs := WC_supp hadm
  -- T1 = ρ μ ⟪B W, W⟫
  have h1 : IntegrableOn
      (fun x => ‖x‖ * muR n x * ⟪BR S.A x (WC ε τ f Df x), WC ε τ f Df x⟫_ℝ)
      {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => hWS x ?_) fun x hx hx0 => ?_
    · intro h; apply hx; simp [h]
    · have hB := (contDiff_BR S).continuous.continuousAt (x := x)
      have hW := continuousWithinAt_WC (ε := ε) (τ := τ) hadm hx hx0
      exact ((continuous_norm.continuousAt.mul (continuousAt_muR hx0)).continuousWithinAt).mul
        ((hB.continuousWithinAt.clm_apply hW).inner hW)
  -- T3 = m² ρ μ w²
  have hw2 : IntegrableOn (fun x => ‖x‖ * muR n x * wC ε τ f x ^ 2) {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => hwS x ?_) fun x hx hx0 => ?_
    · intro h; apply hx; simp [h]
    · exact ((continuous_norm.continuousAt.mul (continuousAt_muR hx0)).continuousWithinAt).mul
        ((continuousWithinAt_wC hadm hx hx0).pow 2)
  have h3 : IntegrableOn (fun x => mR n ^ 2 * (‖x‖ * muR n x * wC ε τ f x ^ 2))
      {x | 0 < vcoord x} := hw2.const_mul _
  -- T4 = τ² q ρ w² μ
  have h4 : IntegrableOn
      (fun x => τ ^ 2 * carlQ (BR S.A) (phiR ε) x * ‖x‖ * wC ε τ f x ^ 2 * muR n x)
      {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => hwS x ?_) fun x hx hx0 => ?_
    · intro h; apply hx; simp [h]
    · have hg : ContinuousAt (gradient (phiR ε)) x :=
        (F2.contDiffAt_gradient (m := 0) (contDiffAt_phiR ε hx0 (k := 1)) (by norm_num)).continuousAt
      have hq : ContinuousAt (carlQ (BR S.A) (phiR ε)) x :=
        ((contDiff_BR S).continuous.continuousAt.clm_apply hg).inner hg
      exact ((((continuousAt_const.mul hq).mul continuous_norm.continuousAt).continuousWithinAt).mul
        ((continuousWithinAt_wC hadm hx hx0).pow 2)).mul (continuousAt_muR hx0).continuousWithinAt
  -- T5 = μ w ⟪B W, x / ρ⟫
  have h5 : IntegrableOn
      (fun x => muR n x * wC ε τ f x * ⟪BR S.A x (WC ε τ f Df x), ‖x‖⁻¹ • x⟫_ℝ)
      {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => hwS x ?_) fun x hx hx0 => ?_
    · intro h; apply hx; simp [h]
    · have hB := (contDiff_BR S).continuous.continuousAt (x := x)
      have hW := continuousWithinAt_WC (ε := ε) (τ := τ) hadm hx hx0
      have hx' : ContinuousAt (fun y : Space n => ‖y‖⁻¹ • y) x :=
        (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.2 hx0)).smul continuousAt_id
      exact ((continuousAt_muR hx0).continuousWithinAt.mul (continuousWithinAt_wC hadm hx hx0)).mul
        ((hB.continuousWithinAt.clm_apply hW).inner hx'.continuousWithinAt)
  -- T2 = S'w ρ w μ, dominated by `(μ S'w² + ρ² μ w²) / 2`
  have hρ2 : IntegrableOn (fun x => ‖x‖ ^ 2 * muR n x * wC ε τ f x ^ 2) {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => hwS x ?_) fun x hx hx0 => ?_
    · intro h; apply hx; simp [h]
    · exact (((continuous_norm.continuousAt.pow 2).mul (continuousAt_muR hx0)).continuousWithinAt).mul
        ((continuousWithinAt_wC hadm hx hx0).pow 2)
  have hSc : ContinuousOn (SpC S ε τ f) {x | 0 < vcoord x} := by
    intro x hx
    have hx0 := ne_zero_of_vcoord_pos hx
    have hid : ∀ y ∈ {x : Space n | 0 < vcoord x},
        SpC S ε τ f y = Real.exp (τ * phiR ε y) * P0R S.A f y - TWC S ε τ f Df y := by
      intro y hy
      rw [conj_eq S ε τ hadm hy, carlT_eq S hadm hy]
      ring
    have h1 : ContinuousWithinAt
        (fun y => Real.exp (τ * phiR ε y) * P0R S.A f y - TWC S ε τ f Df y)
        {x | 0 < vcoord x} x :=
      ((continuousAt_expPhi ε τ hx0).continuousWithinAt.mul
        (continuousOn_P0R S hadm.c2 x hx)).sub
        ((continuousWithinAt_TWC S hadm (le_of_lt hx) hx0).mono
          fun y (hy : 0 < vcoord y) => (le_of_lt hy : 0 ≤ vcoord y))
    exact h1.congr (fun y hy => hid y hy) (hid x hx)
  have h2 : IntegrableOn (fun x => SpC S ε τ f x * ‖x‖ * wC ε τ f x * muR n x)
      {x | 0 < vcoord x} := by
    have hdom : IntegrableOn (fun x => muR n x * SpC S ε τ f x ^ 2
        + ‖x‖ ^ 2 * muR n x * wC ε τ f x ^ 2) {x | 0 < vcoord x} := hSi.add hρ2
    have hmeas : ContinuousOn (fun x => SpC S ε τ f x * ‖x‖ * wC ε τ f x * muR n x)
        {x | 0 < vcoord x} := by
      intro x hx
      have hx0 := ne_zero_of_vcoord_pos hx
      exact (((hSc x hx).mul continuous_norm.continuousAt.continuousWithinAt).mul
        ((continuousWithinAt_wC hadm (le_of_lt hx) hx0).mono
          fun y (hy : 0 < vcoord y) => (le_of_lt hy : 0 ≤ vcoord y))).mul
        (continuousAt_muR hx0).continuousWithinAt
    refine Integrable.mono' hdom (hmeas.aestronglyMeasurable hΩm) ?_
    refine (ae_restrict_iff' hΩm).2 (Eventually.of_forall fun x _ => ?_)
    have hμ := muR_nonneg x
    rw [Real.norm_eq_abs]
    have e : |SpC S ε τ f x * ‖x‖ * wC ε τ f x * muR n x|
        = muR n x * (|SpC S ε τ f x| * |‖x‖ * wC ε τ f x|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hμ, abs_of_nonneg (norm_nonneg x)]
      ring
    rw [e]
    have h0 : |SpC S ε τ f x| * |‖x‖ * wC ε τ f x|
        ≤ SpC S ε τ f x ^ 2 + (‖x‖ * wC ε τ f x) ^ 2 := by
      nlinarith [sq_nonneg (|SpC S ε τ f x| - |‖x‖ * wC ε τ f x|), sq_abs (SpC S ε τ f x),
        sq_abs (‖x‖ * wC ε τ f x)]
    have h6 := mul_le_mul_of_nonneg_left h0 hμ
    calc muR n x * (|SpC S ε τ f x| * |‖x‖ * wC ε τ f x|)
        ≤ muR n x * (SpC S ε τ f x ^ 2 + (‖x‖ * wC ε τ f x) ^ 2) := h6
      _ = muR n x * SpC S ε τ f x ^ 2 + ‖x‖ ^ 2 * muR n x * wC ε τ f x ^ 2 := by ring
  -- assemble
  have hsum : IntegrableOn (fun x =>
      ‖x‖ * muR n x * ⟪BR S.A x (WC ε τ f Df x), WC ε τ f Df x⟫_ℝ
        + SpC S ε τ f x * ‖x‖ * wC ε τ f x * muR n x
        + mR n ^ 2 * (‖x‖ * muR n x * wC ε τ f x ^ 2)
        - τ ^ 2 * carlQ (BR S.A) (phiR ε) x * ‖x‖ * wC ε τ f x ^ 2 * muR n x
        + muR n x * wC ε τ f x * ⟪BR S.A x (WC ε τ f Df x), ‖x‖⁻¹ • x⟫_ℝ)
      {x | 0 < vcoord x} := (((h1.add h2).add h3).sub h4).add h5
  refine hsum.congr_fun (fun x hx => ?_) hΩm
  have := gc_pointwise S (ε := ε) (τ := τ) hadm hx
  simp only
  linarith

/-- **(GC3)** The boundary term: by `F1.integral_divergence_halfSpace_of_continuousOn`,
`∫ div GFlux = -∫ ⟪GFlux (lift y 0), e_d⟫`, and on `t = 0`,
`⟪GFlux, e_d⟫ = ρ³ μ e^{2τφ} f ⟪A Df, e_d⟫` (`inner_BR_WC_ed`), bounded by the integrand of
`IBd` since `ρ ≤ rs ≤ 1` on the support. -/
theorem gc_boundary (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) (hrsR : rs < S.R) (hrs1 : rs ≤ 1)
    (hPi : IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
      {x | 0 < vcoord x}) :
    ∫ x in {x : Space n | 0 < vcoord x}, divergence (GFlux S ε τ f Df) x ≤ IBd S ε τ f Df := by
  have hf0 : ∀ y : Space n, ‖y‖ < δ → f y = 0 := fun y hy => by
    by_contra h
    have := (hadm.supp y h).1
    linarith
  have hf0' : ∀ y : Space n, rs < ‖y‖ → f y = 0 := fun y hy => by
    by_contra h
    have := (hadm.supp y h).2
    linarith
  -- regularity of the flux
  have hC1 : ∀ x, 0 < vcoord x → ContDiffAt ℝ 1 (GFlux S ε τ f Df) x := by
    intro x hx
    have hx0 := ne_zero_of_vcoord_pos hx
    have hU : {x : Space n | 0 < vcoord x} ∈ 𝓝 x :=
      (isOpen_lt continuous_const F1.continuous_vcoord).mem_nhds hx
    have hev : GFlux S ε τ f Df =ᶠ[𝓝 x]
        fun y => (muR n y * ‖y‖ * wC ε τ f y) • BR S.A y (gradient (wC ε τ f) y) := by
      filter_upwards [hU] with y hy
      simp only [GFlux, gradient_wC hadm hy]
    have h1 : ContDiffAt ℝ 1
        (fun y => (muR n y * ‖y‖ * wC ε τ f y) • BR S.A y (gradient (wC ε τ f) y)) x :=
      (((contDiffAt_muR hx0).mul (contDiffAt_norm ℝ hx0)).mul
        ((contDiffAt_wC hadm hx).of_le (by norm_num))).smul
        (((contDiff_BR S).contDiffAt.of_le (by norm_num)).clm_apply
          (F2.contDiffAt_gradient (m := 1) (contDiffAt_wC hadm hx) (by norm_num)))
    exact h1.congr_of_eventuallyEq hev
  have hcont : ContinuousOn (GFlux S ε τ f Df) {x | 0 ≤ vcoord x} := by
    intro x hx
    by_cases hx0 : x = 0
    · have hev : GFlux S ε τ f Df =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds x hadm.pos] with y hy
        rw [Metric.mem_ball, hx0, dist_zero_right] at hy
        simp [GFlux, wC, hf0 y hy]
      exact (continuousAt_const.congr hev.symm).continuousWithinAt
    · exact ((((continuousAt_muR hx0).mul continuous_norm.continuousAt).continuousWithinAt.mul
        (continuousWithinAt_wC hadm hx hx0)).smul
        ((contDiff_BR S).continuous.continuousAt.continuousWithinAt.clm_apply
          (continuousWithinAt_WC hadm hx hx0)))
  have hsupp : HasCompactSupport (GFlux S ε τ f Df) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space n) rs) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    simp [GFlux, wC, hf0' y hy]
  have hIBP := integral_divergence_halfSpace_of_continuousOn (GFlux S ε τ f Df) hC1 hcont hsupp
    (gc_div_integrable S hadm hrsR hPi)
  rw [hIBP]
  -- the boundary integrand is bounded by that of `IBd`
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    ‖lift y 0‖ ^ 2 * muR n (lift y 0) * Real.exp (2 * τ * phiR ε (lift y 0)) *
      (|⟪S.A (lift y 0) (Df (lift y 0)), ed n⟫_ℝ| *
        (‖lift y 0‖ * ‖Df (lift y 0)‖ + |f (lift y 0)|)) with hg
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n), ‖⟪GFlux S ε τ f Df (lift y 0), ed n⟫_ℝ‖ ≤ g y := by
    intro y
    set x := lift y 0 with hxd
    have hμ := muR_nonneg x
    have hg0 : 0 ≤ g y := by
      simp only [hg]
      positivity
    by_cases hfx : f x = 0
    · have : GFlux S ε τ f Df x = 0 := by simp [GFlux, wC, hfx]
      rw [this, inner_zero_left, norm_zero]
      exact hg0
    · obtain ⟨hδx, hxr⟩ := hadm.supp x hfx
      have hx0 : x ≠ 0 := by
        intro h; rw [h, norm_zero] at hδx; linarith [hadm.pos]
      have hxf : x ∈ flatPiece n S.R := ⟨by linarith, by rw [hxd, vcoord_lift]⟩
      have hρ1 : ‖x‖ ≤ 1 := hxr.trans hrs1
      have hinner : ⟪GFlux S ε τ f Df x, ed n⟫_ℝ
          = muR n x * ‖x‖ * wC ε τ f x
            * (‖x‖ ^ 2 * Real.exp (τ * phiR ε x) * ⟪S.A x (Df x), ed n⟫_ℝ) := by
        rw [← inner_BR_WC_ed S ε τ f Df hx0 hxf]
        simp only [GFlux, real_inner_smul_left]
      have hE2 : Real.exp (2 * τ * phiR ε x) = Real.exp (τ * phiR ε x) * Real.exp (τ * phiR ε x) := by
        rw [← Real.exp_add]; ring_nf
      have hE0 : 0 < Real.exp (τ * phiR ε x) := Real.exp_pos _
      obtain ⟨E, hEd⟩ : ∃ e, e = Real.exp (τ * phiR ε x) := ⟨_, rfl⟩
      obtain ⟨Ai, hAid⟩ : ∃ a, a = ⟪S.A x (Df x), ed n⟫_ℝ := ⟨_, rfl⟩
      have hE0' : 0 ≤ E := by rw [hEd]; exact hE0.le
      have hinner' : ⟪GFlux S ε τ f Df x, ed n⟫_ℝ
          = (‖x‖ ^ 2 * muR n x * (E * E)) * (‖x‖ * (f x * Ai)) := by
        rw [hinner, hEd, hAid]; simp only [wC]; ring
      have hgy : g y = (‖x‖ ^ 2 * muR n x * (E * E)) * (|Ai| * (‖x‖ * ‖Df x‖ + |f x|)) := by
        simp only [hg]
        rw [← hxd, hE2, ← hEd, ← hAid]
      have hfac : 0 ≤ ‖x‖ ^ 2 * muR n x * (E * E) := by positivity
      rw [hinner', hgy, Real.norm_eq_abs, abs_mul, abs_of_nonneg hfac, abs_mul,
        abs_of_nonneg (norm_nonneg x), abs_mul]
      apply mul_le_mul_of_nonneg_left _ hfac
      have hf1 : ‖x‖ * |f x| ≤ ‖x‖ * ‖Df x‖ + |f x| := by
        have : ‖x‖ * |f x| ≤ 1 * |f x| := mul_le_mul_of_nonneg_right hρ1 (abs_nonneg _)
        have : 0 ≤ ‖x‖ * ‖Df x‖ := by positivity
        linarith
      have hA0 := abs_nonneg Ai
      calc ‖x‖ * (|f x| * |Ai|) = |Ai| * (‖x‖ * |f x|) := by ring
        _ ≤ |Ai| * (‖x‖ * ‖Df x‖ + |f x|) := mul_le_mul_of_nonneg_left hf1 hA0
  -- integrability of `g`
  have hgi : Integrable g := by
    have hl : Continuous (fun z : EuclideanSpace ℝ (Fin n) => lift z 0) := F1.continuous_lift_left 0
    have hmem : ∀ z : EuclideanSpace ℝ (Fin n), lift z 0 ∈ {x : Space n | 0 ≤ vcoord x} :=
      fun z => by simp [vcoord_lift]
    have hDf0 : ∀ y : Space n, ‖y‖ < δ → Df y = 0 := fun y hy => by
      by_contra h
      have := (hadm.Dsupp y h).1
      linarith
    have hDf0' : ∀ y : Space n, rs < ‖y‖ → Df y = 0 := fun y hy => by
      by_contra h
      have := (hadm.Dsupp y h).2
      linarith
    have hgc : Continuous g := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : ‖y‖ < δ
      · have hev : g =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
          have hz' : ‖lift z 0‖ < δ := by rw [norm_lift_zero]; exact hz
          simp [hg, hf0 _ hz', hDf0 _ hz']
        exact continuousAt_const.congr hev.symm
      · push Not at hy
        have hx0 : lift y 0 ≠ 0 := by
          intro h
          have := norm_lift_zero y
          rw [h, norm_zero] at this
          linarith [hadm.pos]
        have hfc : ContinuousAt (fun z => f (lift z 0)) y :=
          (hadm.cont.comp_continuous hl hmem).continuousAt
        have hDfc : ContinuousAt (fun z => Df (lift z 0)) y :=
          (hadm.Dcont.comp_continuous hl hmem).continuousAt
        have hμ : ContinuousAt (fun z => muR n (lift z 0)) y :=
          ContinuousAt.comp (g := muR n) (f := fun z : EuclideanSpace ℝ (Fin n) => lift z 0)
            (x := y) (continuousAt_muR hx0) hl.continuousAt
        have hφ : ContinuousAt (fun z => Real.exp (2 * τ * phiR ε (lift z 0))) y :=
          Real.continuous_exp.continuousAt.comp
            (continuousAt_const.mul (ContinuousAt.comp (g := phiR ε)
              (f := fun z : EuclideanSpace ℝ (Fin n) => lift z 0) (x := y)
              (continuousAt_phiR ε hx0) hl.continuousAt))
        have hA : ContinuousAt (fun z => S.A (lift z 0)) y :=
          S.coeffs.contDiff_A.continuous.continuousAt.comp hl.continuousAt
        exact (((hl.norm.continuousAt.pow 2).mul hμ).mul hφ).mul
          (((hA.clm_apply hDfc).inner continuousAt_const).abs.mul
            ((hl.norm.continuousAt.mul hDfc.norm).add hfc.abs))
    have hgs : HasCompactSupport g := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) rs)
        fun y hy => ?_
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      have hy' : rs < ‖lift y 0‖ := by rw [norm_lift_zero]; exact hy
      simp [hg, hf0' _ hy', hDf0' _ hy']
    exact hgc.integrable_of_hasCompactSupport hgs
  have h1 := norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)
  have h2 : -(∫ y : EuclideanSpace ℝ (Fin n), ⟪GFlux S ε τ f Df (lift y 0), ed n⟫_ℝ)
      ≤ ‖∫ y : EuclideanSpace ℝ (Fin n), ⟪GFlux S ε τ f Df (lift y 0), ed n⟫_ℝ‖ := by
    rw [Real.norm_eq_abs]; exact neg_le_abs _
  exact h2.trans h1

/-- `q ≤ K (1 - ερ)²` away from `0`. -/
theorem carlQ_le (S : HalfBallSolution n) (ε : ℝ) {x : Space n} (hx0 : x ≠ 0) :
    carlQ (BR S.A) (phiR ε) x ≤ S.K * (1 - ε * ‖x‖) ^ 2 := by
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hg : ‖x‖ ^ 2 * ‖gradPhi ε x‖ ^ 2 = (1 - ε * ‖x‖) ^ 2 := by
    have e : gradPhi ε x = (-(1 - ε * ‖x‖) / ‖x‖ ^ 2) • x := rfl
    rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  have hA : ⟪S.A x (gradPhi ε x), gradPhi ε x⟫_ℝ ≤ S.K * ‖gradPhi ε x‖ ^ 2 := by
    calc ⟪S.A x (gradPhi ε x), gradPhi ε x⟫_ℝ ≤ ‖S.A x (gradPhi ε x)‖ * ‖gradPhi ε x‖ :=
          real_inner_le_norm _ _
      _ ≤ (S.K * ‖gradPhi ε x‖) * ‖gradPhi ε x‖ := by
          gcongr
          exact ((S.A x).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (S.coeffs.bound_A x) (norm_nonneg _))
      _ = S.K * ‖gradPhi ε x‖ ^ 2 := by ring
  simp only [carlQ, gradient_phiR ε hx0, BR, ContinuousLinearMap.smul_apply, real_inner_smul_left]
  calc ‖x‖ ^ 2 * ⟪S.A x (gradPhi ε x), gradPhi ε x⟫_ℝ ≤ ‖x‖ ^ 2 * (S.K * ‖gradPhi ε x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = S.K * (‖x‖ ^ 2 * ‖gradPhi ε x‖ ^ 2) := by ring
    _ = S.K * (1 - ε * ‖x‖) ^ 2 := by rw [hg]

/-- **(GC4)** The pointwise inequality behind `grad_control`, from `gc_pointwise`:
`⟪B W, W⟫ ≥ λ ρ² |W|²`, `q ≤ K` (`q = (1-ερ)² ⟪A x, x⟫/ρ²`), `|⟪B W, x/ρ⟫| ≤ K ρ |W|`,
Young's inequality, and `ρ ≤ rs ≤ 1` on the support. -/
theorem gc_pointwise_bound (S : HalfBallSolution n) {ε τ rs δ : ℝ} (hε : 0 < ε)
    (hrs1 : rs ≤ 1) (hεrs : ε * rs ≤ 1 / 4) {f : Space n → ℝ} {Df : Space n → Space n}
    (hadm : Admissible rs δ f Df) {c : ℝ} (hc : 0 < c) {x : Space n} (hx : 0 < vcoord x) :
    S.lam * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
      ≤ 1 / (2 * c) * (muR n x * SpC S ε τ f x ^ 2)
        + (c / 2 + S.K * τ ^ 2 + S.K ^ 2 / (2 * S.lam))
          * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
        + S.lam / 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
        + divergence (GFlux S ε τ f Df) x := by
  have hx0 := ne_zero_of_vcoord_pos hx
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hμ := muR_nonneg x
  have hlam : 0 < S.lam := S.coeffs.lam_pos
  have hK : 0 ≤ S.K := le_trans (norm_nonneg _) (S.coeffs.bound_A 0)
  have hid := gc_pointwise S (ε := ε) (τ := τ) hadm hx
  obtain ⟨ρ, hρd⟩ : ∃ r, r = ‖x‖ := ⟨_, rfl⟩
  obtain ⟨μ, hμd⟩ : ∃ m, m = muR n x := ⟨_, rfl⟩
  obtain ⟨Wn, hWn⟩ : ∃ m, m = ‖WC ε τ f Df x‖ := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ m, m = wC ε τ f x := ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ m, m = SpC S ε τ f x := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ m, m = carlQ (BR S.A) (phiR ε) x := ⟨_, rfl⟩
  obtain ⟨Ib, hIbd⟩ : ∃ m, m = ⟪BR S.A x (WC ε τ f Df x), WC ε τ f Df x⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨Ix, hIxd⟩ : ∃ m, m = ⟪BR S.A x (WC ε τ f Df x), ‖x‖⁻¹ • x⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨Dv, hDvd⟩ : ∃ m, m = divergence (GFlux S ε τ f Df) x := ⟨_, rfl⟩
  obtain ⟨E2, hE2d⟩ : ∃ m, m = Real.exp (2 * τ * phiR ε x) := ⟨_, rfl⟩
  rw [← hIbd, ← hIxd, ← hDvd, ← hsd, ← hqd, ← hwd, ← hμd, ← hρd] at hid
  rw [← hWn, ← hsd, ← hDvd, ← hE2d, ← hμd, ← hρd]
  have hρ0 : 0 ≤ ρ := by rw [hρd]; exact hρ.le
  have hμ0 : 0 ≤ μ := by rw [hμd]; exact hμ
  have hWn0 : 0 ≤ Wn := by rw [hWn]; exact norm_nonneg _
  -- `w² = e^{2τφ} f²`
  have hw2 : w ^ 2 = E2 * f x ^ 2 := by
    rw [hwd, hE2d, wC, mul_pow, sq, ← Real.exp_add]; ring_nf
  -- `⟪B W, W⟫ ≥ λ ρ² |W|²`
  have hIb : S.lam * ρ ^ 2 * Wn ^ 2 ≤ Ib := by
    have := S.coeffs.ell x (WC ε τ f Df x)
    rw [hIbd, hρd, hWn]
    simp only [BR, ContinuousLinearMap.smul_apply, real_inner_smul_left]
    nlinarith [sq_nonneg ‖x‖]
  -- `|⟪B W, x/ρ⟫| ≤ K ρ² |W|`
  have hIx : |Ix| ≤ S.K * ρ ^ 2 * Wn := by
    have e : Ix = ‖x‖ ^ 2 * ‖x‖⁻¹ * ⟪S.A x (WC ε τ f Df x), x⟫_ℝ := by
      rw [hIxd]
      simp only [BR, ContinuousLinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right]
      ring
    have h1 : |⟪S.A x (WC ε τ f Df x), x⟫_ℝ| ≤ S.K * ‖WC ε τ f Df x‖ * ‖x‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (((S.A x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (S.coeffs.bound_A x) (norm_nonneg _))) (norm_nonneg _))
    have h2 : 0 ≤ ‖x‖ ^ 2 * ‖x‖⁻¹ := by positivity
    rw [e, abs_mul, abs_of_nonneg h2, hρd, hWn]
    calc ‖x‖ ^ 2 * ‖x‖⁻¹ * |⟪S.A x (WC ε τ f Df x), x⟫_ℝ|
        ≤ ‖x‖ ^ 2 * ‖x‖⁻¹ * (S.K * ‖WC ε τ f Df x‖ * ‖x‖) := mul_le_mul_of_nonneg_left h1 h2
      _ = S.K * ‖x‖ ^ 2 * ‖WC ε τ f Df x‖ := by field_simp
  -- `q w² ≤ K w²` and `ρ² w² ≤ ρ w²`
  have hqw : q * w ^ 2 ≤ S.K * w ^ 2 := by
    by_cases hf : f x = 0
    · have : w = 0 := by rw [hwd, wC, hf, mul_zero]
      rw [this]; simp
    · have hxr : ‖x‖ ≤ rs := (hadm.supp x hf).2
      have hερ : ε * ‖x‖ ≤ 1 / 4 := le_trans (mul_le_mul_of_nonneg_left hxr hε.le) hεrs
      have hερ0 : 0 ≤ ε * ‖x‖ := mul_nonneg hε.le hρ.le
      have h1 : (1 - ε * ‖x‖) ^ 2 ≤ 1 := by nlinarith
      have h2 : q ≤ S.K := by
        rw [hqd]
        refine (carlQ_le S ε hx0).trans ?_
        calc S.K * (1 - ε * ‖x‖) ^ 2 ≤ S.K * 1 := mul_le_mul_of_nonneg_left h1 hK
          _ = S.K := mul_one _
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hρw : ρ ^ 2 * w ^ 2 ≤ ρ * w ^ 2 := by
    by_cases hf : f x = 0
    · have : w = 0 := by rw [hwd, wC, hf, mul_zero]
      rw [this]; simp
    · have hxr : ρ ≤ 1 := by rw [hρd]; exact (hadm.supp x hf).2.trans hrs1
      have : ρ ^ 2 ≤ ρ := by
        calc ρ ^ 2 = ρ * ρ := sq ρ
          _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hxr hρ0
          _ = ρ := mul_one ρ
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  -- the individual bounds
  have p1 : S.lam * (ρ ^ 3 * μ * Wn ^ 2) ≤ ρ * μ * Ib := by
    have h := mul_le_mul_of_nonneg_left hIb (mul_nonneg hρ0 hμ0)
    calc S.lam * (ρ ^ 3 * μ * Wn ^ 2) = ρ * μ * (S.lam * ρ ^ 2 * Wn ^ 2) := by ring
      _ ≤ ρ * μ * Ib := h
  have p2 : -(s * ρ * w * μ) ≤ 1 / (2 * c) * (μ * s ^ 2) + c / 2 * (μ * (ρ ^ 2 * w ^ 2)) := by
    have hsq : 0 ≤ 1 / (2 * c) * (s + c * (ρ * w)) ^ 2 := by positivity
    have e : 1 / (2 * c) * (s + c * (ρ * w)) ^ 2
        = 1 / (2 * c) * s ^ 2 + s * (ρ * w) + c / 2 * (ρ ^ 2 * w ^ 2) := by
      field_simp; ring
    have h3 : -(s * (ρ * w)) ≤ 1 / (2 * c) * s ^ 2 + c / 2 * (ρ ^ 2 * w ^ 2) := by
      linarith only [hsq, e]
    have h4 := mul_le_mul_of_nonneg_left h3 hμ0
    calc -(s * ρ * w * μ) = μ * -(s * (ρ * w)) := by ring
      _ ≤ μ * (1 / (2 * c) * s ^ 2 + c / 2 * (ρ ^ 2 * w ^ 2)) := h4
      _ = 1 / (2 * c) * (μ * s ^ 2) + c / 2 * (μ * (ρ ^ 2 * w ^ 2)) := by ring
  have p3 : 0 ≤ mR n ^ 2 * (ρ * μ * w ^ 2) := by positivity
  have p4 : τ ^ 2 * q * ρ * w ^ 2 * μ ≤ S.K * τ ^ 2 * (ρ * μ * w ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hqw (by positivity : (0 : ℝ) ≤ τ ^ 2 * ρ * μ)
    calc τ ^ 2 * q * ρ * w ^ 2 * μ = τ ^ 2 * ρ * μ * (q * w ^ 2) := by ring
      _ ≤ τ ^ 2 * ρ * μ * (S.K * w ^ 2) := h
      _ = S.K * τ ^ 2 * (ρ * μ * w ^ 2) := by ring
  have p5 : -(μ * w * Ix)
      ≤ S.lam / 2 * (ρ ^ 3 * μ * Wn ^ 2) + S.K ^ 2 / (2 * S.lam) * (ρ * μ * w ^ 2) := by
    have h1 : -(w * Ix) ≤ |w| * (S.K * ρ ^ 2 * Wn) := by
      have : -(w * Ix) ≤ |w * Ix| := neg_le_abs _
      rw [abs_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left hIx (abs_nonneg _))
    have h2 : |w| * (S.K * ρ ^ 2 * Wn)
        ≤ S.lam / 2 * (ρ ^ 3 * Wn ^ 2) + S.K ^ 2 / (2 * S.lam) * (ρ * w ^ 2) := by
      have hsq : 0 ≤ ρ / (2 * S.lam) * (S.lam * ρ * Wn - S.K * |w|) ^ 2 := by positivity
      have e : ρ / (2 * S.lam) * (S.lam * ρ * Wn - S.K * |w|) ^ 2
          = S.lam / 2 * (ρ ^ 3 * Wn ^ 2) - |w| * (S.K * ρ ^ 2 * Wn)
            + S.K ^ 2 / (2 * S.lam) * (ρ * |w| ^ 2) := by
        field_simp; ring
      rw [sq_abs] at e
      linarith only [hsq, e]
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hμ0
    calc -(μ * w * Ix) = μ * -(w * Ix) := by ring
      _ ≤ μ * (S.lam / 2 * (ρ ^ 3 * Wn ^ 2) + S.K ^ 2 / (2 * S.lam) * (ρ * w ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hμ0 |>.trans
            (mul_le_mul_of_nonneg_left h2 hμ0)
      _ = S.lam / 2 * (ρ ^ 3 * μ * Wn ^ 2) + S.K ^ 2 / (2 * S.lam) * (ρ * μ * w ^ 2) := by ring
  have hE : ρ * μ * w ^ 2 = ρ * μ * E2 * f x ^ 2 := by rw [hw2]; ring
  have hE' : μ * (ρ ^ 2 * w ^ 2) ≤ ρ * μ * E2 * f x ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hρw hμ0
    calc μ * (ρ ^ 2 * w ^ 2) ≤ μ * (ρ * w ^ 2) := h
      _ = ρ * μ * w ^ 2 := by ring
      _ = ρ * μ * E2 * f x ^ 2 := hE
  have hc2 : c / 2 * (μ * (ρ ^ 2 * w ^ 2)) ≤ c / 2 * (ρ * μ * E2 * f x ^ 2) :=
    mul_le_mul_of_nonneg_left hE' (by positivity)
  have e1 : (c / 2 + S.K * τ ^ 2 + S.K ^ 2 / (2 * S.lam)) * (ρ * μ * E2 * f x ^ 2)
      = c / 2 * (ρ * μ * E2 * f x ^ 2) + S.K * τ ^ 2 * (ρ * μ * E2 * f x ^ 2)
        + S.K ^ 2 / (2 * S.lam) * (ρ * μ * E2 * f x ^ 2) := by ring
  rw [hE] at p4 p5 p3 hid
  rw [e1]
  linarith only [hid, p1, p2, p3, p4, p5, hc2]

/-- The real-number step of `grad_control`. -/
theorem gc_algebra {lam K c τ Y X Sg D Bd : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (h : lam * Y ≤ 1 / (2 * c) * Sg + (c / 2 + K * τ ^ 2 + K ^ 2 / (2 * lam)) * X
      + lam / 2 * Y + D) (hD : D ≤ Bd) :
    c * lam * Y ≤ Sg + c ^ 2 * X + 2 * c * K * τ ^ 2 * X + c * K ^ 2 / lam * X + 2 * c * Bd := by
  have h1 : lam / 2 * Y ≤ 1 / (2 * c) * Sg + (c / 2 + K * τ ^ 2 + K ^ 2 / (2 * lam)) * X + Bd := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * c)
  have e1 : 2 * c * (lam / 2 * Y) = c * lam * Y := by ring
  have e2 : 2 * c * (1 / (2 * c) * Sg + (c / 2 + K * τ ^ 2 + K ^ 2 / (2 * lam)) * X + Bd)
      = Sg + c ^ 2 * X + 2 * c * K * τ ^ 2 * X + c * K ^ 2 / lam * X + 2 * c * Bd := by
    field_simp
    ring
  rw [e1, e2] at h2
  exact h2


/-! ### Pieces of `main_lower` (all still to be proved, see the docstrings) -/

/-- The integrand `carlJ`, as a function of the values `w(x) = wv` and `∇w(x) = W`
(so `carlJ μ B φ τ w x = carlJW S ε τ (w x) (∇w x) x` by definition). -/
noncomputable def carlJW (S : HalfBallSolution n) (ε τ wv : ℝ) (W : Space n) (x : Space n) : ℝ :=
  muR n x * (2 * τ ^ 3 * ⟪carlV (BR S.A) (phiR ε) x, gradient (carlQ (BR S.A) (phiR ε)) x⟫_ℝ
      * wv ^ 2
    + 4 * τ * ⟪fderiv ℝ (carlV (BR S.A) (phiR ε)) x (BR S.A x W), W⟫_ℝ
    - 2 * τ * ⟪fderiv ℝ (BR S.A) x (carlV (BR S.A) (phiR ε) x) W, W⟫_ℝ
    + 2 * τ * wv * ⟪BR S.A x W, gradient (divMu (muR n) (carlV (BR S.A) (phiR ε))) x⟫_ℝ)

/-- The flux `carlFlux`, written with `W` (continuous up to `t = 0`). -/
noncomputable def CFlux (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ)
    (Df : Space n → Space n) (y : Space n) : Space n :=
  muR n y • ((-4 * τ * ⟪carlV (BR S.A) (phiR ε) y, WC ε τ f Df y⟫_ℝ) • BR S.A y (WC ε τ f Df y)
    + (2 * τ * ⟪BR S.A y (WC ε τ f Df y), WC ε τ f Df y⟫_ℝ) • carlV (BR S.A) (phiR ε) y
    - (2 * τ * divMu (muR n) (carlV (BR S.A) (phiR ε)) y * wC ε τ f y)
        • BR S.A y (WC ε τ f Df y)
    - (2 * τ ^ 3 * carlQ (BR S.A) (phiR ε) y * wC ε τ f y ^ 2) • carlV (BR S.A) (phiR ε) y)

/-- The flux `w² μ V` of the `m²` term. -/
noncomputable def MFlux (S : HalfBallSolution n) (ε τ : ℝ) (f : Space n → ℝ) (y : Space n) :
    Space n :=
  (wC ε τ f y ^ 2 * muR n y) • carlV (BR S.A) (phiR ε) y

/-- **(ML1)** The pointwise identity: `F2.carleman_pointwise` (with `hsymm` from `BR_symm`,
`C³` weights away from `0`, `C²` of `BR`) gives `2 S w T w μ = carlJ + div carlFlux`; with
`S w = S'w + m² w`, `∇w = W` (`gradient_wC`, the fluxes agree near `x`), and
`w T w μ = -τ div(w² μ V)` (product rule: `div(w² μ V) = w² div(μ V) + 2 w μ ⟪∇w, V⟫`). -/
theorem ml_pointwise (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 < vcoord x) :
    muR n x * (SpC S ε τ f x + TWC S ε τ f Df x) ^ 2
      = muR n x * SpC S ε τ f x ^ 2 + muR n x * TWC S ε τ f Df x ^ 2
        + carlJW S ε τ (wC ε τ f x) (WC ε τ f Df x) x
        + divergence (CFlux S ε τ f Df) x
        + 2 * mR n ^ 2 * τ * divergence (MFlux S ε τ f) x := by
  have hx0 := ne_zero_of_vcoord_pos hx
  have hU : {x : Space n | 0 < vcoord x} ∈ 𝓝 x :=
    (isOpen_lt continuous_const F1.continuous_vcoord).mem_nhds hx
  have hw2 := contDiffAt_wC (ε := ε) (τ := τ) hadm hx
  -- `2 S w T w μ = carlJ + div carlFlux`
  have key := MazyaRefinedCauchy.carleman_pointwise (muR n) (BR S.A) (phiR ε) τ (wC ε τ f) x
    (contDiffAt_muR hx0) (muR_ne_zero hx0) (contDiff_BR S).contDiffAt (BR_symm S)
    (contDiffAt_phiR ε hx0) hw2
  have hev : carlFlux (muR n) (BR S.A) (phiR ε) τ (wC ε τ f) =ᶠ[𝓝 x] CFlux S ε τ f Df := by
    filter_upwards [hU] with y hy
    simp only [carlFlux, CFlux, gradient_wC hadm hy]
  rw [F2.divergence_congr hev] at key
  have hJ : carlJ (muR n) (BR S.A) (phiR ε) τ (wC ε τ f) x
      = carlJW S ε τ (wC ε τ f x) (WC ε τ f Df x) x := by
    simp only [carlJ, carlJW, gradient_wC hadm hx]
  rw [hJ, carlT_eq S hadm hx] at key
  -- `w T w μ = -τ div(w² μ V)`
  have hM : divergence (MFlux S ε τ f) x
      = wC ε τ f x ^ 2 * (muR n x * divMu (muR n) (carlV (BR S.A) (phiR ε)) x)
        + 2 * wC ε τ f x * muR n x * ⟪WC ε τ f Df x, carlV (BR S.A) (phiR ε) x⟫_ℝ := by
    have e : MFlux S ε τ f
        = fun y => wC ε τ f y ^ 2 • (muR n y • carlV (BR S.A) (phiR ε) y) := by
      funext y
      simp only [MFlux, smul_smul]
    have hwd : DifferentiableAt ℝ (fun y => wC ε τ f y ^ 2) x :=
      (hw2.differentiableAt (by norm_num)).pow 2
    have hVd : DifferentiableAt ℝ (fun y => muR n y • carlV (BR S.A) (phiR ε) y) x :=
      ((contDiffAt_muR hx0 (k := 1)).differentiableAt one_ne_zero).smul
        ((contDiffAt_carlV S ε hx0).differentiableAt one_ne_zero)
    rw [e, F2.divergence_smul hwd hVd, F2.mul_divMu (muR_ne_zero hx0)]
    have hfd : fderiv ℝ (fun y => wC ε τ f y ^ 2) x
        = (2 * wC ε τ f x) • fderiv ℝ (wC ε τ f) x := by
      have h := ((hw2.differentiableAt (by norm_num)).hasFDerivAt.pow 2).fderiv
      rw [h]
      ext v
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [hfd]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul]
    rw [← inner_gradient_left, gradient_wC hadm hx]
    ring
  have hT : TWC S ε τ f Df x = -2 * τ * ⟪carlV (BR S.A) (phiR ε) x, WC ε τ f Df x⟫_ℝ
      - τ * divMu (muR n) (carlV (BR S.A) (phiR ε)) x * wC ε τ f x := rfl
  have hS : carlS (muR n) (BR S.A) (phiR ε) τ (wC ε τ f) x
      = SpC S ε τ f x + mR n ^ 2 * wC ε τ f x := by
    simp only [SpC]; ring
  rw [hS] at key
  rw [hM, real_inner_comm (carlV (BR S.A) (phiR ε) x) (WC ε τ f Df x)]
  have e2 : muR n x * (SpC S ε τ f x + TWC S ε τ f Df x) ^ 2
      = muR n x * SpC S ε τ f x ^ 2 + muR n x * TWC S ε τ f Df x ^ 2
        + 2 * (SpC S ε τ f x + mR n ^ 2 * wC ε τ f x) * TWC S ε τ f Df x * muR n x
        - 2 * mR n ^ 2 * wC ε τ f x * TWC S ε τ f Df x * muR n x := by ring
  rw [e2, key, hT]
  ring

/-- **(ML4)** The pointwise lower bound of `carlJ` (steps (a) of the note, in `x` coordinates,
for `0 < ρ ≤ rs`, `ε ρ ≤ 1/4`, `K ρ ≤ 1/4`, `|A x - I| ≤ K ρ`):
`⟪V, ∇q⟫ ≥ ρ ((81/128) ε - 5 K²)` where `V = -(1-ερ) A x`, `q = (1-ερ)² ⟪A x, x⟫/ρ²`;
`4 ⟪DV (B W), W⟫ - 2 ⟪(DB V) W, W⟫ ≥ -14 K² ρ³ |W|²` (independent of `ε`);
`|2 τ w ⟪B W, ∇ div_μ V⟫| ≤ 2 τ ρ³ |W|² + (K² C_h² / 2) τ ρ w²` where
`C_h = sup_{0 < ρ ≤ rs} |∇ div_μ V|` (finite: uses `bound_dA`, `bound_d2A`). -/
theorem ml_J_lower (S : HalfBallSolution n) {ε rs : ℝ} (hε : 0 < ε) (hrs : 0 < rs)
    (hrsR : rs < S.R) (hrs1 : rs ≤ 1) (hεrs : ε * rs ≤ 1 / 4) (hKrs : (S.K + 1) * rs ≤ 1 / 4) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ τ : ℝ, 1 ≤ τ → ∀ x : Space n, x ≠ 0 → ‖x‖ ≤ rs →
      ∀ (wv : ℝ) (W : Space n),
        muR n x * (2 * ((81 / 128) * ε - 5 * S.K ^ 2) * τ ^ 3 * (‖x‖ * wv ^ 2)
          - 2 * (16 * S.K ^ 2 + 1) * τ * (‖x‖ ^ 3 * ‖W‖ ^ 2) - C' * τ * (‖x‖ * wv ^ 2))
        ≤ carlJW S ε τ wv W x := by
  sorry

/-! ### Regularity of the Carleman fields away from `0` (for `ml_div_integrable`) -/

/-- `V` is `C²` away from `0`. -/
theorem contDiffAt_carlV2 (S : HalfBallSolution n) (ε : ℝ) {x : Space n} (hx0 : x ≠ 0) :
    ContDiffAt ℝ 2 (carlV (BR S.A) (phiR ε)) x :=
  (contDiff_BR S).contDiffAt.clm_apply
    (F2.contDiffAt_gradient (m := 2) (contDiffAt_phiR ε hx0 (k := 3)) (by norm_num))

/-- `q` is `C²` away from `0`. -/
theorem contDiffAt_carlQ (S : HalfBallSolution n) (ε : ℝ) {x : Space n} (hx0 : x ≠ 0) :
    ContDiffAt ℝ 2 (carlQ (BR S.A) (phiR ε)) x := by
  have hg := F2.contDiffAt_gradient (m := 2) (contDiffAt_phiR ε hx0 (k := 3)) (by norm_num)
  exact ((contDiff_BR S).contDiffAt.clm_apply hg).inner ℝ hg

/-- `div_μ V` is `C¹` away from `0`. -/
theorem contDiffAt_divMuV (S : HalfBallSolution n) (ε : ℝ) {x : Space n} (hx0 : x ≠ 0) :
    ContDiffAt ℝ 1 (divMu (muR n) (carlV (BR S.A) (phiR ε))) x := by
  have hG : ContDiffAt ℝ 2 (fun y => muR n y • carlV (BR S.A) (phiR ε) y) x :=
    (contDiffAt_muR hx0).smul (contDiffAt_carlV2 S ε hx0)
  have hd : ContDiffAt ℝ 1
      (fun y => divergence (fun y => muR n y • carlV (BR S.A) (phiR ε) y) y) x :=
    (F2.traceCLM (n := n)).contDiff.contDiffAt.comp x (hG.fderiv_right (m := 1) (by norm_num))
  exact ((contDiffAt_muR hx0).inv (muR_ne_zero hx0)).mul hd

/-- `div(w² μ V) = w² μ div_μ V + 2 w μ ⟪W, V⟫` in the open half-space. -/
theorem div_MFlux_eq (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 < vcoord x) :
    divergence (MFlux S ε τ f) x
      = wC ε τ f x ^ 2 * (muR n x * divMu (muR n) (carlV (BR S.A) (phiR ε)) x)
        + 2 * wC ε τ f x * muR n x * ⟪WC ε τ f Df x, carlV (BR S.A) (phiR ε) x⟫_ℝ := by
  have hx0 := ne_zero_of_vcoord_pos hx
  have hw2 := contDiffAt_wC (ε := ε) (τ := τ) hadm hx
  have e : MFlux S ε τ f
      = fun y => wC ε τ f y ^ 2 • (muR n y • carlV (BR S.A) (phiR ε) y) := by
    funext y
    simp only [MFlux, smul_smul]
  have hwd : DifferentiableAt ℝ (fun y => wC ε τ f y ^ 2) x :=
    (hw2.differentiableAt (by norm_num)).pow 2
  have hVd : DifferentiableAt ℝ (fun y => muR n y • carlV (BR S.A) (phiR ε) y) x :=
    ((contDiffAt_muR hx0 (k := 1)).differentiableAt one_ne_zero).smul
      ((contDiffAt_carlV S ε hx0).differentiableAt one_ne_zero)
  rw [e, F2.divergence_smul hwd hVd, F2.mul_divMu (muR_ne_zero hx0)]
  have hfd : fderiv ℝ (fun y => wC ε τ f y ^ 2) x
      = (2 * wC ε τ f x) • fderiv ℝ (wC ε τ f) x := by
    have h := ((hw2.differentiableAt (by norm_num)).hasFDerivAt.pow 2).fderiv
    rw [h]
    ext v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hfd]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul]
  rw [← inner_gradient_left, gradient_wC hadm hx]
  ring

/-- `μ (T w)²` is integrable on the open half-space. -/
theorem integrableOn_TWC_sq (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) :
    IntegrableOn (fun x => muR n x * TWC S ε τ f Df x ^ 2) {x | 0 < vcoord x} := by
  refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => ?_) fun x hx hx0 => ?_
  · have : TWC S ε τ f Df x ≠ 0 := by
      intro h; apply hx; simp [h]
    exact TWC_supp S hadm x this
  · exact (continuousAt_muR hx0).continuousWithinAt.mul
      ((continuousWithinAt_TWC S hadm hx hx0).pow 2)

/-- The integrand `carlJ` (with `w`, `∇w` replaced by `wC`, `WC`) is continuous up to `t = 0`
away from `0`. -/
theorem continuousWithinAt_carlJW (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) {x : Space n} (hx : 0 ≤ vcoord x)
    (hx0 : x ≠ 0) :
    ContinuousWithinAt (fun y => carlJW S ε τ (wC ε τ f y) (WC ε τ f Df y) y)
      {x | 0 ≤ vcoord x} x := by
  have hw := continuousWithinAt_wC (ε := ε) (τ := τ) hadm hx hx0
  have hW := continuousWithinAt_WC (ε := ε) (τ := τ) hadm hx hx0
  have hμ := (continuousAt_muR hx0).continuousWithinAt (s := {x : Space n | 0 ≤ vcoord x})
  have hV := (contDiffAt_carlV S ε hx0).continuousAt.continuousWithinAt
    (s := {x : Space n | 0 ≤ vcoord x})
  have hgq : ContinuousWithinAt (gradient (carlQ (BR S.A) (phiR ε))) {x | 0 ≤ vcoord x} x :=
    (F2.contDiffAt_gradient (m := 0) (contDiffAt_carlQ S ε hx0)
      (by norm_num)).continuousAt.continuousWithinAt
  have hDV : ContinuousWithinAt (fderiv ℝ (carlV (BR S.A) (phiR ε))) {x | 0 ≤ vcoord x} x :=
    ((contDiffAt_carlV S ε hx0).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hDB : ContinuousWithinAt (fderiv ℝ (BR S.A)) {x | 0 ≤ vcoord x} x :=
    ((contDiff_BR S).continuous_fderiv (by norm_num)).continuousAt.continuousWithinAt
  have hB : ContinuousWithinAt (BR S.A) {x | 0 ≤ vcoord x} x :=
    (contDiff_BR S).continuous.continuousAt.continuousWithinAt
  have hgh : ContinuousWithinAt (gradient (divMu (muR n) (carlV (BR S.A) (phiR ε))))
      {x | 0 ≤ vcoord x} x :=
    (F2.contDiffAt_gradient (m := 0) (contDiffAt_divMuV S ε hx0)
      (by norm_num)).continuousAt.continuousWithinAt
  have hBW := hB.clm_apply hW
  unfold carlJW
  exact hμ.mul (((((continuousWithinAt_const.mul (hV.inner hgq)).mul (hw.pow 2)).add
    (continuousWithinAt_const.mul ((hDV.clm_apply hBW).inner hW))).sub
    (continuousWithinAt_const.mul (((hDB.clm_apply hV).clm_apply hW).inner hW))).add
    ((continuousWithinAt_const.mul hw).mul (hBW.inner hgh)))

/-- `carlJ` (with `wC`, `WC`) is integrable on the open half-space. -/
theorem integrableOn_carlJW (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) :
    IntegrableOn (fun x => carlJW S ε τ (wC ε τ f x) (WC ε τ f Df x) x) {x | 0 < vcoord x} := by
  refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => ?_)
    fun x hx hx0 => continuousWithinAt_carlJW S hadm hx hx0
  by_cases hw : wC ε τ f x = 0
  · by_cases hW : WC ε τ f Df x = 0
    · exfalso; apply hx; simp [carlJW, hw, hW]
    · exact WC_supp hadm x hW
  · exact wC_supp hadm x hw

/-- **(ML2)** Integrability of the two divergences on `{t > 0}` (by `ml_pointwise` the
divergence of `CFlux` is a sum of integrable terms; `div MFlux = μ (w² div_μ V + 2 w ⟪W, V⟫)`
is continuous with compact support away from `0`). -/
theorem ml_div_integrable (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) (hrsR : rs < S.R)
    (hPi : IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
      {x | 0 < vcoord x}) :
    IntegrableOn (divergence (CFlux S ε τ f Df)) {x | 0 < vcoord x} ∧
      IntegrableOn (divergence (MFlux S ε τ f)) {x | 0 < vcoord x} := by
  have hΩm : MeasurableSet {x : Space n | 0 < vcoord x} := F1.measurableSet_halfSpace 0
  -- `div MFlux`
  have hMi : IntegrableOn (divergence (MFlux S ε τ f)) {x | 0 < vcoord x} := by
    have hg : IntegrableOn (fun x =>
        wC ε τ f x ^ 2 * (muR n x * divMu (muR n) (carlV (BR S.A) (phiR ε)) x)
          + 2 * wC ε τ f x * muR n x * ⟪WC ε τ f Df x, carlV (BR S.A) (phiR ε) x⟫_ℝ)
        {x | 0 < vcoord x} := by
      refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => wC_supp (ε := ε) (τ := τ) hadm x ?_)
        fun x hx hx0 => ?_
      · intro h; apply hx; simp [h]
      · have hw := continuousWithinAt_wC (ε := ε) (τ := τ) hadm hx hx0
        have hW := continuousWithinAt_WC (ε := ε) (τ := τ) hadm hx hx0
        have hμ := (continuousAt_muR hx0).continuousWithinAt (s := {x : Space n | 0 ≤ vcoord x})
        have hV := (contDiffAt_carlV S ε hx0).continuousAt.continuousWithinAt
          (s := {x : Space n | 0 ≤ vcoord x})
        have hh := (continuousAt_divMuV S ε hx0).continuousWithinAt
          (s := {x : Space n | 0 ≤ vcoord x})
        exact ((hw.pow 2).mul (hμ.mul hh)).add
          (((continuousWithinAt_const.mul hw).mul hμ).mul (hW.inner hV))
    exact hg.congr_fun (fun x hx => (div_MFlux_eq S hadm hx).symm) hΩm
  refine ⟨?_, hMi⟩
  -- `div CFlux`, from `ml_pointwise`
  have hSi := integrableOn_SpC_sq S hadm hPi
  have hTi := integrableOn_TWC_sq (ε := ε) (τ := τ) S hadm
  have hJi := integrableOn_carlJW (ε := ε) (τ := τ) S hadm
  have hsum : IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2
      - muR n x * SpC S ε τ f x ^ 2 - muR n x * TWC S ε τ f Df x ^ 2
      - carlJW S ε τ (wC ε τ f x) (WC ε τ f Df x) x
      - 2 * mR n ^ 2 * τ * divergence (MFlux S ε τ f) x) {x | 0 < vcoord x} :=
    (((hPi.sub hSi).sub hTi).sub hJi).sub (hMi.const_mul _)
  refine hsum.congr_fun (fun x hx => ?_) hΩm
  have hid := ml_pointwise S (ε := ε) (τ := τ) hadm hx
  have hconj : Real.exp (τ * phiR ε x) * P0R S.A f x = SpC S ε τ f x + TWC S ε τ f Df x := by
    rw [conj_eq S ε τ hadm hx, carlT_eq S hadm hx]
  have hE2 : Real.exp (2 * τ * phiR ε x) = Real.exp (τ * phiR ε x) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hP : muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2
      = muR n x * (SpC S ε τ f x + TWC S ε τ f Df x) ^ 2 := by
    rw [← hconj, hE2]; ring
  simp only
  rw [hP, hid]
  ring

/-- **(ML3, `m²` part)** `∫ div(w² μ V) = 0`: the boundary integrand `w² μ ⟪V, e_d⟫` vanishes
on `t = 0` (`inner_carlV_ed`). -/
theorem ml_boundaryM (S : HalfBallSolution n) {ε τ rs δ : ℝ} {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) (hrsR : rs < S.R)
    (hPi : IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
      {x | 0 < vcoord x}) :
    ∫ x in {x : Space n | 0 < vcoord x}, divergence (MFlux S ε τ f) x = 0 := by
  have hf0 : ∀ y : Space n, ‖y‖ < δ → f y = 0 := fun y hy => by
    by_contra h
    have := (hadm.supp y h).1
    linarith
  have hf0' : ∀ y : Space n, rs < ‖y‖ → f y = 0 := fun y hy => by
    by_contra h
    have := (hadm.supp y h).2
    linarith
  have e : MFlux S ε τ f = fun y => (wC ε τ f y ^ 2 * muR n y) • carlV (BR S.A) (phiR ε) y := rfl
  have hC1 : ∀ x, 0 < vcoord x → ContDiffAt ℝ 1 (MFlux S ε τ f) x := by
    intro x hx
    have hx0 := ne_zero_of_vcoord_pos hx
    rw [e]
    exact ((((contDiffAt_wC (ε := ε) (τ := τ) hadm hx).of_le (by norm_num)).pow 2).mul
      (contDiffAt_muR hx0)).smul (contDiffAt_carlV S ε hx0)
  have hcont : ContinuousOn (MFlux S ε τ f) {x | 0 ≤ vcoord x} := by
    intro x hx
    by_cases hx0 : x = 0
    · have hev : MFlux S ε τ f =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds x hadm.pos] with y hy
        rw [Metric.mem_ball, hx0, dist_zero_right] at hy
        simp [MFlux, wC, hf0 y hy]
      exact (continuousAt_const.congr hev.symm).continuousWithinAt
    · rw [e]
      exact (((continuousWithinAt_wC hadm hx hx0).pow 2).mul
        (continuousAt_muR hx0).continuousWithinAt).smul
        (contDiffAt_carlV S ε hx0).continuousAt.continuousWithinAt
  have hsupp : HasCompactSupport (MFlux S ε τ f) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space n) rs) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    simp [MFlux, wC, hf0' y hy]
  have hIBP := integral_divergence_halfSpace_of_continuousOn (MFlux S ε τ f) hC1 hcont hsupp
    (ml_div_integrable S hadm hrsR hPi).2
  rw [hIBP]
  have h0 : ∀ y : EuclideanSpace ℝ (Fin n), ⟪MFlux S ε τ f (lift y 0), ed n⟫_ℝ = 0 := by
    intro y
    by_cases hfx : f (lift y 0) = 0
    · simp [MFlux, wC, hfx]
    · obtain ⟨hδx, hxr⟩ := hadm.supp _ hfx
      have hx0 : lift y 0 ≠ 0 := by
        intro h; rw [h, norm_zero] at hδx; linarith [hadm.pos]
      have hxf : lift y 0 ∈ flatPiece n S.R := ⟨by linarith, by rw [vcoord_lift]⟩
      simp only [MFlux, real_inner_smul_left, inner_carlV_ed S ε hx0 hxf, mul_zero]
  simp [h0]

/-- **(ML3, `carlFlux` part)** The boundary term of `carlFlux` (as in `gc_boundary`, with
`F1.integral_divergence_halfSpace_of_continuousOn`):
`⟪CFlux, e_d⟫ = μ ⟪B W, e_d⟫ (-4τ ⟪V, W⟫ - 2τ (div_μ V) w)` on `t = 0` (`inner_carlV_ed`
kills the `V`-terms), with `⟪B W, e_d⟫ = ρ² e^{τφ} ⟪A Df, e_d⟫` (`inner_BR_WC_ed`),
`|V| ≤ K ρ`, `ρ |W| ≤ e^{τφ} (ρ |Df| + τ |f|)` and `|div_μ V| ≤ C_h0` on `0 < ρ ≤ rs`. -/
theorem ml_boundaryC (S : HalfBallSolution n) {ε rs : ℝ} (hε : 0 < ε) (hrs : 0 < rs)
    (hrsR : rs < S.R) (hrs1 : rs ≤ 1) (hεrs : ε * rs ≤ 1 / 4) (hKrs : (S.K + 1) * rs ≤ 1 / 4) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ τ : ℝ, 1 ≤ τ → ∀ (f : Space n → ℝ) (Df : Space n → Space n) (δ : ℝ),
      Admissible rs δ f Df →
      IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
        {x | 0 < vcoord x} →
      -(CB * τ ^ 2 * IBd S ε τ f Df)
          ≤ ∫ x in {x : Space n | 0 < vcoord x}, divergence (CFlux S ε τ f Df) x := by
  sorry

/-- **(ML3)** The boundary terms. -/
theorem ml_boundary (S : HalfBallSolution n) {ε rs : ℝ} (hε : 0 < ε) (hrs : 0 < rs)
    (hrsR : rs < S.R) (hrs1 : rs ≤ 1) (hεrs : ε * rs ≤ 1 / 4) (hKrs : (S.K + 1) * rs ≤ 1 / 4) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ τ : ℝ, 1 ≤ τ → ∀ (f : Space n → ℝ) (Df : Space n → Space n) (δ : ℝ),
      Admissible rs δ f Df →
      IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
        {x | 0 < vcoord x} →
      -(CB * τ ^ 2 * IBd S ε τ f Df)
          ≤ ∫ x in {x : Space n | 0 < vcoord x}, divergence (CFlux S ε τ f Df) x ∧
        ∫ x in {x : Space n | 0 < vcoord x}, divergence (MFlux S ε τ f) x = 0 := by
  obtain ⟨CB, hCB, h⟩ := ml_boundaryC S hε hrs hrsR hrs1 hεrs hKrs
  exact ⟨CB, hCB, fun τ hτ f Df δ hadm hPi =>
    ⟨h τ hτ f Df δ hadm hPi, ml_boundaryM S hadm hrsR hPi⟩⟩

/-! ### The three integrated inequalities -/

/-- **Back to `f`**: `ρ³ e^{2τφ} |Df|² ≤ 2 ρ³ |W|² + 2 τ² ρ w²` pointwise (as `ρ |∇φ| ≤ 1`),
integrated. -/
theorem back_to_f {ε rs τ δ : ℝ} (hε : 0 ≤ ε) (hεrs : ε * rs ≤ 1 / 4) {f : Space n → ℝ}
    {Df : Space n → Space n} (hadm : Admissible rs δ f Df) :
    IYf ε τ Df ≤ 2 * IY ε τ f Df + 2 * τ ^ 2 * IX ε τ f := by
  have hΩm : MeasurableSet {x : Space n | 0 < vcoord x} := F1.measurableSet_halfSpace 0
  -- integrability
  have hXi : IntegrableOn (fun x => ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => ?_) fun x hx hx0 => ?_
    · have : f x ≠ 0 := by
        intro h; apply hx; simp [h]
      exact hadm.supp x this
    · have h1 : ContinuousAt (fun y : Space n => ‖y‖ * (muR n y * Real.exp (2 * τ * phiR ε y)))
          x := continuous_norm.continuousAt.mul (continuousAt_weight ε τ hx0)
      have h2 := h1.continuousWithinAt (s := {x : Space n | 0 ≤ vcoord x}).mul
        ((hadm.cont x hx).pow 2)
      refine h2.congr (fun y _ => ?_) ?_
      · simp only [Pi.mul_apply, Pi.pow_apply]
        ring
      · simp only [Pi.mul_apply, Pi.pow_apply]
        ring
  have hYfi : IntegrableOn
      (fun x => ‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2)
      {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => ?_) fun x hx hx0 => ?_
    · have : Df x ≠ 0 := by
        intro h; apply hx; simp [h]
      exact hadm.Dsupp x this
    · have h1 : ContinuousAt
          (fun y : Space n => ‖y‖ ^ 3 * (muR n y * Real.exp (2 * τ * phiR ε y))) x :=
        (continuous_norm.continuousAt.pow 3).mul (continuousAt_weight ε τ hx0)
      have h2 := h1.continuousWithinAt (s := {x : Space n | 0 ≤ vcoord x}).mul
        ((hadm.Dcont x hx).norm.pow 2)
      refine h2.congr (fun y _ => ?_) ?_
      · simp only [Pi.mul_apply, Pi.pow_apply]
        ring
      · simp only [Pi.mul_apply, Pi.pow_apply]
        ring
  have hYi : IntegrableOn (fun x => ‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
      {x | 0 < vcoord x} := by
    refine integrableOn_of_annulus (rs := rs) hadm.pos (fun x hx => ?_) fun x hx hx0 => ?_
    · by_contra hcon
      apply hx
      have hf0 : f x = 0 := by
        by_contra h; exact hcon (hadm.supp x h)
      have hD0 : Df x = 0 := by
        by_contra h; exact hcon (hadm.Dsupp x h)
      simp [WC, hf0, hD0]
    · have hgc : ContinuousAt (gradPhi ε) x := by
        have e : gradPhi ε = fun y : Space n => (-(1 - ε * ‖y‖) / ‖y‖ ^ 2) • y := rfl
        rw [e]
        exact (((continuous_const.sub (continuous_const.mul continuous_norm)).neg.continuousAt).div
          (continuous_norm.pow 2).continuousAt
          (pow_ne_zero 2 (norm_ne_zero_iff.2 hx0))).smul continuousAt_id
      have hφc : ContinuousAt (fun y => Real.exp (τ * phiR ε y)) x :=
        Real.continuous_exp.continuousAt.comp (continuousAt_const.mul (continuousAt_phiR ε hx0))
      have hWC : ContinuousWithinAt (WC ε τ f Df) {x : Space n | 0 ≤ vcoord x} x :=
        hφc.continuousWithinAt.smul ((hadm.Dcont x hx).add
          ((continuousWithinAt_const.mul (hadm.cont x hx)).smul hgc.continuousWithinAt))
      have h1 : ContinuousAt (fun y : Space n => ‖y‖ ^ 3 * muR n y) x :=
        (continuous_norm.continuousAt.pow 3).mul (continuousAt_muR hx0)
      exact h1.continuousWithinAt.mul (hWC.norm.pow 2)
  -- the pointwise inequality
  have hpt : ∀ x ∈ {x : Space n | 0 < vcoord x},
      ‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2
        ≤ 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
          + 2 * τ ^ 2 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_zero_of_vcoord_pos hx
    have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
    obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (τ * phiR ε x) := ⟨_, rfl⟩
    have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
    have hE2 : Real.exp (2 * τ * phiR ε x) = E ^ 2 := by
      rw [hE, sq, ← Real.exp_add]; ring_nf
    have hμ := muR_nonneg x
    have hW : E * ‖Df x‖ ≤ ‖WC ε τ f Df x‖ + |E * (τ * f x)| * ‖gradPhi ε x‖ := by
      have h1 : E • Df x = WC ε τ f Df x - (E * (τ * f x)) • gradPhi ε x := by
        simp only [WC, ← hE]
        rw [smul_add, smul_smul]
        abel
      have h2 := norm_sub_le (WC ε τ f Df x) ((E * (τ * f x)) • gradPhi ε x)
      rw [← h1, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hE0] at h2
      exact h2
    have hsq : E ^ 2 * ‖Df x‖ ^ 2 ≤ 2 * ‖WC ε τ f Df x‖ ^ 2
        + 2 * ((E * (τ * f x)) ^ 2 * ‖gradPhi ε x‖ ^ 2) := by
      have h0 : 0 ≤ E * ‖Df x‖ := by positivity
      have h3 : (E * ‖Df x‖) ^ 2
          ≤ (‖WC ε τ f Df x‖ + |E * (τ * f x)| * ‖gradPhi ε x‖) ^ 2 :=
        pow_le_pow_left₀ h0 hW 2
      have h4 : (|E * (τ * f x)| * ‖gradPhi ε x‖) ^ 2
          = (E * (τ * f x)) ^ 2 * ‖gradPhi ε x‖ ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (‖WC ε τ f Df x‖ - |E * (τ * f x)| * ‖gradPhi ε x‖)]
    have hg : ‖x‖ ^ 3 * ((E * (τ * f x)) ^ 2 * ‖gradPhi ε x‖ ^ 2)
        ≤ τ ^ 2 * (‖x‖ * E ^ 2 * f x ^ 2) := by
      by_cases hf : f x = 0
      · simp [hf]
      · have hxr : ‖x‖ ≤ rs := (hadm.supp x hf).2
        have hερ : ε * ‖x‖ ≤ 1 / 4 := le_trans (mul_le_mul_of_nonneg_left hxr hε) hεrs
        have hερ0 : 0 ≤ ε * ‖x‖ := mul_nonneg hε hρ.le
        have hnorm : ‖x‖ ^ 3 * ‖gradPhi ε x‖ ^ 2 = ‖x‖ * (1 - ε * ‖x‖) ^ 2 := by
          have e : gradPhi ε x = (-(1 - ε * ‖x‖) / ‖x‖ ^ 2) • x := rfl
          rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
          field_simp
        have h1 : (1 - ε * ‖x‖) ^ 2 ≤ 1 := by nlinarith
        calc ‖x‖ ^ 3 * ((E * (τ * f x)) ^ 2 * ‖gradPhi ε x‖ ^ 2)
            = (E * (τ * f x)) ^ 2 * (‖x‖ ^ 3 * ‖gradPhi ε x‖ ^ 2) := by ring
          _ = (E * (τ * f x)) ^ 2 * (‖x‖ * (1 - ε * ‖x‖) ^ 2) := by rw [hnorm]
          _ ≤ (E * (τ * f x)) ^ 2 * (‖x‖ * 1) := by gcongr
          _ = τ ^ 2 * (‖x‖ * E ^ 2 * f x ^ 2) := by ring
    rw [hE2]
    have h5 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ‖x‖ ^ 3 * muR n x by positivity)
    have h6 := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2 * muR n x by positivity)
    calc ‖x‖ ^ 3 * muR n x * E ^ 2 * ‖Df x‖ ^ 2
        = ‖x‖ ^ 3 * muR n x * (E ^ 2 * ‖Df x‖ ^ 2) := by ring
      _ ≤ ‖x‖ ^ 3 * muR n x * (2 * ‖WC ε τ f Df x‖ ^ 2
          + 2 * ((E * (τ * f x)) ^ 2 * ‖gradPhi ε x‖ ^ 2)) := h5
      _ = 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
          + 2 * muR n x * (‖x‖ ^ 3 * ((E * (τ * f x)) ^ 2 * ‖gradPhi ε x‖ ^ 2)) := by ring
      _ ≤ 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
          + 2 * muR n x * (τ ^ 2 * (‖x‖ * E ^ 2 * f x ^ 2)) := by linarith
      _ = 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
          + 2 * τ ^ 2 * (‖x‖ * muR n x * E ^ 2 * f x ^ 2) := by ring
  have hY2 : IntegrableOn (fun x => 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2))
      {x | 0 < vcoord x} := hYi.const_mul 2
  have hX2 : IntegrableOn
      (fun x => 2 * τ ^ 2 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2))
      {x | 0 < vcoord x} := hXi.const_mul _
  have hsum : IntegrableOn (fun x => 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
      + 2 * τ ^ 2 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2))
      {x | 0 < vcoord x} := hY2.add hX2
  have hmono := setIntegral_mono_on hYfi hsum hΩm hpt
  rw [integral_add hY2 hX2, integral_const_mul, integral_const_mul] at hmono
  exact hmono

/-- **Gradient control** (step (b) of the note, Lemma 2.1(3) with `ϱ = ρ`):
`F2.carleman_gradient_pointwise` with `ϱ = ‖·‖`, integrated over `{t > 0}` with
`F1.integral_divergence_halfSpace_of_continuousOn` (flux `μ ρ w B W`, whose normal component at
`t = 0` is `μ ρ³ e^{2τφ} f ⟪A Df, e_d⟫`, bounded by the integrand of `IBd`). Then
`λ ρ² |W|² ≤ ⟪B W, W⟫`, `-S w ρ w = -S' w ρ w - m² ρ w² ≤ |S' w| ρ |w|`,
`|S'w| ρ |w| ≤ (1/(2c)) S'w² + (c/2) ρ² w²`, `q ≤ K`, `|⟪B W, ∇ρ⟫| ≤ K ρ² |W|` and
`K ρ² |w| |W| ≤ (λ/2) ρ³ |W|² + (K²/(2λ)) ρ w²`; multiply by `2c`. -/
theorem grad_control (S : HalfBallSolution n) {ε rs : ℝ} (hε : 0 < ε) (hrs : 0 < rs)
    (hrsR : rs < S.R) (hrs1 : rs ≤ 1) (hεrs : ε * rs ≤ 1 / 4) (hKrs : (S.K + 1) * rs ≤ 1 / 4)
    {τ : ℝ} (hτ : 1 ≤ τ) {f : Space n → ℝ} {Df : Space n → Space n} {δ : ℝ}
    (hadm : Admissible rs δ f Df)
    (hPi : IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
      {x | 0 < vcoord x}) :
    ∀ c : ℝ, 0 < c → c * S.lam * IY ε τ f Df
      ≤ ISg S ε τ f + c ^ 2 * IX ε τ f + 2 * c * S.K * τ ^ 2 * IX ε τ f
        + c * S.K ^ 2 / S.lam * IX ε τ f + 2 * c * IBd S ε τ f Df := by
  intro c hc
  have hΩm : MeasurableSet {x : Space n | 0 < vcoord x} := F1.measurableSet_halfSpace 0
  have hlam : 0 < S.lam := S.coeffs.lam_pos
  have hYi := integrableOn_Y (ε := ε) (τ := τ) hadm
  have hXi := integrableOn_X (ε := ε) (τ := τ) hadm
  have hSi := integrableOn_SpC_sq S hadm hPi
  have hDi := gc_div_integrable S hadm hrsR hPi
  have hL : IntegrableOn (fun x => S.lam * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2))
      {x | 0 < vcoord x} := hYi.const_mul _
  have hR1 : IntegrableOn (fun x => 1 / (2 * c) * (muR n x * SpC S ε τ f x ^ 2))
      {x | 0 < vcoord x} := hSi.const_mul _
  have hR2 : IntegrableOn (fun x => (c / 2 + S.K * τ ^ 2 + S.K ^ 2 / (2 * S.lam))
      * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)) {x | 0 < vcoord x} :=
    hXi.const_mul _
  have hR3 : IntegrableOn (fun x => S.lam / 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2))
      {x | 0 < vcoord x} := hYi.const_mul _
  have hR12 : IntegrableOn (fun x => 1 / (2 * c) * (muR n x * SpC S ε τ f x ^ 2)
      + (c / 2 + S.K * τ ^ 2 + S.K ^ 2 / (2 * S.lam))
        * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)) {x | 0 < vcoord x} :=
    hR1.add hR2
  have hR123 : IntegrableOn (fun x => 1 / (2 * c) * (muR n x * SpC S ε τ f x ^ 2)
      + (c / 2 + S.K * τ ^ 2 + S.K ^ 2 / (2 * S.lam))
        * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      + S.lam / 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)) {x | 0 < vcoord x} :=
    hR12.add hR3
  have hR : IntegrableOn (fun x => 1 / (2 * c) * (muR n x * SpC S ε τ f x ^ 2)
      + (c / 2 + S.K * τ ^ 2 + S.K ^ 2 / (2 * S.lam))
        * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      + S.lam / 2 * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
      + divergence (GFlux S ε τ f Df) x) {x | 0 < vcoord x} := hR123.add hDi
  have hmono := setIntegral_mono_on hL hR hΩm fun x hx =>
    gc_pointwise_bound S hε hrs1 hεrs hadm hc hx
  rw [integral_add hR123 hDi, integral_add hR12 hR3, integral_add hR1 hR2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul] at hmono
  exact gc_algebra hlam hc hmono (gc_boundary S hadm hrsR hrs1 hPi)

/-- **The main lower bound** (steps (a), (c) of the note):
`∫ (S'w + Tw)² μ ≥ Σ + 2 ∫ S w T w μ - 2 m² ∫ w T w μ`, with
`2 S w T w μ = carlJ + div carlFlux` (`F2.carleman_pointwise`) and
`w T w μ = -τ div(w² μ V)` (no boundary term since `⟪V, e_d⟫ = 0` on `t = 0`). The boundary term
of `carlFlux` is `μ ⟪B W, e_d⟫ (-4τ ⟪V, W⟫ - 2τ (div_μ V) w)` with
`⟪B W, e_d⟫ = ρ² e^{τφ} ⟪A Df, e_d⟫`, `|V| ≤ K ρ`, `|W| ≤ e^{τφ} (|Df| + τ |f| / ρ)`,
`|div_μ V| ≤ C_h0`: bounded by `CB τ² IBd`. Lower bound of `carlJ` (for `ε ρ ≤ 1/4`,
`K ρ ≤ 1/4`, `|A - I| ≤ K ρ`): `⟪V, ∇q⟫ ≥ ρ ((81/128) ε - 5 K²)`;
`4 ⟪DV (B ξ), ξ⟫ - 2 ⟪(DB V) ξ, ξ⟫ ≥ -14 K² ρ³ |ξ|²`;
`|2 τ w ⟪B ξ, ∇ div_μ V⟫| ≤ 2 τ ρ³ |ξ|² + (C_h² K² / 2) τ ρ w²` with `|∇ div_μ V| ≤ C_h`
(uses `bound_d2A`). Here `V = carlV (BR A) φ = -(1 - ερ) A x`, `q = (1-ερ)² ⟪A x, x⟫ / ρ²`. -/
theorem main_lower (S : HalfBallSolution n) (hn : 0 < n) {ε rs : ℝ} (hε : 0 < ε) (hrs : 0 < rs)
    (hrsR : rs < S.R) (hrs1 : rs ≤ 1) (hεrs : ε * rs ≤ 1 / 4) (hKrs : (S.K + 1) * rs ≤ 1 / 4) :
    ∃ C' CB : ℝ, 0 ≤ C' ∧ 0 ≤ CB ∧ ∀ τ : ℝ, 1 ≤ τ → ∀ (f : Space n → ℝ)
      (Df : Space n → Space n) (δ : ℝ), Admissible rs δ f Df →
      IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
        {x | 0 < vcoord x} →
      ISg S ε τ f + 2 * ((81 / 128) * ε - 5 * S.K ^ 2) * τ ^ 3 * IX ε τ f
          - 2 * (16 * S.K ^ 2 + 1) * τ * IY ε τ f Df - C' * τ * IX ε τ f
          - CB * τ ^ 2 * IBd S ε τ f Df
        ≤ IPP S ε τ f := by
  obtain ⟨C', hC'0, hJ⟩ := ml_J_lower S hε hrs hrsR hrs1 hεrs hKrs
  obtain ⟨CB, hCB0, hBdry⟩ := ml_boundary S hε hrs hrsR hrs1 hεrs hKrs
  refine ⟨C', CB, hC'0, hCB0, fun τ hτ f Df δ hadm hPi => ?_⟩
  have hΩm : MeasurableSet {x : Space n | 0 < vcoord x} := F1.measurableSet_halfSpace 0
  obtain ⟨hCi, hMi⟩ := ml_div_integrable S hadm hrsR hPi
  obtain ⟨hbC, hbM⟩ := hBdry τ hτ f Df δ hadm hPi
  have hSi := integrableOn_SpC_sq S hadm hPi
  have hXi := integrableOn_X (ε := ε) (τ := τ) hadm
  have hYi := integrableOn_Y (ε := ε) (τ := τ) hadm
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = 2 * ((81 / 128) * ε - 5 * S.K ^ 2) := ⟨_, rfl⟩
  obtain ⟨cY, hcY⟩ : ∃ c : ℝ, c = 2 * (16 * S.K ^ 2 + 1) := ⟨_, rfl⟩
  rw [← had, ← hcY]
  -- the pointwise inequality
  have hpt : ∀ x ∈ {x : Space n | 0 < vcoord x},
      muR n x * SpC S ε τ f x ^ 2
        + a * τ ^ 3 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
        - cY * τ * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
        - C' * τ * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
        + divergence (CFlux S ε τ f Df) x
        + 2 * mR n ^ 2 * τ * divergence (MFlux S ε τ f) x
      ≤ muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2 := by
    intro x hx
    have hx0 := ne_zero_of_vcoord_pos hx
    have hμ := muR_nonneg x
    have hconj : Real.exp (τ * phiR ε x) * P0R S.A f x = SpC S ε τ f x + TWC S ε τ f Df x := by
      rw [conj_eq S ε τ hadm hx, carlT_eq S hadm hx]
    have hE2 : Real.exp (2 * τ * phiR ε x) = Real.exp (τ * phiR ε x) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hP : muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2
        = muR n x * (SpC S ε τ f x + TWC S ε τ f Df x) ^ 2 := by
      rw [← hconj, hE2]; ring
    have hw2 : wC ε τ f x ^ 2 = Real.exp (2 * τ * phiR ε x) * f x ^ 2 := by
      rw [hE2, wC, mul_pow]
    have hid := ml_pointwise S (ε := ε) (τ := τ) hadm hx
    have hJx : muR n x * (a * τ ^ 3 * (‖x‖ * wC ε τ f x ^ 2)
          - cY * τ * (‖x‖ ^ 3 * ‖WC ε τ f Df x‖ ^ 2) - C' * τ * (‖x‖ * wC ε τ f x ^ 2))
        ≤ carlJW S ε τ (wC ε τ f x) (WC ε τ f Df x) x := by
      by_cases hxr : ‖x‖ ≤ rs
      · have := hJ τ hτ x hx0 hxr (wC ε τ f x) (WC ε τ f Df x)
        rw [had, hcY]
        exact this
      · push Not at hxr
        have hf0 : f x = 0 := by
          by_contra h; have := (hadm.supp x h).2; linarith
        have hD0 : Df x = 0 := by
          by_contra h; have := (hadm.Dsupp x h).2; linarith
        have hw0 : wC ε τ f x = 0 := by simp [wC, hf0]
        have hW0 : WC ε τ f Df x = 0 := by simp [WC, hf0, hD0]
        rw [hw0, hW0]
        simp [carlJW]
    have hT : 0 ≤ muR n x * TWC S ε τ f Df x ^ 2 := by positivity
    have e1 : muR n x * (a * τ ^ 3 * (‖x‖ * wC ε τ f x ^ 2)
          - cY * τ * (‖x‖ ^ 3 * ‖WC ε τ f Df x‖ ^ 2) - C' * τ * (‖x‖ * wC ε τ f x ^ 2))
        = a * τ ^ 3 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
          - cY * τ * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
          - C' * τ * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2) := by
      rw [hw2]; ring
    rw [hP]
    linarith only [hid, hJx, hT, e1]
  -- integrate
  have i1 : IntegrableOn (fun x => a * τ ^ 3 *
      (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)) {x | 0 < vcoord x} :=
    hXi.const_mul _
  have i2 : IntegrableOn (fun x => cY * τ * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2))
      {x | 0 < vcoord x} := hYi.const_mul _
  have i3 : IntegrableOn (fun x => C' * τ *
      (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)) {x | 0 < vcoord x} :=
    hXi.const_mul _
  have i5 : IntegrableOn (fun x => 2 * mR n ^ 2 * τ * divergence (MFlux S ε τ f) x)
      {x | 0 < vcoord x} := hMi.const_mul _
  have j1 : IntegrableOn (fun x => muR n x * SpC S ε τ f x ^ 2
      + a * τ ^ 3 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2))
      {x | 0 < vcoord x} := hSi.add i1
  have j2 : IntegrableOn (fun x => muR n x * SpC S ε τ f x ^ 2
      + a * τ ^ 3 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      - cY * τ * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)) {x | 0 < vcoord x} := j1.sub i2
  have j3 : IntegrableOn (fun x => muR n x * SpC S ε τ f x ^ 2
      + a * τ ^ 3 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      - cY * τ * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
      - C' * τ * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2))
      {x | 0 < vcoord x} := j2.sub i3
  have j4 : IntegrableOn (fun x => muR n x * SpC S ε τ f x ^ 2
      + a * τ ^ 3 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      - cY * τ * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
      - C' * τ * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      + divergence (CFlux S ε τ f Df) x) {x | 0 < vcoord x} := j3.add hCi
  have j5 : IntegrableOn (fun x => muR n x * SpC S ε τ f x ^ 2
      + a * τ ^ 3 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      - cY * τ * (‖x‖ ^ 3 * muR n x * ‖WC ε τ f Df x‖ ^ 2)
      - C' * τ * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      + divergence (CFlux S ε τ f Df) x
      + 2 * mR n ^ 2 * τ * divergence (MFlux S ε τ f) x) {x | 0 < vcoord x} := j4.add i5
  have hmono := setIntegral_mono_on j5 hPi hΩm hpt
  rw [integral_add j4 i5, integral_add j3 hCi, integral_sub j2 i3, integral_sub j1 i2,
    integral_add hSi i1, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, hbM] at hmono
  simp only [ISg, IX, IY, IBd, IPP] at hbC ⊢
  linarith only [hmono, hbC]

/-! ### Real-number absorption -/

/-- The constant of `core`. -/
noncomputable def coreC (lam K CJ CB : ℝ) : ℝ :=
  (3 + 2 / lam * (1 + 2 * K + K ^ 2 / lam)) * (1 + (4 * CJ / lam + CB)) + 4 / lam
    + 4 * (4 * CJ / lam + CB) / lam + 4 / lam + 1

theorem coreC_pos {lam K CJ CB : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) (hCJ : 0 < CJ) (hCB : 0 ≤ CB) :
    0 < coreC lam K CJ CB := by
  unfold coreC
  have h1 : 0 ≤ 2 / lam * (1 + 2 * K + K ^ 2 / lam) :=
    mul_nonneg (div_nonneg zero_le_two hlam.le)
      (add_nonneg (by linarith) (div_nonneg (sq_nonneg K) hlam.le))
  have h2 : 0 ≤ 4 * CJ / lam + CB := add_nonneg (div_nonneg (by linarith) hlam.le) hCB
  have h3 : 0 ≤ 4 / lam := div_nonneg (by norm_num) hlam.le
  have h4 : 0 ≤ 4 * (4 * CJ / lam + CB) / lam := div_nonneg (by linarith) hlam.le
  have h5 : 0 ≤ (3 + 2 / lam * (1 + 2 * K + K ^ 2 / lam)) * (1 + (4 * CJ / lam + CB)) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

theorem core_algebra {lam K CJ a C' CB τ X Y Yf Sg Bd PP : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K)
    (hCJ : 0 < CJ) (hC' : 0 ≤ C') (hCB : 0 ≤ CB) (ha : 4 * CJ * K / lam + 2 ≤ a)
    (hτ1 : 1 ≤ τ) (hτ : 8 * CJ ^ 2 / lam ^ 2 + (2 * CJ * K ^ 2 / lam ^ 2 + C') ≤ τ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hSg : 0 ≤ Sg) (hBd : 0 ≤ Bd) (hPP : 0 ≤ PP)
    (hML : Sg + a * τ ^ 3 * X - 2 * CJ * τ * Y - C' * τ * X - CB * τ ^ 2 * Bd ≤ PP)
    (hGC : ∀ c : ℝ, 0 < c → c * lam * Y
      ≤ Sg + c ^ 2 * X + 2 * c * K * τ ^ 2 * X + c * K ^ 2 / lam * X + 2 * c * Bd)
    (hBF : Yf ≤ 2 * Y + 2 * τ ^ 2 * X) :
    τ ^ 3 * X + τ * Yf ≤ coreC lam K CJ CB * PP + coreC lam K CJ CB * τ ^ 2 * Bd := by
  have hτ0 : 0 < τ := by linarith
  have hτ2 : τ ≤ τ ^ 2 := by nlinarith
  have hτ3 : τ ^ 2 ≤ τ ^ 3 := by nlinarith
  obtain ⟨P3, hP3⟩ : ∃ P, P = τ ^ 3 * X := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P, P = τ ^ 2 * X := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P, P = τ * X := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ Q, Q = τ ^ 2 * Bd := ⟨_, rfl⟩
  obtain ⟨Q1, hQ1⟩ : ∃ Q, Q = τ * Bd := ⟨_, rfl⟩
  obtain ⟨TY, hTY⟩ : ∃ T, T = τ * Y := ⟨_, rfl⟩
  have hP3P2 : P2 ≤ P3 := by rw [hP2, hP3]; exact mul_le_mul_of_nonneg_right hτ3 hX
  have hP2P1 : P1 ≤ P2 := by rw [hP1, hP2]; exact mul_le_mul_of_nonneg_right hτ2 hX
  have hQ : Q1 ≤ Q2 := by rw [hQ1, hQ2]; exact mul_le_mul_of_nonneg_right hτ2 hBd
  have hP30 : 0 ≤ P3 := by rw [hP3]; positivity
  have hP20 : 0 ≤ P2 := by rw [hP2]; positivity
  have hQ20 : 0 ≤ Q2 := by rw [hQ2]; positivity
  have hML' : Sg + a * P3 - 2 * CJ * TY - C' * P1 - CB * Q2 ≤ PP := by
    rw [hP3, hTY, hP1, hQ2]; (try simp only [div_eq_mul_inv] at *); linarith only [hML]
  -- step 1: `hGC` with `c = 4 CJ τ / λ`
  have h1 := hGC (4 * CJ / lam * τ) (by positivity)
  have e1 : 4 * CJ / lam * τ * lam * Y = 4 * CJ * TY := by
    rw [hTY]; field_simp
  have e2 : (4 * CJ / lam * τ) ^ 2 * X = 16 * CJ ^ 2 / lam ^ 2 * P2 := by rw [hP2]; ring
  have e3 : 2 * (4 * CJ / lam * τ) * K * τ ^ 2 * X = 8 * CJ * K / lam * P3 := by rw [hP3]; ring
  have e4 : 4 * CJ / lam * τ * K ^ 2 / lam * X = 4 * CJ * K ^ 2 / lam ^ 2 * P1 := by
    rw [hP1]; ring
  have e5 : 2 * (4 * CJ / lam * τ) * Bd = 8 * CJ / lam * Q1 := by rw [hQ1]; ring
  have h1' : 4 * CJ * TY ≤ Sg + 16 * CJ ^ 2 / lam ^ 2 * P2 + 8 * CJ * K / lam * P3
      + 4 * CJ * K ^ 2 / lam ^ 2 * P1 + 8 * CJ / lam * Q1 := by
    rw [e1, e2, e3, e4, e5] at h1; exact h1
  -- step 2: the main inequality
  have hA : (4 * CJ * K / lam + 2) * P3 ≤ a * P3 := mul_le_mul_of_nonneg_right ha hP30
  have hD : 8 * CJ ^ 2 / lam ^ 2 * P2 + (2 * CJ * K ^ 2 / lam ^ 2 + C') * P1 ≤ P3 := by
    have i2 : (2 * CJ * K ^ 2 / lam ^ 2 + C') * P1 ≤ (2 * CJ * K ^ 2 / lam ^ 2 + C') * P2 :=
      mul_le_mul_of_nonneg_left hP2P1 (by positivity)
    have i3 : (8 * CJ ^ 2 / lam ^ 2 + (2 * CJ * K ^ 2 / lam ^ 2 + C')) * P2 ≤ τ * P2 :=
      mul_le_mul_of_nonneg_right hτ hP20
    have i4 : τ * P2 = P3 := by rw [hP2, hP3]; ring
    (try simp only [div_eq_mul_inv] at *); linarith only [i2, i3, i4]
  have h8 : 8 * CJ / lam * Q1 ≤ 8 * CJ / lam * Q2 := mul_le_mul_of_nonneg_left hQ (by positivity)
  have hmain : Sg / 2 + P3 - (4 * CJ / lam + CB) * Q2 ≤ PP := by
    (try simp only [div_eq_mul_inv] at *); linarith only [hML', h1', hA, hD, h8]
  -- step 4: `hGC` with `c = τ`
  have h4 := hGC τ hτ0
  have h4' : lam * TY ≤ Sg + (1 + 2 * K + K ^ 2 / lam) * P3 + 2 * Q2 := by
    have f1 : τ * lam * Y = lam * TY := by rw [hTY]; ring
    have f3 : 2 * τ * K * τ ^ 2 * X = 2 * K * P3 := by rw [hP3]; ring
    have f4 : τ * K ^ 2 / lam * X = K ^ 2 / lam * P1 := by rw [hP1]; ring
    have f5 : 2 * τ * Bd = 2 * Q1 := by rw [hQ1]; ring
    have i1 : K ^ 2 / lam * P1 ≤ K ^ 2 / lam * P3 :=
      mul_le_mul_of_nonneg_left (hP2P1.trans hP3P2) (by positivity)
    (try simp only [div_eq_mul_inv] at *); linarith only [h4, f1, hP2, f3, f4, f5, i1, hP3P2, hQ]
  -- step 5
  have h5 : τ * Yf ≤ 2 * TY + 2 * P3 := by
    have h := mul_le_mul_of_nonneg_left hBF hτ0.le
    have e : τ * (2 * Y + 2 * τ ^ 2 * X) = 2 * TY + 2 * P3 := by rw [hTY, hP3]; ring
    (try simp only [div_eq_mul_inv] at *); linarith only [h, e]
  -- assembly
  obtain ⟨E, hE⟩ : ∃ E, E = 3 + 2 / lam * (1 + 2 * K + K ^ 2 / lam) := ⟨_, rfl⟩
  obtain ⟨D₃, hD₃⟩ : ∃ D, D = 4 * CJ / lam + CB := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hD₃0 : 0 ≤ D₃ := by rw [hD₃]; positivity
  have hmain' : Sg / 2 + P3 - D₃ * Q2 ≤ PP := by rw [hD₃]; exact hmain
  have hTYb : 2 * TY ≤ 2 / lam * Sg + 2 / lam * (1 + 2 * K + K ^ 2 / lam) * P3 + 4 / lam * Q2 := by
    have : TY ≤ (Sg + (1 + 2 * K + K ^ 2 / lam) * P3 + 2 * Q2) / lam := by
      rw [le_div_iff₀ hlam]; (try simp only [div_eq_mul_inv] at *); linarith only [h4']
    have e : 2 * ((Sg + (1 + 2 * K + K ^ 2 / lam) * P3 + 2 * Q2) / lam)
        = 2 / lam * Sg + 2 / lam * (1 + 2 * K + K ^ 2 / lam) * P3 + 4 / lam * Q2 := by ring
    (try simp only [div_eq_mul_inv] at *); linarith only [this, e]
  have hsum : τ ^ 3 * X + τ * Yf ≤ E * P3 + 2 / lam * Sg + 4 / lam * Q2 := by
    have e : E * P3 = 3 * P3 + 2 / lam * (1 + 2 * K + K ^ 2 / lam) * P3 := by rw [hE]; ring
    (try simp only [div_eq_mul_inv] at *); linarith only [h5, hTYb, e, hP3]
  have hP3' : P3 ≤ PP + D₃ * Q2 := by (try simp only [div_eq_mul_inv] at *); linarith only [hmain', hSg]
  have hSg' : Sg ≤ 2 * PP + 2 * D₃ * Q2 := by (try simp only [div_eq_mul_inv] at *); linarith only [hmain', hP30]
  have f1 : E * P3 ≤ E * PP + E * D₃ * Q2 := by
    have := mul_le_mul_of_nonneg_left hP3' hE0
    (try simp only [div_eq_mul_inv] at *); linarith only [this]
  have f2 : 2 / lam * Sg ≤ 4 / lam * PP + 4 * D₃ / lam * Q2 := by
    have := mul_le_mul_of_nonneg_left hSg' (div_nonneg zero_le_two hlam.le)
    have e : 2 / lam * (2 * PP + 2 * D₃ * Q2) = 4 / lam * PP + 4 * D₃ / lam * Q2 := by ring
    (try simp only [div_eq_mul_inv] at *); linarith only [this, e]
  have hC : coreC lam K CJ CB = E + E * D₃ + 4 / lam + 4 * D₃ / lam + 4 / lam + 1 := by
    rw [hE, hD₃]; unfold coreC; ring
  have g1 : 0 ≤ (E * D₃ + 4 * D₃ / lam + 4 / lam + 1) * PP := by
    apply mul_nonneg _ hPP
    have : 0 ≤ 4 * D₃ / lam := div_nonneg (by linarith) hlam.le
    have : 0 ≤ 4 / lam := div_nonneg (by norm_num) hlam.le
    have : 0 ≤ E * D₃ := mul_nonneg hE0 hD₃0
    linarith
  have g2 : 0 ≤ (E + 4 / lam + 1) * Q2 := by
    apply mul_nonneg _ hQ20
    have : 0 ≤ 4 / lam := div_nonneg (by norm_num) hlam.le
    linarith
  have eg : coreC lam K CJ CB * τ ^ 2 * Bd = coreC lam K CJ CB * Q2 := by rw [hQ2]; ring
  rw [eg, hC]
  have ex1 : (E + E * D₃ + 4 / lam + 4 * D₃ / lam + 4 / lam + 1) * PP
      = (E + 4 / lam) * PP + (E * D₃ + 4 * D₃ / lam + 4 / lam + 1) * PP := by ring
  have ex2 : (E + E * D₃ + 4 / lam + 4 * D₃ / lam + 4 / lam + 1) * Q2
      = (E * D₃ + 4 * D₃ / lam + 4 / lam) * Q2 + (E + 4 / lam + 1) * Q2 := by ring
  have ex3 : (E + 4 / lam) * PP = E * PP + 4 / lam * PP := by ring
  have ex4 : (E * D₃ + 4 * D₃ / lam + 4 / lam) * Q2 = E * D₃ * Q2 + 4 * D₃ / lam * Q2
      + 4 / lam * Q2 := by ring
  (try simp only [div_eq_mul_inv] at *); linarith only [hsum, f1, f2, g1, g2, ex1, ex2, ex3, ex4]

/-- **The core Carleman estimate** (Lemma R2 for `P₀` itself, i.e. `K₁ = 0` and `F = P₀ f`).
Assembled from `main_lower`, `grad_control`, `back_to_f` and `core_algebra`, with
`C_J = 16 K² + 1`, `ε = 2 (5 K² + 2 C_J K / λ + 1)` and `rs` small. -/
theorem core (S : HalfBallSolution n) (hn : 0 < n) :
    ∃ ε rs τ₁ C : ℝ, 0 < ε ∧ 0 < rs ∧ rs < S.R ∧ rs ≤ 1 ∧ ε * rs ≤ 1 / 4 ∧ 1 ≤ τ₁ ∧ 0 < C ∧
      ∀ τ : ℝ, τ₁ ≤ τ → ∀ (f : Space n → ℝ) (Df : Space n → Space n) (δ : ℝ), 0 < δ →
        (∀ x, f x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs) →
        (∀ x, Df x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs) →
        (∀ x, 0 < vcoord x → ContDiffAt ℝ 2 f x) →
        (∀ x, 0 < vcoord x → gradient f x = Df x) →
        ContinuousOn f {x | 0 ≤ vcoord x} → ContinuousOn Df {x | 0 ≤ vcoord x} →
        IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
          {x | 0 < vcoord x} →
        τ ^ 3 * (∫ x in {x : Space n | 0 < vcoord x},
            ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
          + τ * (∫ x in {x : Space n | 0 < vcoord x},
            ‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2)
        ≤ C * (∫ x in {x : Space n | 0 < vcoord x},
            muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
          + C * τ ^ 2 * (∫ y : EuclideanSpace ℝ (Fin n),
            ‖lift y 0‖ ^ 2 * muR n (lift y 0) * Real.exp (2 * τ * phiR ε (lift y 0)) *
              (|⟪S.A (lift y 0) (Df (lift y 0)), ed n⟫_ℝ| *
                (‖lift y 0‖ * ‖Df (lift y 0)‖ + |f (lift y 0)|))) := by
  have hK : 0 ≤ S.K := le_trans (norm_nonneg _) (S.coeffs.bound_A 0)
  have hlam : 0 < S.lam := S.coeffs.lam_pos
  have hR := S.R_pos
  obtain ⟨CJ, hCJ⟩ : ∃ c : ℝ, c = 16 * S.K ^ 2 + 1 := ⟨_, rfl⟩
  have hCJ0 : 0 < CJ := by rw [hCJ]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ e : ℝ, e = 2 * (5 * S.K ^ 2 + 2 * CJ * S.K / S.lam + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨rs, hrsdef⟩ : ∃ r : ℝ,
      r = min (min (1 / (4 * ε)) (1 / (4 * (S.K + 1)))) (min (S.R / 2) 1) := ⟨_, rfl⟩
  have hrs : 0 < rs := by
    rw [hrsdef]
    exact lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) one_pos)
  have hrs_a : rs ≤ 1 / (4 * ε) := by
    rw [hrsdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrs_b : rs ≤ 1 / (4 * (S.K + 1)) := by
    rw [hrsdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrs_c : rs ≤ S.R / 2 := by
    rw [hrsdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hrs1 : rs ≤ 1 := by
    rw [hrsdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hrsR : rs < S.R := by linarith
  have hεrs : ε * rs ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hrs_a hε.le
    rw [show ε * (1 / (4 * ε)) = 1 / 4 by field_simp] at this
    exact this
  have hKrs : (S.K + 1) * rs ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hrs_b (by linarith : (0 : ℝ) ≤ S.K + 1)
    rw [show (S.K + 1) * (1 / (4 * (S.K + 1))) = 1 / 4 by field_simp] at this
    exact this
  obtain ⟨C', CB, hC', hCB, hML⟩ := main_lower S hn hε hrs hrsR hrs1 hεrs hKrs
  refine ⟨ε, rs, max 1 (8 * CJ ^ 2 / S.lam ^ 2 + (2 * CJ * S.K ^ 2 / S.lam ^ 2 + C')),
    coreC S.lam S.K CJ CB, hε, hrs, hrsR, hrs1, hεrs, le_max_left _ _,
    coreC_pos hlam hK hCJ0 hCB, ?_⟩
  intro τ hτ f Df δ hδ hfs hDfs hf2 hgrad hfc hDfc hPi
  have hadm : Admissible rs δ f Df := ⟨hδ, hfs, hDfs, hf2, hgrad, hfc, hDfc⟩
  have hτ1 : 1 ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ' : 8 * CJ ^ 2 / S.lam ^ 2 + (2 * CJ * S.K ^ 2 / S.lam ^ 2 + C') ≤ τ :=
    le_trans (le_max_right _ _) hτ
  have hml := hML τ hτ1 f Df δ hadm hPi
  rw [← hCJ] at hml
  have hgc := grad_control S hε hrs hrsR hrs1 hεrs hKrs hτ1 hadm hPi
  have hbf := back_to_f hε.le hεrs (τ := τ) hadm
  have ha : 4 * CJ * S.K / S.lam + 2 ≤ 2 * ((81 / 128) * ε - 5 * S.K ^ 2) := by
    have ht : 0 ≤ CJ * S.K / S.lam := by positivity
    rw [hεdef]
    simp only [div_eq_mul_inv] at ht ⊢
    nlinarith [sq_nonneg S.K]
  have hX0 : 0 ≤ IX ε τ f :=
    setIntegral_nonneg (F1.measurableSet_halfSpace 0) fun x _ => by
      have := muR_nonneg x
      positivity
  have hY0 : 0 ≤ IY ε τ f Df :=
    setIntegral_nonneg (F1.measurableSet_halfSpace 0) fun x _ => by
      have := muR_nonneg x
      positivity
  have hS0 : 0 ≤ ISg S ε τ f :=
    setIntegral_nonneg (F1.measurableSet_halfSpace 0) fun x _ => by
      have := muR_nonneg x
      positivity
  have hP0 : 0 ≤ IPP S ε τ f :=
    setIntegral_nonneg (F1.measurableSet_halfSpace 0) fun x _ => by
      have := muR_nonneg x
      positivity
  have hB0 : 0 ≤ IBd S ε τ f Df :=
    integral_nonneg fun y => by
      have := muR_nonneg (lift y 0)
      positivity
  exact core_algebra hlam hK hCJ0 hC' hCB ha hτ1 hτ' hX0 hY0 hS0 hB0 hP0 hml hgc hbf

end W_R_carleman

/-- **Lemma R2 (Carleman estimate with Neumann boundary terms), in `x` coordinates.**
For `f` supported in an annulus `δ ≤ ρ ≤ rs`, `C²` in the open half-space and `C¹` up to
`{t = 0}`, with `|P₀ f| ≤ |F| + K₁ ρ (ρ |∇f| + |f|)`:
`τ³ ∫ ρ μ e^{2τφ} f² + τ ∫ ρ³ μ e^{2τφ} |∇f|²`
`≤ C₅ ∫ μ e^{2τφ} F² + C₅ τ² ∫_{t=0} ρ² μ e^{2τφ} |⟪A ∇f, e_d⟫| (ρ |∇f| + |f|)`.
Every boundary term contains the conormal derivative `⟪A ∇f, e_d⟫`. -/
theorem carleman (S : HalfBallSolution n) (hn : 0 < n) (K₁ : ℝ) (hK₁ : 0 ≤ K₁) :
    ∃ ε rs τ₀ C₅ : ℝ, 0 < ε ∧ 0 < rs ∧ rs < S.R ∧ rs ≤ 1 ∧ ε * rs ≤ 1 / 4 ∧ 1 ≤ τ₀ ∧
      0 < C₅ ∧
      ∀ τ : ℝ, τ₀ ≤ τ → ∀ (f F : Space n → ℝ) (Df : Space n → Space n) (δ : ℝ), 0 < δ →
        (∀ x, f x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs) →
        (∀ x, Df x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ rs) →
        (∀ x, 0 < vcoord x → ContDiffAt ℝ 2 f x) →
        (∀ x, 0 < vcoord x → gradient f x = Df x) →
        ContinuousOn f {x | 0 ≤ vcoord x} → ContinuousOn Df {x | 0 ≤ vcoord x} →
        IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * F x ^ 2)
          {x | 0 < vcoord x} →
        (∀ x, 0 < vcoord x → |P0R S.A f x| ≤ |F x| + K₁ * ‖x‖ * (‖x‖ * ‖Df x‖ + |f x|)) →
        τ ^ 3 * (∫ x in {x : Space n | 0 < vcoord x},
            ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
          + τ * (∫ x in {x : Space n | 0 < vcoord x},
            ‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2)
        ≤ C₅ * (∫ x in {x : Space n | 0 < vcoord x},
            muR n x * Real.exp (2 * τ * phiR ε x) * F x ^ 2)
          + C₅ * τ ^ 2 * (∫ y : EuclideanSpace ℝ (Fin n),
            ‖lift y 0‖ ^ 2 * muR n (lift y 0) * Real.exp (2 * τ * phiR ε (lift y 0)) *
              (|⟪S.A (lift y 0) (Df (lift y 0)), ed n⟫_ℝ| *
                (‖lift y 0‖ * ‖Df (lift y 0)‖ + |f (lift y 0)|))) := by
  obtain ⟨ε, rs, τ₁, C, hε, hrs, hrsR, hrs1, hεrs, hτ₁, hC, hcore⟩ := W_R_carleman.core S hn
  refine ⟨ε, rs, max τ₁ (8 * C * K₁ ^ 2 + 1), 4 * C, hε, hrs, hrsR, hrs1, hεrs,
    le_trans hτ₁ (le_max_left _ _), by positivity, ?_⟩
  intro τ hτ f F Df δ hδ hfs hDfs hf2 hgrad hfc hDfc hFi hP0
  have hτ₁' : τ₁ ≤ τ := le_trans (le_max_left _ _) hτ
  have hτK : 8 * C * K₁ ^ 2 + 1 ≤ τ := le_trans (le_max_right _ _) hτ
  have hτ1 : 1 ≤ τ := le_trans hτ₁ hτ₁'
  have hΩm : MeasurableSet {x : Space n | 0 < vcoord x} := F1.measurableSet_halfSpace 0
  -- integrability of the two left-hand integrands
  have hXi : IntegrableOn (fun x => ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2)
      {x | 0 < vcoord x} := by
    refine W_R_carleman.integrableOn_of_annulus (rs := rs) hδ (fun x hx => ?_) fun x hx hx0 => ?_
    · have : f x ≠ 0 := by
        intro h; apply hx; simp [h]
      exact hfs x this
    · have hw := W_R_carleman.continuousAt_weight ε τ hx0
      have h1 : ContinuousAt (fun y : Space n => ‖y‖ * (muR n y * Real.exp (2 * τ * phiR ε y)))
          x := continuous_norm.continuousAt.mul hw
      have h2 := h1.continuousWithinAt (s := {x : Space n | 0 ≤ vcoord x}).mul
        ((hfc x hx).pow 2)
      refine h2.congr (fun y _ => ?_) ?_
      · simp only [Pi.mul_apply, Pi.pow_apply]
        ring
      · simp only [Pi.mul_apply, Pi.pow_apply]
        ring
  have hYi : IntegrableOn (fun x => ‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2)
      {x | 0 < vcoord x} := by
    refine W_R_carleman.integrableOn_of_annulus (rs := rs) hδ (fun x hx => ?_) fun x hx hx0 => ?_
    · have : Df x ≠ 0 := by
        intro h; apply hx; simp [h]
      exact hDfs x this
    · have hw := W_R_carleman.continuousAt_weight ε τ hx0
      have h1 : ContinuousAt
          (fun y : Space n => ‖y‖ ^ 3 * (muR n y * Real.exp (2 * τ * phiR ε y))) x :=
        (continuous_norm.continuousAt.pow 3).mul hw
      have h2 := h1.continuousWithinAt (s := {x : Space n | 0 ≤ vcoord x}).mul
        ((hDfc x hx).norm.pow 2)
      refine h2.congr (fun y _ => ?_) ?_
      · simp only [Pi.mul_apply, Pi.pow_apply]
        ring
      · simp only [Pi.mul_apply, Pi.pow_apply]
        ring
  -- the pointwise bound for `P₀ f`
  have hpt : ∀ x ∈ {x : Space n | 0 < vcoord x},
      muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2
        ≤ 2 * (muR n x * Real.exp (2 * τ * phiR ε x) * F x ^ 2)
          + 4 * K₁ ^ 2 * (‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2)
          + 4 * K₁ ^ 2 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2) := by
    intro x hx
    have h1 : ‖x‖ ^ 4 * ‖Df x‖ ^ 2 ≤ ‖x‖ ^ 3 * ‖Df x‖ ^ 2 := by
      by_cases h : Df x = 0
      · simp [h]
      · have hx1 : ‖x‖ ≤ 1 := (hDfs x h).2.trans hrs1
        have : ‖x‖ ^ 4 ≤ ‖x‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hx1 (by norm_num)
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h2 : ‖x‖ ^ 2 * f x ^ 2 ≤ ‖x‖ * f x ^ 2 := by
      by_cases h : f x = 0
      · simp [h]
      · have hx1 : ‖x‖ ≤ 1 := (hfs x h).2.trans hrs1
        have : ‖x‖ ^ 2 ≤ ‖x‖ := by nlinarith [norm_nonneg x]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have key := W_R_carleman.ptwise_real (norm_nonneg x) hK₁ (norm_nonneg _) (hP0 x hx) h1 h2
    have hw0 : 0 ≤ muR n x * Real.exp (2 * τ * phiR ε x) :=
      mul_nonneg (W_R_carleman.muR_nonneg x) (Real.exp_pos _).le
    have h3 := mul_le_mul_of_nonneg_left key hw0
    calc muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2
        = muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2 := rfl
      _ ≤ muR n x * Real.exp (2 * τ * phiR ε x) * (2 * F x ^ 2
            + 4 * K₁ ^ 2 * (‖x‖ ^ 3 * ‖Df x‖ ^ 2) + 4 * K₁ ^ 2 * (‖x‖ * f x ^ 2)) := h3
      _ = _ := by ring
  -- measurability and integrability of `μ e^{2τφ} (P₀ f)²`
  have hPc : ContinuousOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
      {x | 0 < vcoord x} := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp [vcoord] at hx
    exact (W_R_carleman.continuousAt_weight ε τ hx0).continuousWithinAt.mul
      ((W_R_carleman.continuousOn_P0R S hf2 x hx).pow 2)
  have hFi2 : IntegrableOn (fun x => 2 * (muR n x * Real.exp (2 * τ * phiR ε x) * F x ^ 2))
      {x | 0 < vcoord x} := hFi.const_mul 2
  have hYi2 : IntegrableOn (fun x =>
      4 * K₁ ^ 2 * (‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2))
      {x | 0 < vcoord x} := hYi.const_mul _
  have hXi2 : IntegrableOn (fun x =>
      4 * K₁ ^ 2 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2))
      {x | 0 < vcoord x} := hXi.const_mul _
  have hFY : IntegrableOn (fun x =>
      2 * (muR n x * Real.exp (2 * τ * phiR ε x) * F x ^ 2)
        + 4 * K₁ ^ 2 * (‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2))
      {x | 0 < vcoord x} := hFi2.add hYi2
  have hbdi : IntegrableOn (fun x =>
      2 * (muR n x * Real.exp (2 * τ * phiR ε x) * F x ^ 2)
        + 4 * K₁ ^ 2 * (‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2)
        + 4 * K₁ ^ 2 * (‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2))
      {x | 0 < vcoord x} := hFY.add hXi2
  have hPi : IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2)
      {x | 0 < vcoord x} := by
    refine Integrable.mono' hbdi (hPc.aestronglyMeasurable hΩm) ?_
    refine (ae_restrict_iff' hΩm).2 (Eventually.of_forall fun x hx => ?_)
    have h0 : 0 ≤ muR n x * Real.exp (2 * τ * phiR ε x) * P0R S.A f x ^ 2 :=
      mul_nonneg (mul_nonneg (W_R_carleman.muR_nonneg x) (Real.exp_pos _).le) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hpt x hx
  have hc := hcore τ hτ₁' f Df δ hδ hfs hDfs hf2 hgrad hfc hDfc hPi
  have hPle := setIntegral_mono_on hPi hbdi hΩm hpt
  rw [integral_add hFY hXi2, integral_add hFi2 hYi2, integral_const_mul, integral_const_mul,
    integral_const_mul] at hPle
  -- nonnegativity
  have hX0 : 0 ≤ ∫ x in {x : Space n | 0 < vcoord x},
      ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * f x ^ 2 :=
    setIntegral_nonneg hΩm fun x _ => by
      have := W_R_carleman.muR_nonneg x
      positivity
  have hY0 : 0 ≤ ∫ x in {x : Space n | 0 < vcoord x},
      ‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖Df x‖ ^ 2 :=
    setIntegral_nonneg hΩm fun x _ => by
      have := W_R_carleman.muR_nonneg x
      positivity
  have hB0 : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin n),
      ‖lift y 0‖ ^ 2 * muR n (lift y 0) * Real.exp (2 * τ * phiR ε (lift y 0)) *
        (|⟪S.A (lift y 0) (Df (lift y 0)), ed n⟫_ℝ| *
          (‖lift y 0‖ * ‖Df (lift y 0)‖ + |f (lift y 0)|)) :=
    integral_nonneg fun y => by
      have := W_R_carleman.muR_nonneg (lift y 0)
      positivity
  exact W_R_carleman.final_algebra hτ1 hτK hC hX0 hY0 hB0 hc hPle

namespace W_R_transfer

/-! ### Helpers for `transfer` (fully proved)

With `h = ψ ρ^m`, `g = ρ^m` and `f = h v`:
* `P0R_eq`: `P₀ u = ρ² div(A∇u) + (1 - n) ⟪x, A∇u⟫ - m² u` for `x ≠ 0`;
* `div_A_grad_mul`: the product rule for `div(A∇(u w))`;
* `div_A_grad_norm_rpow`: `div(A∇ρ^p) = p ρ^{p-2} div(A x) + p (p-2) ρ^{p-4} ⟪x, A x x⟫`;
* `P0_identity`: the exact identity for `P₀ f` after the equation `div(A∇v) = -⟪B,∇v⟫ - C v`
  (the `⟪A x, ∇v⟫` and `⟪A x, ∇ψ⟫` terms cancel by the symmetry of `A`);
* `div_A_x_bound`, `inner_A_x_x_bound`, `P0g_bound`: `|P₀ ρ^m| ≤ C_g K ρ^{m+1}` from `A 0 = I`
  and `|DA| ≤ K`;
* `div_A_grad_bound`: `|div(A∇ψ)| ≤ d K (|∇ψ| + |∇²ψ|)`;
* `final_real`: the closing real inequality. -/

/-- Derivative of `‖y‖^p` away from `0`. -/
theorem hasFDerivAt_norm_rpow' {x : Space n} (hx : x ≠ 0) (p : ℝ) :
    HasFDerivAt (fun y : Space n => ‖y‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  have e : (fun y : Space n => ‖y‖ ^ p) = fun y => (‖y‖ ^ 2) ^ (p / 2) := by
    funext y
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
    congr 1
    push_cast
    ring
  have hd : HasFDerivAt (fun y : Space n => (‖y‖ ^ 2) ^ (p / 2))
      ((p / 2 * (‖x‖ ^ 2) ^ (p / 2 - 1)) • (2 • innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
      (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.2 hx)))
  have h2 : (‖x‖ ^ 2) ^ (p / 2 - 1) = ‖x‖ ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
    congr 1
    push_cast
    ring
  rw [e]
  refine hd.congr_fderiv ?_
  rw [h2]
  ext v
  simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem gradient_norm_rpow' {x : Space n} (hx : x ≠ 0) (p : ℝ) :
    gradient (fun y : Space n => ‖y‖ ^ p) x = (p * ‖x‖ ^ (p - 2)) • x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, (hasFDerivAt_norm_rpow' hx p).fderiv]
  simp [real_inner_smul_left]

theorem contDiffAt_norm_rpow {x : Space n} (hx : x ≠ 0) (p : ℝ) {k : ℕ∞ω} :
    ContDiffAt ℝ k (fun y : Space n => ‖y‖ ^ p) x :=
  (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.2 hx)

/-- Gradient of a product (copied from `RPkg.gradient_mul'`). -/
theorem gradient_mul' {f h : Space n → ℝ} {x : Space n} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) :
    gradient (fun y => f y * h y) x = f x • gradient h x + h x • gradient f x := by
  have hd : HasFDerivAt (fun y => f y * h y) (f x • fderiv ℝ h x + h x • fderiv ℝ f x) x :=
    hf.hasFDerivAt.mul hh.hasFDerivAt
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, hd.fderiv, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, inner_gradient_left, inner_gradient_left]
  simp [smul_eq_mul]

/-- `|tr L| ≤ d ‖L‖`. -/
theorem abs_trace_le (L : Space n →L[ℝ] Space n) :
    |LinearMap.trace ℝ (Space n) (L : Space n →ₗ[ℝ] Space n)| ≤ ((n : ℝ) + 1) * ‖L‖ := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ i, |⟪(EuclideanSpace.basisFun (Fin (n + 1)) ℝ) i,
      (L : Space n →ₗ[ℝ] Space n) ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ) i)⟫_ℝ| ≤ ‖L‖ := by
    intro i
    have h1 : ‖(EuclideanSpace.basisFun (Fin (n + 1)) ℝ) i‖ = 1 :=
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).orthonormal.1 i
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [h1, one_mul]
    simpa [h1] using L.le_opNorm ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ) i)
  refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
  simp

theorem abs_divergence_le (F : Space n → Space n) (x : Space n) :
    |divergence F x| ≤ ((n : ℝ) + 1) * ‖fderiv ℝ F x‖ :=
  abs_trace_le _

/-- `|A(x) - I| ≤ K |x|`. -/
theorem norm_A_sub_id_le (S : HalfBallSolution n) (x : Space n) :
    ‖S.A x - ContinuousLinearMap.id ℝ (Space n)‖ ≤ S.K * ‖x‖ := by
  have hd : Differentiable ℝ S.A := S.coeffs.contDiff_A.differentiable (by norm_num)
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun y _ => hd y)
    (fun y _ => S.coeffs.bound_dA y) (Set.mem_univ 0) (Set.mem_univ x)
  rwa [S.A_zero, sub_zero] at h

theorem K_nonneg (S : HalfBallSolution n) : 0 ≤ S.K :=
  le_trans (norm_nonneg _) (S.coeffs.bound_A 0)


/-- `P₀ u = ρ² div(A∇u) + (1 - n) ⟪x, A∇u⟫ - m² u` away from `0`. -/
theorem P0R_eq (A : Space n → Space n →L[ℝ] Space n) (u : Space n → ℝ) {x : Space n}
    (hx : x ≠ 0) (hW : DifferentiableAt ℝ (fun y => A y (gradient u y)) x) :
    P0R A u x = ‖x‖ ^ 2 * divergence (fun y => A y (gradient u y)) x
      + (1 - (n : ℝ)) * ⟪x, A x (gradient u x)⟫_ℝ - mR n ^ 2 * u x := by
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hfield : (fun y => muR n y • BR A y (gradient u y))
      = fun y => (muR n y * ‖y‖ ^ 2) • A y (gradient u y) := by
    funext y
    simp only [BR, _root_.smul_apply, smul_smul]
  have hs : (fun y : Space n => muR n y * ‖y‖ ^ 2) =ᶠ[𝓝 x]
      fun y => ‖y‖ ^ (1 - (n : ℝ)) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    simp only [muR]
    rw [Real.rpow_sub hy', Real.rpow_one, Real.rpow_natCast]
    field_simp
    ring
  have hsd : HasFDerivAt (fun y : Space n => muR n y * ‖y‖ ^ 2)
      (((1 - (n : ℝ)) * ‖x‖ ^ ((1 - (n : ℝ)) - 2)) • innerSL ℝ x) x :=
    (hasFDerivAt_norm_rpow' hx _).congr_of_eventuallyEq hs
  have hr : ‖x‖ ^ ((1 - (n : ℝ)) - 2) = (‖x‖ ^ (n + 1))⁻¹ := by
    rw [show (1 - (n : ℝ)) - 2 = -((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hρ.le,
      Real.rpow_natCast]
  unfold P0R divMu
  rw [hfield, F2.divergence_smul hsd.differentiableAt hW, hsd.fderiv]
  simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul, muR, inv_inv]
  rw [hr]
  field_simp

/-- The product rule `div(A∇(u w)) = u div(A∇w) + w div(A∇u) + ⟪∇u, A∇w⟫ + ⟪∇w, A∇u⟫`. -/
theorem div_A_grad_mul (A : Space n → Space n →L[ℝ] Space n) (hA : Differentiable ℝ A)
    {u w : Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u x) (hw : ContDiffAt ℝ 2 w x) :
    divergence (fun y => A y (gradient (fun z => u z * w z) y)) x
      = u x * divergence (fun y => A y (gradient w y)) x
        + w x * divergence (fun y => A y (gradient u y)) x
        + ⟪gradient u x, A x (gradient w x)⟫_ℝ + ⟪gradient w x, A x (gradient u x)⟫_ℝ := by
  have hu1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y := by
    filter_upwards [hu.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hw1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ w y := by
    filter_upwards [hw.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hev : (fun y => A y (gradient (fun z => u z * w z) y)) =ᶠ[𝓝 x]
      fun y => u y • A y (gradient w y) + w y • A y (gradient u y) := by
    filter_upwards [hu1, hw1] with y hy1 hy2
    rw [gradient_mul' hy1 hy2, map_add, map_smul, map_smul]
  rw [F2.divergence_congr hev]
  have hAd : DifferentiableAt ℝ A x := hA x
  have hgu : DifferentiableAt ℝ (gradient u) x := F2.differentiableAt_gradient hu
  have hgw : DifferentiableAt ℝ (gradient w) x := F2.differentiableAt_gradient hw
  have hAgu : DifferentiableAt ℝ (fun y => A y (gradient u y)) x := hAd.clm_apply hgu
  have hAgw : DifferentiableAt ℝ (fun y => A y (gradient w y)) x := hAd.clm_apply hgw
  have hud : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hwd : DifferentiableAt ℝ w x := hw.differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fun y => u y • A y (gradient w y)) x := hud.smul hAgw
  have h2 : DifferentiableAt ℝ (fun y => w y • A y (gradient u y)) x := hwd.smul hAgu
  rw [F2.divergence_add h1 h2, F2.divergence_smul hud hAgw,
    F2.divergence_smul hwd hAgu, ← inner_gradient_left, ← inner_gradient_left]
  ring


/-- `|div(A x) - d| ≤ 2 d K |x|`, from `A 0 = I` and `|DA| ≤ K`. -/
theorem div_A_x_bound (S : HalfBallSolution n) (x : Space n) :
    |divergence (fun y => S.A y y) x - ((n : ℝ) + 1)| ≤ 2 * ((n : ℝ) + 1) * S.K * ‖x‖ := by
  have hAd : DifferentiableAt ℝ S.A x := (S.coeffs.contDiff_A.differentiable (by norm_num)) x
  have hD : HasFDerivAt (fun y => S.A y y)
      ((S.A x).comp (ContinuousLinearMap.id ℝ (Space n)) + (fderiv ℝ S.A x).flip x) x :=
    hAd.hasFDerivAt.clm_apply (hasFDerivAt_id x)
  have hid : F2.traceCLM (ContinuousLinearMap.id ℝ (Space n)) = (n : ℝ) + 1 := by
    rw [F2.traceCLM_apply, ContinuousLinearMap.coe_id, LinearMap.trace_id,
      finrank_euclideanSpace, Fintype.card_fin]
    push_cast
    ring
  have htr : divergence (fun y => S.A y y) x - ((n : ℝ) + 1)
      = F2.traceCLM ((S.A x - ContinuousLinearMap.id ℝ (Space n))
          + (fderiv ℝ S.A x).flip x) := by
    rw [F2.divergence_eq_traceCLM, hD.fderiv, ContinuousLinearMap.comp_id, map_add, map_add,
      map_sub, hid]
    ring
  rw [htr, F2.traceCLM_apply]
  refine (abs_trace_le _).trans ?_
  have h1 := norm_A_sub_id_le S x
  have h2 : ‖(fderiv ℝ S.A x).flip x‖ ≤ S.K * ‖x‖ := by
    refine (ContinuousLinearMap.le_opNorm _ x).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_mul_of_nonneg_right (S.coeffs.bound_dA x) (norm_nonneg _)
  have h3 := norm_add_le (S.A x - ContinuousLinearMap.id ℝ (Space n))
    ((fderiv ℝ S.A x).flip x)
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h4 : ‖(S.A x - ContinuousLinearMap.id ℝ (Space n)) + (fderiv ℝ S.A x).flip x‖
      ≤ 2 * S.K * ‖x‖ := by linarith
  calc ((n : ℝ) + 1) * ‖(S.A x - ContinuousLinearMap.id ℝ (Space n)) + (fderiv ℝ S.A x).flip x‖
      ≤ ((n : ℝ) + 1) * (2 * S.K * ‖x‖) := mul_le_mul_of_nonneg_left h4 hn
    _ = 2 * ((n : ℝ) + 1) * S.K * ‖x‖ := by ring

/-- `|div(A ∇ψ)| ≤ d (K |∇ψ| + K |∇²ψ|)`. -/
theorem div_A_grad_bound (S : HalfBallSolution n) {ψ : Space n → ℝ} {x : Space n}
    (hψ : DifferentiableAt ℝ (gradient ψ) x) :
    |divergence (fun y => S.A y (gradient ψ y)) x|
      ≤ ((n : ℝ) + 1) * (S.K * ‖gradient ψ x‖ + S.K * ‖fderiv ℝ (gradient ψ) x‖) := by
  have hAd : DifferentiableAt ℝ S.A x := (S.coeffs.contDiff_A.differentiable (by norm_num)) x
  have hD : HasFDerivAt (fun y => S.A y (gradient ψ y))
      ((S.A x).comp (fderiv ℝ (gradient ψ) x) + (fderiv ℝ S.A x).flip (gradient ψ x)) x :=
    hAd.hasFDerivAt.clm_apply hψ.hasFDerivAt
  refine (abs_divergence_le _ x).trans ?_
  rw [hD.fderiv]
  have h1 : ‖(S.A x).comp (fderiv ℝ (gradient ψ) x)‖ ≤ S.K * ‖fderiv ℝ (gradient ψ) x‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (S.coeffs.bound_A x) (norm_nonneg _))
  have h2 : ‖(fderiv ℝ S.A x).flip (gradient ψ x)‖ ≤ S.K * ‖gradient ψ x‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_mul_of_nonneg_right (S.coeffs.bound_dA x) (norm_nonneg _)
  have h3 := norm_add_le ((S.A x).comp (fderiv ℝ (gradient ψ) x))
    ((fderiv ℝ S.A x).flip (gradient ψ x))
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hn

/-- `div(A ∇ρ^p) = p ρ^{p-2} div(A x) + p (p-2) ρ^{p-4} ⟪x, A x x⟫`. -/
theorem div_A_grad_norm_rpow (A : Space n → Space n →L[ℝ] Space n) (hA : Differentiable ℝ A)
    {x : Space n} (hx : x ≠ 0) (p : ℝ) :
    divergence (fun y => A y (gradient (fun z : Space n => ‖z‖ ^ p) y)) x
      = p * ‖x‖ ^ (p - 2) * divergence (fun y => A y y) x
        + p * ((p - 2) * ‖x‖ ^ (p - 2 - 2)) * ⟪x, A x x⟫_ℝ := by
  have hev : (fun y => A y (gradient (fun z : Space n => ‖z‖ ^ p) y)) =ᶠ[𝓝 x]
      fun y => (p * ‖y‖ ^ (p - 2)) • A y y := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [gradient_norm_rpow' hy, map_smul]
  rw [F2.divergence_congr hev]
  have hs : HasFDerivAt (fun y : Space n => p * ‖y‖ ^ (p - 2))
      (p • (((p - 2) * ‖x‖ ^ (p - 2 - 2)) • innerSL ℝ x)) x :=
    (hasFDerivAt_norm_rpow' hx (p - 2)).const_mul p
  have hAx : DifferentiableAt ℝ (fun y => A y y) x := (hA x).clm_apply differentiableAt_id
  rw [F2.divergence_smul hs.differentiableAt hAx, hs.fderiv]
  simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- The final real inequality. -/
theorem final_real {K ρ t Gf af gψ Hψ av Dv m' Cg nn : ℝ} (hK : 0 ≤ K) (hρ : 0 ≤ ρ)
    (ht : 0 ≤ t) (hGf : 0 ≤ Gf) (haf : 0 ≤ af) (hgψ : 0 ≤ gψ) (hHψ : 0 ≤ Hψ) (hav : 0 ≤ av)
    (hDv : 0 ≤ Dv) (hm' : 0 ≤ m') (hCg : 0 ≤ Cg) (hnn : 0 ≤ nn) :
    ρ ^ 2 * (K * Gf) + ρ * (K * af) + ρ * t * av * (K * gψ) + m' * af * (K * ρ)
        + 2 * ρ ^ 2 * t * (K * gψ * Dv) + Cg * K * ρ * af
        + (nn + 1) * K * t * av * (ρ * gψ + ρ ^ 2 * Hψ)
      ≤ K * (2 + m' + Cg) * ρ * (ρ * Gf + af)
        + K * (nn + 4) * (ρ * gψ + ρ ^ 2 * Hψ) * (t * (av + ρ * Dv)) := by
  have e : K * (2 + m' + Cg) * ρ * (ρ * Gf + af)
        + K * (nn + 4) * (ρ * gψ + ρ ^ 2 * Hψ) * (t * (av + ρ * Dv))
      - (ρ ^ 2 * (K * Gf) + ρ * (K * af) + ρ * t * av * (K * gψ) + m' * af * (K * ρ)
        + 2 * ρ ^ 2 * t * (K * gψ * Dv) + Cg * K * ρ * af
        + (nn + 1) * K * t * av * (ρ * gψ + ρ ^ 2 * Hψ))
      = K * (1 + m' + Cg) * ρ ^ 2 * Gf + K * ρ * af
        + K * (2 * ρ * t * av * gψ + (nn + 2) * ρ ^ 2 * t * gψ * Dv
          + 3 * ρ ^ 2 * t * av * Hψ + (nn + 4) * ρ ^ 3 * t * Hψ * Dv) := by ring
  have h : 0 ≤ K * (1 + m' + Cg) * ρ ^ 2 * Gf + K * ρ * af
        + K * (2 * ρ * t * av * gψ + (nn + 2) * ρ ^ 2 * t * gψ * Dv
          + 3 * ρ ^ 2 * t * av * Hψ + (nn + 4) * ρ ^ 3 * t * Hψ * Dv) := by positivity
  linarith


theorem ne_zero_of_mem_halfBall {R : ℝ} {x : Space n} (hx : x ∈ halfBall n R) : x ≠ 0 := by
  intro h
  have h2 := hx.2
  rw [h] at h2
  simp [vcoord] at h2

/-- The exact identity for `P₀(ψ ρ^m v)`, after using the equation for `v`. -/
theorem P0_identity (S : HalfBallSolution n) {ψ : Space n → ℝ} {x : Space n}
    (hx : x ∈ halfBall n S.R) (hψ : ContDiffAt ℝ 2 ψ x) :
    P0R S.A (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x
      = -(‖x‖ ^ 2 * ⟪S.B x, gradient (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x⟫_ℝ)
        - ‖x‖ ^ 2 * S.C x * (ψ x * ‖x‖ ^ mR n * S.v x)
        + ‖x‖ ^ 2 * ‖x‖ ^ mR n * S.v x * ⟪S.B x, gradient ψ x⟫_ℝ
        + mR n * (ψ x * ‖x‖ ^ mR n * S.v x) * ⟪S.B x, x⟫_ℝ
        + 2 * ‖x‖ ^ 2 * ‖x‖ ^ mR n * ⟪gradient ψ x, S.A x (S.Dv x)⟫_ℝ
        + S.v x * ψ x * (mR n * ‖x‖ ^ mR n * (divergence (fun y => S.A y y) x - ((n : ℝ) + 1))
            - mR n * (mR n + 2) * (‖x‖ ^ mR n / ‖x‖ ^ 2) * (⟪x, S.A x x⟫_ℝ - ‖x‖ ^ 2))
        + S.v x * ‖x‖ ^ 2 * ‖x‖ ^ mR n * divergence (fun y => S.A y (gradient ψ y)) x := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_halfBall hx
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hv : ContDiffAt ℝ 2 S.v x :=
    S.v_contDiffOn.contDiffAt ((isOpen_halfBall S.R).mem_nhds hx)
  have hg : ContDiffAt ℝ 2 (fun y : Space n => ‖y‖ ^ mR n) x := contDiffAt_norm_rpow hx0 _
  have hh : ContDiffAt ℝ 2 (fun y => ψ y * ‖y‖ ^ mR n) x := hψ.mul hg
  have hf : ContDiffAt ℝ 2 (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x := hh.mul hv
  have hA : Differentiable ℝ S.A := S.coeffs.contDiff_A.differentiable (by norm_num)
  have e1 := P0R_eq S.A (fun y => ψ y * ‖y‖ ^ mR n * S.v y) hx0
    ((hA x).clm_apply (F2.differentiableAt_gradient hf))
  have e2 := div_A_grad_mul S.A hA hh hv
  have e3 := div_A_grad_mul S.A hA hψ hg
  have e4 := div_A_grad_norm_rpow S.A hA hx0 (mR n)
  have g1 := gradient_mul' (hh.differentiableAt (by norm_num))
    (hv.differentiableAt (by norm_num))
  have g2 := gradient_mul' (hψ.differentiableAt (by norm_num))
    (hg.differentiableAt (by norm_num))
  have g3 := gradient_norm_rpow' hx0 (mR n)
  have heq := S.eqn x hx
  have hDv := S.gradient_eq x hx
  simp only [ellOp] at heq
  rw [hDv] at heq
  have hLv : divergence (fun y => S.A y (gradient S.v y)) x
      = -⟪S.B x, S.Dv x⟫_ℝ - S.C x * S.v x := by linarith
  have s1 : ⟪S.Dv x, S.A x (gradient ψ x)⟫_ℝ = ⟪gradient ψ x, S.A x (S.Dv x)⟫_ℝ := by
    rw [real_inner_comm, S.coeffs.symm]
  have s2 : ⟪S.Dv x, S.A x x⟫_ℝ = ⟪x, S.A x (S.Dv x)⟫_ℝ := by
    rw [real_inner_comm, S.coeffs.symm]
  have s3 : ⟪gradient ψ x, S.A x x⟫_ℝ = ⟪x, S.A x (gradient ψ x)⟫_ℝ := by
    rw [real_inner_comm, S.coeffs.symm]
  have r1 : ‖x‖ ^ (mR n - 2) = ‖x‖ ^ mR n / ‖x‖ ^ 2 := by
    rw [Real.rpow_sub hρ, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have r2 : ‖x‖ ^ (mR n - 2 - 2) = ‖x‖ ^ mR n / ‖x‖ ^ 4 := by
    rw [show mR n - 2 - 2 = mR n - ((4 : ℕ) : ℝ) by push_cast; ring, Real.rpow_sub hρ,
      Real.rpow_natCast]
  have hn : (n : ℝ) = 2 * mR n + 1 := by unfold mR; ring
  rw [e1, e2, e3, e4, g1, g2, g3, hDv, hLv]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, s1, s2, s3]
  rw [r1, r2, hn]
  field_simp
  ring


/-- `|⟪x, A x x⟫ - |x|²| ≤ K |x|³`. -/
theorem inner_A_x_x_bound (S : HalfBallSolution n) (x : Space n) :
    |⟪x, S.A x x⟫_ℝ - ‖x‖ ^ 2| ≤ S.K * ‖x‖ ^ 3 := by
  have e : ⟪x, S.A x x⟫_ℝ - ‖x‖ ^ 2
      = ⟪x, (S.A x - ContinuousLinearMap.id ℝ (Space n)) x⟫_ℝ := by
    rw [_root_.sub_apply, inner_sub_right, ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
  rw [e]
  have h1 : ‖(S.A x - ContinuousLinearMap.id ℝ (Space n)) x‖ ≤ S.K * ‖x‖ * ‖x‖ :=
    ((S.A x - ContinuousLinearMap.id ℝ (Space n)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (norm_A_sub_id_le S x) (norm_nonneg _))
  calc |⟪x, (S.A x - ContinuousLinearMap.id ℝ (Space n)) x⟫_ℝ|
      ≤ ‖x‖ * ‖(S.A x - ContinuousLinearMap.id ℝ (Space n)) x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (S.K * ‖x‖ * ‖x‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = S.K * ‖x‖ ^ 3 := by ring

/-- `|⟪a, A x b⟫| ≤ K |a| |b|`. -/
theorem inner_A_bound (S : HalfBallSolution n) (x a b : Space n) :
    |⟪a, S.A x b⟫_ℝ| ≤ S.K * ‖a‖ * ‖b‖ := by
  have h1 : ‖S.A x b‖ ≤ S.K * ‖b‖ :=
    ((S.A x).le_opNorm b).trans (mul_le_mul_of_nonneg_right (S.coeffs.bound_A x) (norm_nonneg _))
  calc |⟪a, S.A x b⟫_ℝ| ≤ ‖a‖ * ‖S.A x b‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖a‖ * (S.K * ‖b‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = S.K * ‖a‖ * ‖b‖ := by ring

/-- `|⟪B, a⟫| ≤ K |a|`. -/
theorem inner_B_bound (S : HalfBallSolution n) (x a : Space n) :
    |⟪S.B x, a⟫_ℝ| ≤ S.K * ‖a‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (S.coeffs.bound_B x) (norm_nonneg _))

/-- The bound `|P₀ ρ^m| ≤ C_g K ρ^{m+1}` in the form used by `transfer`. -/
theorem P0g_bound (S : HalfBallSolution n) {x : Space n} (hx0 : x ≠ 0) :
    |mR n * ‖x‖ ^ mR n * (divergence (fun y => S.A y y) x - ((n : ℝ) + 1))
        - mR n * (mR n + 2) * (‖x‖ ^ mR n / ‖x‖ ^ 2) * (⟪x, S.A x x⟫_ℝ - ‖x‖ ^ 2)|
      ≤ (2 * ((n : ℝ) + 1) * |mR n| + |mR n * (mR n + 2)|) * S.K * ‖x‖ ^ mR n * ‖x‖ := by
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have ht : 0 ≤ ‖x‖ ^ mR n := Real.rpow_nonneg (norm_nonneg _) _
  have hK := K_nonneg S
  have i1 : |mR n * ‖x‖ ^ mR n * (divergence (fun y => S.A y y) x - ((n : ℝ) + 1))|
      ≤ |mR n| * ‖x‖ ^ mR n * (2 * ((n : ℝ) + 1) * S.K * ‖x‖) := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (div_A_x_bound S x) (by positivity)
  have i2 : |mR n * (mR n + 2) * (‖x‖ ^ mR n / ‖x‖ ^ 2) * (⟪x, S.A x x⟫_ℝ - ‖x‖ ^ 2)|
      ≤ |mR n * (mR n + 2)| * (‖x‖ ^ mR n / ‖x‖ ^ 2) * (S.K * ‖x‖ ^ 3) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ mR n / ‖x‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left (inner_A_x_x_bound S x) (by positivity)
  have i3 : |mR n * (mR n + 2)| * (‖x‖ ^ mR n / ‖x‖ ^ 2) * (S.K * ‖x‖ ^ 3)
      = |mR n * (mR n + 2)| * S.K * ‖x‖ ^ mR n * ‖x‖ := by
    field_simp
  have i4 := abs_sub (mR n * ‖x‖ ^ mR n * (divergence (fun y => S.A y y) x - ((n : ℝ) + 1)))
    (mR n * (mR n + 2) * (‖x‖ ^ mR n / ‖x‖ ^ 2) * (⟪x, S.A x x⟫_ℝ - ‖x‖ ^ 2))
  have i5 : |mR n| * ‖x‖ ^ mR n * (2 * ((n : ℝ) + 1) * S.K * ‖x‖)
      + |mR n * (mR n + 2)| * S.K * ‖x‖ ^ mR n * ‖x‖
      = (2 * ((n : ℝ) + 1) * |mR n| + |mR n * (mR n + 2)|) * S.K * ‖x‖ ^ mR n * ‖x‖ := by
    ring
  linarith

end W_R_transfer

/-- **The equation in cylinder form.** For a cutoff `ψ`, the equation for `v` bounds
`P₀(ψ ρ^m v)` by `K₁ ρ (ρ |∇f| + |f|)` plus commutator terms carrying `∇ψ` and `∇²ψ`. -/
theorem transfer (S : HalfBallSolution n) (hn : 0 < n) :
    ∃ K₁ CT : ℝ, 0 ≤ K₁ ∧ 0 ≤ CT ∧ ∀ (ψ : Space n → ℝ) (x : Space n), x ∈ halfBall n S.R →
      ‖x‖ ≤ 1 → ContDiffAt ℝ 2 ψ x →
      |P0R S.A (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x|
        ≤ K₁ * ‖x‖ * (‖x‖ * ‖gradient (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x‖
            + |ψ x * ‖x‖ ^ mR n * S.v x|)
          + CT * (‖x‖ * ‖gradient ψ x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient ψ) x‖) *
            (‖x‖ ^ mR n * (|S.v x| + ‖x‖ * ‖S.Dv x‖)) := by
  have hK := W_R_transfer.K_nonneg S
  have hCg0 : 0 ≤ 2 * ((n : ℝ) + 1) * |mR n| + |mR n * (mR n + 2)| := by positivity
  refine ⟨S.K * (2 + |mR n| + (2 * ((n : ℝ) + 1) * |mR n| + |mR n * (mR n + 2)|)),
    S.K * ((n : ℝ) + 4), by positivity, by positivity, fun ψ x hx hx1 hψ => ?_⟩
  have hx0 : x ≠ 0 := W_R_transfer.ne_zero_of_mem_halfBall hx
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have ht : 0 ≤ ‖x‖ ^ mR n := Real.rpow_nonneg (norm_nonneg _) _
  have hρ2 : ‖x‖ ^ 2 ≤ ‖x‖ := by nlinarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [W_R_transfer.P0_identity S hx hψ]
  -- the seven terms
  have hT1 : |‖x‖ ^ 2 * ⟪S.B x, gradient (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x⟫_ℝ|
      ≤ ‖x‖ ^ 2 * (S.K * ‖gradient (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x‖) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
    exact mul_le_mul_of_nonneg_left (W_R_transfer.inner_B_bound S x _) (sq_nonneg _)
  have hT2 : |‖x‖ ^ 2 * S.C x * (ψ x * ‖x‖ ^ mR n * S.v x)|
      ≤ ‖x‖ * (S.K * |ψ x * ‖x‖ ^ mR n * S.v x|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
    have hC := S.coeffs.bound_C x
    calc ‖x‖ ^ 2 * |S.C x| * |ψ x * ‖x‖ ^ mR n * S.v x|
        ≤ ‖x‖ * S.K * |ψ x * ‖x‖ ^ mR n * S.v x| := by gcongr
      _ = ‖x‖ * (S.K * |ψ x * ‖x‖ ^ mR n * S.v x|) := by ring
  have hT3 : |‖x‖ ^ 2 * ‖x‖ ^ mR n * S.v x * ⟪S.B x, gradient ψ x⟫_ℝ|
      ≤ ‖x‖ * ‖x‖ ^ mR n * |S.v x| * (S.K * ‖gradient ψ x‖) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖), abs_of_nonneg ht]
    have hB := W_R_transfer.inner_B_bound S x (gradient ψ x)
    gcongr
  have hT4 : |mR n * (ψ x * ‖x‖ ^ mR n * S.v x) * ⟪S.B x, x⟫_ℝ|
      ≤ |mR n| * |ψ x * ‖x‖ ^ mR n * S.v x| * (S.K * ‖x‖) := by
    rw [abs_mul, abs_mul]
    have hB := W_R_transfer.inner_B_bound S x x
    gcongr
  have hT5 : |2 * ‖x‖ ^ 2 * ‖x‖ ^ mR n * ⟪gradient ψ x, S.A x (S.Dv x)⟫_ℝ|
      ≤ 2 * ‖x‖ ^ 2 * ‖x‖ ^ mR n * (S.K * ‖gradient ψ x‖ * ‖S.Dv x‖) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖x‖ ^ 2 * ‖x‖ ^ mR n)]
    exact mul_le_mul_of_nonneg_left (W_R_transfer.inner_A_bound S x _ _) (by positivity)
  have hT6 : |S.v x * ψ x * (mR n * ‖x‖ ^ mR n * (divergence (fun y => S.A y y) x - ((n : ℝ) + 1))
        - mR n * (mR n + 2) * (‖x‖ ^ mR n / ‖x‖ ^ 2) * (⟪x, S.A x x⟫_ℝ - ‖x‖ ^ 2))|
      ≤ (2 * ((n : ℝ) + 1) * |mR n| + |mR n * (mR n + 2)|) * S.K * ‖x‖
          * |ψ x * ‖x‖ ^ mR n * S.v x| := by
    have hP := W_R_transfer.P0g_bound S hx0
    have hf0 : |ψ x * ‖x‖ ^ mR n * S.v x| = |ψ x| * ‖x‖ ^ mR n * |S.v x| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht]
    rw [abs_mul, abs_mul, hf0]
    calc |S.v x| * |ψ x| * |mR n * ‖x‖ ^ mR n * (divergence (fun y => S.A y y) x - ((n : ℝ) + 1))
          - mR n * (mR n + 2) * (‖x‖ ^ mR n / ‖x‖ ^ 2) * (⟪x, S.A x x⟫_ℝ - ‖x‖ ^ 2)|
        ≤ |S.v x| * |ψ x| * ((2 * ((n : ℝ) + 1) * |mR n| + |mR n * (mR n + 2)|) * S.K
            * ‖x‖ ^ mR n * ‖x‖) := mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (2 * ((n : ℝ) + 1) * |mR n| + |mR n * (mR n + 2)|) * S.K * ‖x‖
          * (|ψ x| * ‖x‖ ^ mR n * |S.v x|) := by ring
  have hT7 : |S.v x * ‖x‖ ^ 2 * ‖x‖ ^ mR n * divergence (fun y => S.A y (gradient ψ y)) x|
      ≤ ((n : ℝ) + 1) * S.K * ‖x‖ ^ mR n * |S.v x|
          * (‖x‖ * ‖gradient ψ x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient ψ) x‖) := by
    have hL := W_R_transfer.div_A_grad_bound S (F2.differentiableAt_gradient hψ)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖), abs_of_nonneg ht]
    have hρρ : 0 ≤ ‖x‖ - ‖x‖ ^ 2 := by linarith
    have hpos : 0 ≤ ((n : ℝ) + 1) * S.K * ‖x‖ ^ mR n * |S.v x|
        * ((‖x‖ - ‖x‖ ^ 2) * ‖gradient ψ x‖) := by
      have := norm_nonneg (gradient ψ x)
      positivity
    calc |S.v x| * ‖x‖ ^ 2 * ‖x‖ ^ mR n * |divergence (fun y => S.A y (gradient ψ y)) x|
        ≤ |S.v x| * ‖x‖ ^ 2 * ‖x‖ ^ mR n * (((n : ℝ) + 1) * (S.K * ‖gradient ψ x‖
            + S.K * ‖fderiv ℝ (gradient ψ) x‖)) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ ≤ ((n : ℝ) + 1) * S.K * ‖x‖ ^ mR n * |S.v x|
          * (‖x‖ * ‖gradient ψ x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient ψ) x‖) := by
        nlinarith [hpos]
  have hfin := W_R_transfer.final_real (K := S.K) (ρ := ‖x‖) (t := ‖x‖ ^ mR n)
    (Gf := ‖gradient (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x‖)
    (af := |ψ x * ‖x‖ ^ mR n * S.v x|) (gψ := ‖gradient ψ x‖)
    (Hψ := ‖fderiv ℝ (gradient ψ) x‖) (av := |S.v x|) (Dv := ‖S.Dv x‖) (m' := |mR n|)
    (Cg := 2 * ((n : ℝ) + 1) * |mR n| + |mR n * (mR n + 2)|) (nn := (n : ℝ)) hK hρ.le ht
    (norm_nonneg _) (abs_nonneg _) (norm_nonneg _) (norm_nonneg _) (abs_nonneg _)
    (norm_nonneg _) (abs_nonneg _) hCg0 (Nat.cast_nonneg n)
  obtain ⟨h1a, h1b⟩ := abs_le.mp hT1
  obtain ⟨h2a, h2b⟩ := abs_le.mp hT2
  obtain ⟨h3a, h3b⟩ := abs_le.mp hT3
  obtain ⟨h4a, h4b⟩ := abs_le.mp hT4
  obtain ⟨h5a, h5b⟩ := abs_le.mp hT5
  obtain ⟨h6a, h6b⟩ := abs_le.mp hT6
  obtain ⟨h7a, h7b⟩ := abs_le.mp hT7
  refine (abs_le.mpr ⟨?_, ?_⟩).trans hfin
  · linarith
  · linarith

/-! ### The cutoff of Step 1 and the function `f = ψ_δ ρ^m v` -/

/-- `Θ_in(t) = S((4t - 1) / 3)`: equal to `0` for `t ≤ 1/4` and to `1` for `t ≥ 1`. -/
noncomputable def thetaIn (t : ℝ) : ℝ := Real.smoothTransition ((4 * t - 1) / 3)

/-- The cutoff of Step 1: `0` for `ρ ≤ δ/2`, `1` on `[δ, r₁/2]`, `0` for `ρ ≥ r₁`. -/
noncomputable def psiS (δ r₁ : ℝ) (x : Space n) : ℝ :=
  thetaIn (‖x‖ ^ 2 / δ ^ 2) * (1 - thetaIn (‖x‖ ^ 2 / r₁ ^ 2))

/-- `h = ψ_δ ρ^m`. -/
noncomputable def hS (δ r₁ : ℝ) (x : Space n) : ℝ := psiS δ r₁ x * ‖x‖ ^ mR n

/-- `f = ψ_δ ρ^m v`. -/
noncomputable def fS (S : HalfBallSolution n) (δ r₁ : ℝ) (x : Space n) : ℝ :=
  psiS δ r₁ x * ‖x‖ ^ mR n * S.v x

/-- The continuous extension of `∇f` up to `{t = 0}`: `h Dv + v ∇h`. -/
noncomputable def DfS (S : HalfBallSolution n) (δ r₁ : ℝ) (x : Space n) : Space n :=
  hS δ r₁ x • S.Dv x + S.v x • gradient (hS δ r₁) x

/-- The commutator bound of `transfer` for `ψ = ψ_δ`. -/
noncomputable def FS (S : HalfBallSolution n) (CT δ r₁ : ℝ) (x : Space n) : ℝ :=
  CT * (‖x‖ * ‖gradient (psiS δ r₁) x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) x‖) *
    (‖x‖ ^ mR n * (|S.v x| + ‖x‖ * ‖S.Dv x‖))

theorem thetaIn_contDiff : ContDiff ℝ ∞ thetaIn := by
  unfold thetaIn
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const 3)

theorem thetaIn_eq_zero {t : ℝ} (ht : t ≤ 1 / 4) : thetaIn t = 0 := by
  unfold thetaIn
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem thetaIn_eq_one {t : ℝ} (ht : 1 ≤ t) : thetaIn t = 1 := by
  unfold thetaIn
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem thetaIn_nonneg (t : ℝ) : 0 ≤ thetaIn t := Real.smoothTransition.nonneg _

theorem thetaIn_le_one (t : ℝ) : thetaIn t ≤ 1 := Real.smoothTransition.le_one _

theorem psiS_contDiff (δ r₁ : ℝ) : ContDiff ℝ ∞ (psiS (n := n) δ r₁) := by
  unfold psiS
  exact (thetaIn_contDiff.comp ((contDiff_norm_sq ℝ).div_const _)).mul
    (contDiff_const.sub (thetaIn_contDiff.comp ((contDiff_norm_sq ℝ).div_const _)))

theorem psiS_eq_zero_of_le {δ r₁ : ℝ} (hδ : 0 < δ) {x : Space n} (hx : ‖x‖ ≤ δ / 2) :
    psiS δ r₁ x = 0 := by
  unfold psiS
  rw [thetaIn_eq_zero, zero_mul]
  rw [div_le_iff₀ (by positivity)]
  have h0 := norm_nonneg x
  nlinarith

theorem psiS_eq_zero_of_ge {δ r₁ : ℝ} (hr₁ : 0 < r₁) {x : Space n} (hx : r₁ ≤ ‖x‖) :
    psiS δ r₁ x = 0 := by
  unfold psiS
  rw [thetaIn_eq_one (t := ‖x‖ ^ 2 / r₁ ^ 2), sub_self, mul_zero]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem psiS_eq_one {δ r₁ : ℝ} (hδ : 0 < δ) (hr₁ : 0 < r₁) {x : Space n} (hx1 : δ ≤ ‖x‖)
    (hx2 : ‖x‖ ≤ r₁ / 2) : psiS δ r₁ x = 1 := by
  unfold psiS
  rw [thetaIn_eq_one, thetaIn_eq_zero, sub_zero, mul_one]
  · rw [div_le_iff₀ (by positivity)]
    have h0 := norm_nonneg x
    nlinarith
  · rw [le_div_iff₀ (by positivity)]
    nlinarith

theorem psiS_nonneg (δ r₁ : ℝ) (x : Space n) : 0 ≤ psiS δ r₁ x := by
  unfold psiS
  exact mul_nonneg (thetaIn_nonneg _) (by linarith [thetaIn_le_one (‖x‖ ^ 2 / r₁ ^ 2)])

theorem psiS_le_one (δ r₁ : ℝ) (x : Space n) : psiS δ r₁ x ≤ 1 := by
  unfold psiS
  have h1 := thetaIn_nonneg (‖x‖ ^ 2 / δ ^ 2)
  have h2 := thetaIn_le_one (‖x‖ ^ 2 / δ ^ 2)
  have h3 := thetaIn_nonneg (‖x‖ ^ 2 / r₁ ^ 2)
  have h4 := thetaIn_le_one (‖x‖ ^ 2 / r₁ ^ 2)
  nlinarith

/-- The gradient of a locally constant function vanishes nearby. -/
theorem gradient_eventuallyEq_zero {f : Space n → ℝ} {x : Space n} {c : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) : gradient f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h.eventually_nhds] with y hy
  have : fderiv ℝ f y = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hy]
    exact fderiv_const_apply c
  simp [gradient, this]

theorem gradient_and_hessian_zero_of_locally_const {f : Space n → ℝ} {x : Space n} {c : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) :
    gradient f x = 0 ∧ fderiv ℝ (gradient f) x = 0 := by
  have hg := gradient_eventuallyEq_zero h
  refine ⟨hg.eq_of_nhds, ?_⟩
  rw [Filter.EventuallyEq.fderiv_eq hg]
  exact fderiv_const_apply _

/-- Gradient of a product. -/
theorem gradient_mul' {f h : Space n → ℝ} {x : Space n} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) :
    gradient (fun y => f y * h y) x = f x • gradient h x + h x • gradient f x := by
  have hd : HasFDerivAt (fun y => f y * h y) (f x • fderiv ℝ h x + h x • fderiv ℝ f x) x :=
    hf.hasFDerivAt.mul hh.hasFDerivAt
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, hd.fderiv, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, inner_gradient_left, inner_gradient_left]
  simp [smul_eq_mul]

/-- `ρ ↦ -log ρ + ερ` is nonincreasing on `(0, 1/ε]`. -/
theorem phi_antitone {ε ρ r : ℝ} (_hε : 0 ≤ ε) (hρ : 0 < ρ) (hρr : ρ ≤ r) (hεr : ε * r ≤ 1) :
    -Real.log r + ε * r ≤ -Real.log ρ + ε * ρ := by
  have hr : 0 < r := lt_of_lt_of_le hρ hρr
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hr hρ)
  rw [Real.log_div hr.ne' hρ.ne', inv_div] at h1
  -- `ε (r - ρ) ≤ (r - ρ) / r = 1 - ρ / r`
  have h2 : ε * (r - ρ) ≤ 1 - ρ / r := by
    have e : 1 - ρ / r = (r - ρ) / r := by field_simp
    rw [e, le_div_iff₀ hr]
    have : 0 ≤ r - ρ := by linarith
    nlinarith
  linarith

theorem hasFDerivAt_comp_normsq {Θ : ℝ → ℝ} (hΘ : Differentiable ℝ Θ) (c : ℝ) (x : Space n) :
    HasFDerivAt (fun y : Space n => Θ (‖y‖ ^ 2 / c ^ 2))
      ((deriv Θ (‖x‖ ^ 2 / c ^ 2) * (2 / c ^ 2)) • innerSL ℝ x) x := by
  have h1 : HasFDerivAt (fun y : Space n => ‖y‖ ^ 2 / c ^ 2)
      ((1 / c ^ 2) • (2 • innerSL ℝ x)) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const ((c ^ 2)⁻¹)
  have h := (hΘ (‖x‖ ^ 2 / c ^ 2)).hasDerivAt.comp_hasFDerivAt x h1
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem gradient_comp_normsq {Θ : ℝ → ℝ} (hΘ : Differentiable ℝ Θ) (c : ℝ) (x : Space n) :
    gradient (fun y : Space n => Θ (‖y‖ ^ 2 / c ^ 2)) x
      = (deriv Θ (‖x‖ ^ 2 / c ^ 2) * (2 / c ^ 2)) • x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, (hasFDerivAt_comp_normsq hΘ c x).fderiv]
  simp [real_inner_smul_left]

theorem thetaIn_differentiable : Differentiable ℝ thetaIn :=
  thetaIn_contDiff.differentiable (by simp)

theorem deriv_thetaIn_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv thetaIn t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := smoothTransition_deriv_bound
  refine ⟨4 / 3 * C, by positivity, fun t => ?_⟩
  have hd : HasDerivAt thetaIn (deriv Real.smoothTransition ((4 * t - 1) / 3) * (4 / 3)) t := by
    have h1 : HasDerivAt (fun t : ℝ => (4 * t - 1) / 3) (4 / 3) t := by
      have := (((hasDerivAt_id t).const_mul 4).sub_const 1).div_const 3
      simpa using this
    exact ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
      ((4 * t - 1) / 3)).hasDerivAt.comp t h1
  rw [hd.deriv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
  have := hC ((4 * t - 1) / 3)
  nlinarith

theorem deriv_thetaIn_eq_zero {t : ℝ} (ht : 1 < t) : deriv thetaIn t = 0 := by
  have heq : thetaIn =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact thetaIn_eq_one (le_of_lt hs)
  rw [heq.deriv_eq, deriv_const]

/-- `∇ψ_δ` is radial with `ρ |∇ψ_δ| ≤ 4C`. -/
theorem gradient_psiS (δ r₁ : ℝ) (x : Space n) :
    gradient (psiS δ r₁) x
      = (thetaIn (‖x‖ ^ 2 / δ ^ 2) * (-deriv thetaIn (‖x‖ ^ 2 / r₁ ^ 2) * (2 / r₁ ^ 2))
          + (1 - thetaIn (‖x‖ ^ 2 / r₁ ^ 2)) * (deriv thetaIn (‖x‖ ^ 2 / δ ^ 2) * (2 / δ ^ 2)))
        • x := by
  have hd1 : Differentiable ℝ (fun t : ℝ => 1 - thetaIn t) :=
    (differentiable_const 1).sub thetaIn_differentiable
  have hF₁ : DifferentiableAt ℝ (fun y : Space n => thetaIn (‖y‖ ^ 2 / δ ^ 2)) x :=
    (hasFDerivAt_comp_normsq thetaIn_differentiable δ x).differentiableAt
  have hF₂ : DifferentiableAt ℝ (fun y : Space n => 1 - thetaIn (‖y‖ ^ 2 / r₁ ^ 2)) x :=
    (hasFDerivAt_comp_normsq hd1 r₁ x).differentiableAt
  have e : psiS (n := n) δ r₁
      = fun y => thetaIn (‖y‖ ^ 2 / δ ^ 2) * (1 - thetaIn (‖y‖ ^ 2 / r₁ ^ 2)) := rfl
  have hderiv : deriv (fun t : ℝ => 1 - thetaIn t) (‖x‖ ^ 2 / r₁ ^ 2)
      = -deriv thetaIn (‖x‖ ^ 2 / r₁ ^ 2) := by
    rw [deriv_const_sub]
  rw [e, gradient_mul' hF₁ hF₂, gradient_comp_normsq thetaIn_differentiable δ x]
  have h2 := gradient_comp_normsq hd1 r₁ x
  rw [h2, hderiv, smul_smul, smul_smul, ← add_smul]

theorem norm_mul_gradient_psiS_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ r₁ : ℝ), 0 < δ → 0 < r₁ →
    ∀ x : Space n, ‖x‖ * ‖gradient (psiS δ r₁) x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := deriv_thetaIn_bound
  refine ⟨4 * C, by positivity, fun δ r₁ hδ hr₁ x => ?_⟩
  -- each term `‖x‖² |θ'(‖x‖²/c²)| (2/c²)` is at most `2C`
  have key : ∀ c : ℝ, 0 < c → ‖x‖ ^ 2 * (|deriv thetaIn (‖x‖ ^ 2 / c ^ 2)| * (2 / c ^ 2)) ≤ 2 * C := by
    intro c hc
    by_cases h : 1 < ‖x‖ ^ 2 / c ^ 2
    · rw [deriv_thetaIn_eq_zero h, abs_zero, zero_mul, mul_zero]
      positivity
    · push Not at h
      rw [div_le_one (by positivity)] at h
      have hc2 : 0 < c ^ 2 := by positivity
      calc ‖x‖ ^ 2 * (|deriv thetaIn (‖x‖ ^ 2 / c ^ 2)| * (2 / c ^ 2))
          ≤ c ^ 2 * (C * (2 / c ^ 2)) := by
            gcongr
            exact hC _
        _ = 2 * C := by field_simp
  have k1 := key δ hδ
  have k2 := key r₁ hr₁
  rw [gradient_psiS, norm_smul, Real.norm_eq_abs]
  have hA := thetaIn_nonneg (‖x‖ ^ 2 / δ ^ 2)
  have hA' := thetaIn_le_one (‖x‖ ^ 2 / δ ^ 2)
  have hB := thetaIn_nonneg (‖x‖ ^ 2 / r₁ ^ 2)
  have hB' := thetaIn_le_one (‖x‖ ^ 2 / r₁ ^ 2)
  set a := deriv thetaIn (‖x‖ ^ 2 / r₁ ^ 2)
  set b := deriv thetaIn (‖x‖ ^ 2 / δ ^ 2)
  set p := thetaIn (‖x‖ ^ 2 / δ ^ 2)
  set q := thetaIn (‖x‖ ^ 2 / r₁ ^ 2)
  have habs : |p * (-a * (2 / r₁ ^ 2)) + (1 - q) * (b * (2 / δ ^ 2))|
      ≤ |a| * (2 / r₁ ^ 2) + |b| * (2 / δ ^ 2) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hA,
        abs_of_pos (by positivity : (0 : ℝ) < 2 / r₁ ^ 2)]
      have : 0 ≤ |a| * (2 / r₁ ^ 2) := by positivity
      nlinarith
    · rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - q),
        abs_of_pos (by positivity : (0 : ℝ) < 2 / δ ^ 2)]
      have : 0 ≤ |b| * (2 / δ ^ 2) := by positivity
      nlinarith
  have hx2 : ‖x‖ * (|p * (-a * (2 / r₁ ^ 2)) + (1 - q) * (b * (2 / δ ^ 2))| * ‖x‖)
      ≤ ‖x‖ ^ 2 * (|a| * (2 / r₁ ^ 2) + |b| * (2 / δ ^ 2)) := by
    have := mul_le_mul_of_nonneg_left habs (sq_nonneg ‖x‖)
    nlinarith
  linarith

theorem gradient_norm_rpow {x : Space n} (hx : x ≠ 0) (p : ℝ) :
    gradient (fun y : Space n => ‖y‖ ^ p) x = (p * (‖x‖ ^ 2) ^ (p / 2 - 1)) • x := by
  have e : (fun y : Space n => ‖y‖ ^ p) = fun y => (‖y‖ ^ 2) ^ (p / 2) := by
    funext y
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
    congr 1
    push_cast
    ring
  have hd : HasFDerivAt (fun y : Space n => (‖y‖ ^ 2) ^ (p / 2))
      ((p / 2 * (‖x‖ ^ 2) ^ (p / 2 - 1)) • (2 • innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
      (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.2 hx)))
  rw [e]
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    real_inner_smul_left]
  push_cast
  ring

namespace W_R_psiS

/-! Helpers for `psiS_deriv_bound`.

Write `t = ‖x‖²`, `s_c = t / c²`. By `gradient_psiS`, `∇ψ_δ(x) = aProf δ r₁ (‖x‖²) • x` with the
one-variable profile `aProf`. Hence `D∇ψ_δ(x) = aProf(t) I + 2 aProf'(t) x ⊗ x`, so
`‖x‖ ‖∇ψ_δ‖ + ‖x‖² ‖D∇ψ_δ‖ ≤ 2 t |aProf t| + 2 t² |aProf' t|`, and both `t aProf(t)` and
`t² aProf'(t)` are polynomials in `Θ(s_c)`, `s_c Θ'(s_c)`, `s_c² Θ''(s_c)`, which are bounded since
`Θ'`, `Θ''` vanish for `s > 1`. -/

theorem contDiff_deriv_thetaIn : ContDiff ℝ ∞ (deriv thetaIn) :=
  (contDiff_infty_iff_deriv.1 thetaIn_contDiff).2

theorem differentiable_deriv_thetaIn : Differentiable ℝ (deriv thetaIn) :=
  contDiff_deriv_thetaIn.differentiable (by simp)

theorem deriv_thetaIn_eq_zero_of_lt {t : ℝ} (ht : t < 1 / 4) : deriv thetaIn t = 0 := by
  have heq : thetaIn =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact thetaIn_eq_zero (le_of_lt hs)
  rw [heq.deriv_eq, deriv_const]

theorem deriv2_thetaIn_eq_zero_of_lt {t : ℝ} (ht : t < 1 / 4) :
    deriv (deriv thetaIn) t = 0 := by
  have heq : deriv thetaIn =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact deriv_thetaIn_eq_zero_of_lt hs
  rw [heq.deriv_eq, deriv_const]

theorem deriv2_thetaIn_eq_zero {t : ℝ} (ht : 1 < t) : deriv (deriv thetaIn) t = 0 := by
  have heq : deriv thetaIn =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact deriv_thetaIn_eq_zero hs
  rw [heq.deriv_eq, deriv_const]

theorem deriv2_thetaIn_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv (deriv thetaIn) t| ≤ C := by
  have hc : Continuous (deriv (deriv thetaIn)) :=
    contDiff_deriv_thetaIn.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 / 4 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases h0 : t < 1 / 4
  · rw [deriv2_thetaIn_eq_zero_of_lt h0, abs_zero]
    exact le_max_right _ _
  by_cases h1 : 1 < t
  · rw [deriv2_thetaIn_eq_zero h1, abs_zero]
    exact le_max_right _ _
  push Not at h0 h1
  have := hC t ⟨h0, h1⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Scale-invariant bounds `|s Θ'(s)| ≤ C₁`, `|s² Θ''(s)| ≤ C₂` for `s ≥ 0`. -/
theorem scaled_deriv_bounds : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    (∀ s, 0 ≤ s → |s * deriv thetaIn s| ≤ C₁) ∧
    (∀ s, 0 ≤ s → |s ^ 2 * deriv (deriv thetaIn) s| ≤ C₂) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := deriv_thetaIn_bound
  obtain ⟨C₂, hC₂, hb₂⟩ := deriv2_thetaIn_bound
  refine ⟨C₁, C₂, hC₁, hC₂, fun s hs => ?_, fun s hs => ?_⟩
  · by_cases h : 1 < s
    · rw [deriv_thetaIn_eq_zero h, mul_zero, abs_zero]
      exact hC₁
    · push Not at h
      rw [abs_mul, abs_of_nonneg hs]
      calc s * |deriv thetaIn s| ≤ 1 * C₁ := mul_le_mul h (hb₁ s) (abs_nonneg _) zero_le_one
        _ = C₁ := one_mul _
  · by_cases h : 1 < s
    · rw [deriv2_thetaIn_eq_zero h, mul_zero, abs_zero]
      exact hC₂
    · push Not at h
      rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
      have h2 : s ^ 2 ≤ 1 := by nlinarith
      calc s ^ 2 * |deriv (deriv thetaIn) s| ≤ 1 * C₂ :=
            mul_le_mul h2 (hb₂ s) (abs_nonneg _) zero_le_one
        _ = C₂ := one_mul _

/-- The radial profile of `∇ψ_δ`: `∇ψ_δ(x) = aProf δ r₁ (‖x‖²) • x`. -/
noncomputable def aProf (δ r₁ t : ℝ) : ℝ :=
  thetaIn (t / δ ^ 2) * (-deriv thetaIn (t / r₁ ^ 2) * (2 / r₁ ^ 2))
    + (1 - thetaIn (t / r₁ ^ 2)) * (deriv thetaIn (t / δ ^ 2) * (2 / δ ^ 2))

/-- The derivative of `aProf δ r₁` in `t`. -/
noncomputable def aProf' (δ r₁ t : ℝ) : ℝ :=
  deriv thetaIn (t / δ ^ 2) / δ ^ 2 * (-deriv thetaIn (t / r₁ ^ 2) * (2 / r₁ ^ 2))
    + thetaIn (t / δ ^ 2) * (-(deriv (deriv thetaIn) (t / r₁ ^ 2) / r₁ ^ 2) * (2 / r₁ ^ 2))
    + (-(deriv thetaIn (t / r₁ ^ 2) / r₁ ^ 2) * (deriv thetaIn (t / δ ^ 2) * (2 / δ ^ 2))
      + (1 - thetaIn (t / r₁ ^ 2)) * (deriv (deriv thetaIn) (t / δ ^ 2) / δ ^ 2 * (2 / δ ^ 2)))

theorem hasDerivAt_comp_div {Θ : ℝ → ℝ} (hΘ : Differentiable ℝ Θ) (c t : ℝ) :
    HasDerivAt (fun s => Θ (s / c ^ 2)) (deriv Θ (t / c ^ 2) / c ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => s / c ^ 2) (1 / c ^ 2) t := (hasDerivAt_id' t).div_const _
  have h := (hΘ (t / c ^ 2)).hasDerivAt.comp t h1
  exact h.congr_deriv (by ring)

theorem hasDerivAt_aProf (δ r₁ t : ℝ) : HasDerivAt (aProf δ r₁) (aProf' δ r₁ t) t := by
  have h1 := hasDerivAt_comp_div thetaIn_differentiable δ t
  have h2 := hasDerivAt_comp_div differentiable_deriv_thetaIn r₁ t
  have h3 := hasDerivAt_comp_div thetaIn_differentiable r₁ t
  have h4 := hasDerivAt_comp_div differentiable_deriv_thetaIn δ t
  exact (h1.mul (h2.neg.mul_const (2 / r₁ ^ 2))).add
    ((h3.const_sub 1).mul (h4.mul_const (2 / δ ^ 2)))

theorem gradient_psiS_eq (δ r₁ : ℝ) :
    gradient (psiS (n := n) δ r₁) = fun y => aProf δ r₁ (‖y‖ ^ 2) • y := by
  funext y
  rw [gradient_psiS]
  rfl

theorem hasFDerivAt_gradient_psiS (δ r₁ : ℝ) (x : Space n) :
    HasFDerivAt (gradient (psiS (n := n) δ r₁))
      (aProf δ r₁ (‖x‖ ^ 2) • ContinuousLinearMap.id ℝ (Space n)
        + (aProf' δ r₁ (‖x‖ ^ 2) • (2 • innerSL ℝ x)).smulRight x) x := by
  rw [gradient_psiS_eq]
  have hc : HasFDerivAt (fun y : Space n => aProf δ r₁ (‖y‖ ^ 2))
      (aProf' δ r₁ (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x := by
    have h := (hasDerivAt_aProf δ r₁ (‖x‖ ^ 2)).comp_hasFDerivAt x
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    exact h
  have h := hc.smul (hasFDerivAt_id x)
  exact h

theorem norm_fderiv_gradient_psiS_le (δ r₁ : ℝ) (x : Space n) :
    ‖fderiv ℝ (gradient (psiS (n := n) δ r₁)) x‖
      ≤ |aProf δ r₁ (‖x‖ ^ 2)| + 2 * |aProf' δ r₁ (‖x‖ ^ 2)| * ‖x‖ ^ 2 := by
  rw [(hasFDerivAt_gradient_psiS δ r₁ x).fderiv]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    have h1 : ‖aProf' δ r₁ (‖x‖ ^ 2) • (2 • innerSL ℝ x)‖ ≤ |aProf' δ r₁ (‖x‖ ^ 2)| * (2 * ‖x‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      rw [two_nsmul]
      refine (norm_add_le _ _).trans ?_
      rw [innerSL_apply_norm]
      linarith
    calc ‖aProf' δ r₁ (‖x‖ ^ 2) • (2 • innerSL ℝ x)‖ * ‖x‖
        ≤ |aProf' δ r₁ (‖x‖ ^ 2)| * (2 * ‖x‖) * ‖x‖ := by gcongr
      _ = 2 * |aProf' δ r₁ (‖x‖ ^ 2)| * ‖x‖ ^ 2 := by ring

/-- Bounds for `|P v|` with `0 ≤ P ≤ 1`. -/
theorem abs_mul_le_of_unit {P v C : ℝ} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hv : |v| ≤ C) :
    |P * v| ≤ C := by
  rw [abs_mul, abs_of_nonneg hP0]
  calc P * |v| ≤ 1 * C := mul_le_mul hP1 hv (abs_nonneg _) zero_le_one
    _ = C := one_mul _

theorem real_bounds {P Q u v U V C₁ C₂ : ℝ} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hQ0 : 0 ≤ Q)
    (hQ1 : Q ≤ 1) (hu : |u| ≤ C₁) (hv : |v| ≤ C₁) (hU : |U| ≤ C₂) (hV : |V| ≤ C₂) :
    |-2 * P * v + 2 * (1 - Q) * u| ≤ 4 * C₁ ∧
      |-4 * u * v - 2 * P * V + 2 * (1 - Q) * U| ≤ 4 * C₁ ^ 2 + 4 * C₂ := by
  have hQ0' : 0 ≤ 1 - Q := by linarith
  have hQ1' : 1 - Q ≤ 1 := by linarith
  have a1 := abs_mul_le_of_unit hP0 hP1 hv
  have a2 := abs_mul_le_of_unit hQ0' hQ1' hu
  have a3 := abs_mul_le_of_unit hP0 hP1 hV
  have a4 := abs_mul_le_of_unit hQ0' hQ1' hU
  have a5 : |u * v| ≤ C₁ ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hu hv (abs_nonneg _) ((abs_nonneg u).trans hu)
  constructor
  · have e : -2 * P * v + 2 * (1 - Q) * u = -(2 * (P * v)) + 2 * ((1 - Q) * u) := by ring
    rw [e]
    have b1 : |-(2 * (P * v))| ≤ 2 * C₁ := by
      rw [abs_neg, abs_mul, abs_two]
      linarith
    have b2 : |2 * ((1 - Q) * u)| ≤ 2 * C₁ := by
      rw [abs_mul, abs_two]
      linarith
    linarith [abs_add_le (-(2 * (P * v))) (2 * ((1 - Q) * u))]
  · have e : -4 * u * v - 2 * P * V + 2 * (1 - Q) * U
        = -(4 * (u * v)) + -(2 * (P * V)) + 2 * ((1 - Q) * U) := by ring
    rw [e]
    have b1 : |-(4 * (u * v))| ≤ 4 * C₁ ^ 2 := by
      rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith
    have b2 : |-(2 * (P * V))| ≤ 2 * C₂ := by
      rw [abs_neg, abs_mul, abs_two]
      linarith
    have b3 : |2 * ((1 - Q) * U)| ≤ 2 * C₂ := by
      rw [abs_mul, abs_two]
      linarith
    linarith [abs_add_le (-(4 * (u * v)) + -(2 * (P * V))) (2 * ((1 - Q) * U)),
      abs_add_le (-(4 * (u * v))) (-(2 * (P * V)))]

theorem profile_bounds {C₁ C₂ : ℝ} (hb₁ : ∀ s, 0 ≤ s → |s * deriv thetaIn s| ≤ C₁)
    (hb₂ : ∀ s, 0 ≤ s → |s ^ 2 * deriv (deriv thetaIn) s| ≤ C₂)
    {δ r₁ t : ℝ} (hδ : 0 < δ) (hr₁ : 0 < r₁) (ht : 0 ≤ t) :
    |t * aProf δ r₁ t| ≤ 4 * C₁ ∧ |t ^ 2 * aProf' δ r₁ t| ≤ 4 * C₁ ^ 2 + 4 * C₂ := by
  have hsδ : 0 ≤ t / δ ^ 2 := by positivity
  have hsr : 0 ≤ t / r₁ ^ 2 := by positivity
  have e1 : t * aProf δ r₁ t
      = -2 * thetaIn (t / δ ^ 2) * (t / r₁ ^ 2 * deriv thetaIn (t / r₁ ^ 2))
        + 2 * (1 - thetaIn (t / r₁ ^ 2)) * (t / δ ^ 2 * deriv thetaIn (t / δ ^ 2)) := by
    unfold aProf
    field_simp
  have e2 : t ^ 2 * aProf' δ r₁ t
      = -4 * (t / δ ^ 2 * deriv thetaIn (t / δ ^ 2)) * (t / r₁ ^ 2 * deriv thetaIn (t / r₁ ^ 2))
        - 2 * thetaIn (t / δ ^ 2) * ((t / r₁ ^ 2) ^ 2 * deriv (deriv thetaIn) (t / r₁ ^ 2))
        + 2 * (1 - thetaIn (t / r₁ ^ 2))
          * ((t / δ ^ 2) ^ 2 * deriv (deriv thetaIn) (t / δ ^ 2)) := by
    unfold aProf'
    field_simp
    ring
  rw [e1, e2]
  exact real_bounds (thetaIn_nonneg _) (thetaIn_le_one _) (thetaIn_nonneg _) (thetaIn_le_one _)
    (hb₁ _ hsδ) (hb₁ _ hsr) (hb₂ _ hsδ) (hb₂ _ hsr)

end W_R_psiS

/-- Scale-invariant derivative bounds for `ψ_δ`, uniform in `δ` and `r₁`. -/
theorem psiS_deriv_bound : ∃ Cψ : ℝ, 0 ≤ Cψ ∧ ∀ δ r₁ : ℝ, 0 < δ → 4 * δ ≤ r₁ → ∀ x : Space n,
    ‖x‖ * ‖gradient (psiS δ r₁) x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) x‖ ≤ Cψ := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb₁, hb₂⟩ := W_R_psiS.scaled_deriv_bounds
  refine ⟨8 * C₁ + 8 * C₁ ^ 2 + 8 * C₂, by positivity, fun δ r₁ hδ hδr x => ?_⟩
  have hr₁ : 0 < r₁ := by linarith
  have hg : ‖x‖ * ‖gradient (psiS δ r₁) x‖ = |‖x‖ ^ 2 * W_R_psiS.aProf δ r₁ (‖x‖ ^ 2)| := by
    rw [W_R_psiS.gradient_psiS_eq, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg ‖x‖)]
    ring
  have hH := W_R_psiS.norm_fderiv_gradient_psiS_le δ r₁ x
  obtain ⟨h1, h2⟩ := W_R_psiS.profile_bounds hb₁ hb₂ hδ hr₁ (sq_nonneg ‖x‖)
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)] at h1
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖x‖ ^ 2) ^ 2)] at h2
  rw [hg, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
  have hx2 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  calc ‖x‖ ^ 2 * |W_R_psiS.aProf δ r₁ (‖x‖ ^ 2)|
        + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) x‖
      ≤ ‖x‖ ^ 2 * |W_R_psiS.aProf δ r₁ (‖x‖ ^ 2)|
        + ‖x‖ ^ 2 * (|W_R_psiS.aProf δ r₁ (‖x‖ ^ 2)|
          + 2 * |W_R_psiS.aProf' δ r₁ (‖x‖ ^ 2)| * ‖x‖ ^ 2) := by gcongr
    _ = 2 * (‖x‖ ^ 2 * |W_R_psiS.aProf δ r₁ (‖x‖ ^ 2)|)
        + 2 * ((‖x‖ ^ 2) ^ 2 * |W_R_psiS.aProf' δ r₁ (‖x‖ ^ 2)|) := by ring
    _ ≤ 2 * (4 * C₁) + 2 * (4 * C₁ ^ 2 + 4 * C₂) := by gcongr
    _ = 8 * C₁ + 8 * C₁ ^ 2 + 8 * C₂ := by ring

/-- `∇ψ_δ` and `∇²ψ_δ` vanish where `ψ_δ` is locally constant. -/
theorem psiS_deriv_eq_zero {δ r₁ : ℝ} (hδ : 0 < δ) (hδr : 4 * δ ≤ r₁) {x : Space n}
    (hx : ‖x‖ < δ / 2 ∨ (δ < ‖x‖ ∧ ‖x‖ < r₁ / 2) ∨ r₁ < ‖x‖) :
    gradient (psiS δ r₁) x = 0 ∧ fderiv ℝ (gradient (psiS δ r₁)) x = 0 := by
  have hr₁ : 0 < r₁ := by linarith
  rcases hx with hx | hx | hx
  · apply gradient_and_hessian_zero_of_locally_const (c := 0)
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact psiS_eq_zero_of_le hδ (le_of_lt hy)
  · apply gradient_and_hessian_zero_of_locally_const (c := 1)
    filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds hx] with y hy
    exact psiS_eq_one hδ hr₁ (le_of_lt hy.1) (le_of_lt hy.2)
  · apply gradient_and_hessian_zero_of_locally_const (c := 0)
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact psiS_eq_zero_of_ge hr₁ (le_of_lt hy)

/-- `h = ψ_δ ρ^m` is smooth (it vanishes near `0`). -/
theorem hS_contDiff {δ r₁ : ℝ} (hδ : 0 < δ) (_hn : 0 < n) : ContDiff ℝ ∞ (hS (n := n) δ r₁) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ‖x‖ < δ / 2
  · have hev : hS (n := n) δ r₁ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      simp [hS, psiS_eq_zero_of_le hδ (le_of_lt hy)]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · push Not at hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      linarith
    have h1 : ContDiffAt ℝ ∞ (fun y : Space n => ‖y‖ ^ mR n) x :=
      (contDiffAt_norm ℝ hx0).rpow_const_of_ne (norm_ne_zero_iff.2 hx0)
    exact (psiS_contDiff δ r₁).contDiffAt.mul h1

theorem hS_eq_zero {δ r₁ : ℝ} (hδ : 0 < δ) (hr₁ : 0 < r₁) {x : Space n}
    (hx : ‖x‖ ≤ δ / 2 ∨ r₁ ≤ ‖x‖) : hS δ r₁ x = 0 := by
  rcases hx with hx | hx
  · simp [hS, psiS_eq_zero_of_le hδ hx]
  · simp [hS, psiS_eq_zero_of_ge hr₁ hx]

theorem gradient_hS_eq_zero {δ r₁ : ℝ} (hδ : 0 < δ) (hr₁ : 0 < r₁) {x : Space n}
    (hx : ‖x‖ < δ / 2 ∨ r₁ < ‖x‖) : gradient (hS δ r₁) x = 0 := by
  rcases hx with hx | hx
  · refine (gradient_and_hessian_zero_of_locally_const (c := 0) ?_).1
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact hS_eq_zero hδ hr₁ (Or.inl (le_of_lt hy))
  · refine (gradient_and_hessian_zero_of_locally_const (c := 0) ?_).1
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact hS_eq_zero hδ hr₁ (Or.inr (le_of_lt hy))

theorem continuous_gradient_of_contDiff {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (gradient f) := by
  rw [F2.gradient_eq_comp]
  exact (F2.toDualSymmCLE (n := n)).continuous.comp (hf.continuous_fderiv (by simp))

/-- `∇h` is radial, vanishes where `ψ_δ` is locally zero, and `ρ |∇h| ≤ (Cψ + m) ρ^m`. -/
theorem gradient_hS (hn : 0 < n) : ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ δ r₁ : ℝ, 0 < δ → 4 * δ ≤ r₁ →
    ∀ x : Space n, (∃ c : ℝ, gradient (hS δ r₁) x = c • x) ∧
      ‖x‖ * ‖gradient (hS δ r₁) x‖ ≤ Ch * ‖x‖ ^ mR n ∧
      ((‖x‖ < δ / 2 ∨ r₁ < ‖x‖) → gradient (hS δ r₁) x = 0) := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := norm_mul_gradient_psiS_le (n := n)
  have hm : 0 ≤ mR n := by
    unfold mR
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨mR n + Cψ, by positivity, fun δ r₁ hδ hδr x => ?_⟩
  have hr₁ : 0 < r₁ := by linarith
  refine ⟨?_, ?_, fun hx => gradient_hS_eq_zero hδ hr₁ hx⟩
  · by_cases hx0 : x = 0
    · refine ⟨0, ?_⟩
      rw [zero_smul]
      exact gradient_hS_eq_zero hδ hr₁ (Or.inl (by rw [hx0, norm_zero]; positivity))
    · have hψd : DifferentiableAt ℝ (psiS (n := n) δ r₁) x :=
        ((psiS_contDiff δ r₁).differentiable (by simp)) x
      have hpd : DifferentiableAt ℝ (fun y : Space n => ‖y‖ ^ mR n) x :=
        ((contDiffAt_norm ℝ hx0 (n := 1)).rpow_const_of_ne
          (norm_ne_zero_iff.2 hx0)).differentiableAt one_ne_zero
      have e : hS (n := n) δ r₁ = fun y => psiS δ r₁ y * ‖y‖ ^ mR n := rfl
      rw [e, gradient_mul' hψd hpd, gradient_norm_rpow hx0, gradient_psiS, smul_smul, smul_smul,
        ← add_smul]
      exact ⟨_, rfl⟩
  · by_cases hx0 : x = 0
    · rw [hx0, norm_zero, zero_mul]
      positivity
    · have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hψd : DifferentiableAt ℝ (psiS (n := n) δ r₁) x :=
        ((psiS_contDiff δ r₁).differentiable (by simp)) x
      have hpd : DifferentiableAt ℝ (fun y : Space n => ‖y‖ ^ mR n) x :=
        ((contDiffAt_norm ℝ hx0 (n := 1)).rpow_const_of_ne
          (norm_ne_zero_iff.2 hx0)).differentiableAt one_ne_zero
      have e : hS (n := n) δ r₁ = fun y => psiS δ r₁ y * ‖y‖ ^ mR n := rfl
      rw [e, gradient_mul' hψd hpd, gradient_norm_rpow hx0]
      -- `‖x‖ ‖∇ρ^m‖ = m ρ^m`
      have hpow : (‖x‖ ^ 2) ^ (mR n / 2 - 1) * ‖x‖ ^ 2 = ‖x‖ ^ mR n := by
        have h2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
        rw [Real.rpow_sub_one h2.ne', div_mul_cancel₀ _ h2.ne', ← Real.rpow_natCast,
          ← Real.rpow_mul hρ.le]
        congr 1
        push_cast
        ring
      have hψ0 := psiS_nonneg δ r₁ x
      have hψ1 := psiS_le_one δ r₁ x
      have hgψ := hCψ δ r₁ hδ hr₁ x
      have hρm : 0 ≤ ‖x‖ ^ mR n := Real.rpow_nonneg hρ.le _
      have hq : 0 ≤ (‖x‖ ^ 2) ^ (mR n / 2 - 1) := Real.rpow_nonneg (by positivity) _
      calc ‖x‖ * ‖psiS δ r₁ x • ((mR n * (‖x‖ ^ 2) ^ (mR n / 2 - 1)) • x)
            + ‖x‖ ^ mR n • gradient (psiS δ r₁) x‖
          ≤ ‖x‖ * (psiS δ r₁ x * (mR n * (‖x‖ ^ 2) ^ (mR n / 2 - 1)) * ‖x‖
            + ‖x‖ ^ mR n * ‖gradient (psiS δ r₁) x‖) := by
            apply mul_le_mul_of_nonneg_left _ hρ.le
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg hψ0, abs_of_nonneg (by positivity), abs_of_nonneg hρm]
            ring
        _ = psiS δ r₁ x * mR n * ((‖x‖ ^ 2) ^ (mR n / 2 - 1) * ‖x‖ ^ 2)
            + ‖x‖ ^ mR n * (‖x‖ * ‖gradient (psiS δ r₁) x‖) := by ring
        _ ≤ 1 * mR n * ‖x‖ ^ mR n + ‖x‖ ^ mR n * Cψ := by
            rw [hpow]
            gcongr
        _ = (mR n + Cψ) * ‖x‖ ^ mR n := by ring

/-- The hypotheses of `carleman` for `f = ψ_δ ρ^m v` and `Df = h Dv + v ∇h`. -/
theorem fS_carleman_hyps (S : HalfBallSolution n) (hn : 0 < n) {δ r₁ : ℝ} (hδ : 0 < δ)
    (hδr : 4 * δ ≤ r₁) (hr₁R : r₁ < S.R) :
    (∀ x, fS S δ r₁ x ≠ 0 → δ / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ r₁) ∧
    (∀ x, DfS S δ r₁ x ≠ 0 → δ / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ r₁) ∧
    (∀ x, 0 < vcoord x → ContDiffAt ℝ 2 (fS S δ r₁) x) ∧
    (∀ x, 0 < vcoord x → gradient (fS S δ r₁) x = DfS S δ r₁ x) ∧
    ContinuousOn (fS S δ r₁) {x | 0 ≤ vcoord x} ∧
    ContinuousOn (DfS S δ r₁) {x | 0 ≤ vcoord x} := by
  have hr₁ : 0 < r₁ := by linarith
  have hhc : ContDiff ℝ ∞ (hS (n := n) δ r₁) := hS_contDiff hδ hn
  have hfS : fS S δ r₁ = fun x => hS δ r₁ x * S.v x := rfl
  have hfz : ∀ x : Space n, r₁ ≤ ‖x‖ → fS S δ r₁ x = 0 := fun x hx => by
    rw [hfS]; simp [hS_eq_zero hδ hr₁ (Or.inr hx)]
  have hev_out : ∀ x : Space n, r₁ < ‖x‖ → fS S δ r₁ =ᶠ[𝓝 x] fun _ => 0 := fun x hx =>
    eventuallyEq_zero_of_norm_ge hfz hx
  have hDfz : ∀ x : Space n, (‖x‖ < δ / 2 ∨ r₁ < ‖x‖) → DfS S δ r₁ x = 0 := by
    intro x hx
    have h1 : hS δ r₁ x = 0 := by
      rcases hx with hx | hx
      · exact hS_eq_zero hδ hr₁ (Or.inl hx.le)
      · exact hS_eq_zero hδ hr₁ (Or.inr hx.le)
    simp only [DfS, h1, gradient_hS_eq_zero hδ hr₁ hx, zero_smul, smul_zero, add_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_contra h
    apply hx
    rcases not_and_or.1 h with h | h
    · push Not at h
      rw [hfS]; simp [hS_eq_zero hδ hr₁ (Or.inl h.le)]
    · push Not at h
      exact hfz x h.le
  · intro x hx
    by_contra h
    apply hx
    rcases not_and_or.1 h with h | h
    · push Not at h
      exact hDfz x (Or.inl h)
    · push Not at h
      exact hDfz x (Or.inr h)
  · intro x hx
    by_cases hxR : ‖x‖ < S.R
    · have hUn := (isOpen_halfBall S.R).mem_nhds (show x ∈ halfBall n S.R from ⟨hxR, hx⟩)
      rw [hfS]
      exact (hhc.contDiffAt.of_le (by simp)).mul (S.v_contDiffOn.contDiffAt hUn)
    · push Not at hxR
      exact contDiffAt_const.congr_of_eventuallyEq (hev_out x (by linarith))
  · intro x hx
    by_cases hxR : ‖x‖ < S.R
    · have hxU : x ∈ halfBall n S.R := ⟨hxR, hx⟩
      have hUn := (isOpen_halfBall S.R).mem_nhds hxU
      have hvd : DifferentiableAt ℝ S.v x :=
        (S.v_contDiffOn.contDiffAt hUn).differentiableAt (by simp)
      have hhd : DifferentiableAt ℝ (hS δ r₁) x := (hhc.differentiable (by simp)) x
      rw [hfS, gradient_mul' hhd hvd, S.gradient_eq x hxU]
      rfl
    · push Not at hxR
      rw [(gradient_and_hessian_zero_of_locally_const (hev_out x (by linarith))).1,
        hDfz x (Or.inr (by linarith))]
  · refine continuousOn_halfSpace_of_closedHalfBall hr₁R ?_ hfz
    rw [hfS]
    exact hhc.continuous.continuousOn.mul S.v_continuousOn
  · have hρ₀ : (r₁ + S.R) / 2 < S.R := by linarith
    refine continuousOn_halfSpace_of_closedHalfBall hρ₀ ?_ (fun x hx => hDfz x (Or.inr (by linarith)))
    exact (hhc.continuous.continuousOn.smul S.Dv_continuousOn).add
      (S.v_continuousOn.smul (continuous_gradient_of_contDiff hhc).continuousOn)

/-- A function vanishing near `0` and continuous elsewhere on the closed half-ball. -/
theorem continuousOn_closedHalfBall_of_vanish {f : Space n → ℝ} {R a : ℝ} (ha : 0 < a)
    (hz : ∀ x : Space n, ‖x‖ < a → f x = 0)
    (hc : ∀ x ∈ closedHalfBall n R, x ≠ 0 → ContinuousWithinAt f (closedHalfBall n R) x) :
    ContinuousOn f (closedHalfBall n R) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    have hev : f =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space n) ha] with y hy
      exact hz y (by simpa [dist_zero_right] using hy)
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  · exact hc x hx hx0

theorem continuousAt_muR {x : Space n} (hx : x ≠ 0) : ContinuousAt (muR n) x := by
  unfold muR
  exact ((continuous_norm.pow (n + 1)).continuousAt).inv₀
    (pow_ne_zero _ (norm_ne_zero_iff.2 hx))

theorem continuousAt_phiR (ε : ℝ) {x : Space n} (hx : x ≠ 0) : ContinuousAt (phiR ε) x := by
  unfold phiR
  exact ((Real.continuousAt_log (norm_ne_zero_iff.2 hx)).comp
    continuous_norm.continuousAt).neg.add (continuous_const.mul continuous_norm).continuousAt

theorem muR_nonneg (x : Space n) : 0 ≤ muR n x := by unfold muR; positivity

/-- `ρ μ (ρ^m)² = ρ⁻¹`. -/
theorem rho_mu_rpow_sq (hn : 0 < n) {x : Space n} (hx : x ≠ 0) :
    ‖x‖ * muR n x * (‖x‖ ^ mR n) ^ 2 = ‖x‖⁻¹ := by
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 : (‖x‖ ^ mR n) ^ 2 = ‖x‖ ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    unfold mR
    congr 1
    push_cast
    ring
  have h2 : ‖x‖ ^ ((n : ℝ) - 1) = ‖x‖ ^ n / ‖x‖ := by
    rw [Real.rpow_sub_one hρ.ne', Real.rpow_natCast]
  rw [h1, h2]
  unfold muR
  field_simp
  ring

/-- The bound for `P₀ f` from `transfer`, for every point of the open half-space. -/
theorem P0_fS_bound (S : HalfBallSolution n) (hn : 0 < n) {K₁ CT : ℝ}
    (htr : ∀ (ψ : Space n → ℝ) (x : Space n), x ∈ halfBall n S.R →
      ‖x‖ ≤ 1 → ContDiffAt ℝ 2 ψ x →
      |P0R S.A (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x|
        ≤ K₁ * ‖x‖ * (‖x‖ * ‖gradient (fun y => ψ y * ‖y‖ ^ mR n * S.v y) x‖
            + |ψ x * ‖x‖ ^ mR n * S.v x|)
          + CT * (‖x‖ * ‖gradient ψ x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient ψ) x‖) *
            (‖x‖ ^ mR n * (|S.v x| + ‖x‖ * ‖S.Dv x‖)))
    (hCT : 0 ≤ CT) {δ r₁ : ℝ} (hδ : 0 < δ) (hδr : 4 * δ ≤ r₁) (hr₁R : r₁ < S.R) (hr₁1 : r₁ ≤ 1) :
    ∀ x, 0 < vcoord x → |P0R S.A (fS S δ r₁) x|
      ≤ |FS S CT δ r₁ x| + K₁ * ‖x‖ * (‖x‖ * ‖DfS S δ r₁ x‖ + |fS S δ r₁ x|) := by
  intro x hx
  have hr₁ : 0 < r₁ := by linarith
  obtain ⟨-, -, -, hgrad, -, -⟩ := fS_carleman_hyps S hn hδ hδr hr₁R
  by_cases hin : ‖x‖ < S.R ∧ ‖x‖ ≤ 1
  · have hxU : x ∈ halfBall n S.R := ⟨hin.1, hx⟩
    have hψ : ContDiffAt ℝ 2 (psiS δ r₁) x := ((psiS_contDiff δ r₁).of_le (by simp)).contDiffAt
    have h := htr (psiS δ r₁) x hxU hin.2 hψ
    have hg : gradient (fun y => psiS δ r₁ y * ‖y‖ ^ mR n * S.v y) x = DfS S δ r₁ x :=
      hgrad x hx
    rw [hg] at h
    have hFe : CT * (‖x‖ * ‖gradient (psiS δ r₁) x‖ +
        ‖x‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) x‖) *
        (‖x‖ ^ mR n * (|S.v x| + ‖x‖ * ‖S.Dv x‖)) = FS S CT δ r₁ x := rfl
    rw [hFe] at h
    have hF := le_abs_self (FS S CT δ r₁ x)
    have hfe : |fS S δ r₁ x| = |psiS δ r₁ x * ‖x‖ ^ mR n * S.v x| := rfl
    have hPe : P0R S.A (fS S δ r₁) x
        = P0R S.A (fun y => psiS δ r₁ y * ‖y‖ ^ mR n * S.v y) x := rfl
    rw [hPe, hfe]
    linarith
  · have hxr : r₁ < ‖x‖ := by
      rcases not_and_or.1 hin with h | h <;> push Not at h <;> linarith
    have hfz : ∀ y : Space n, r₁ ≤ ‖y‖ → fS S δ r₁ y = 0 := fun y hy => by
      simp [fS, psiS_eq_zero_of_ge hr₁ hy]
    have hev : fS S δ r₁ =ᶠ[𝓝 x] fun _ => 0 := eventuallyEq_zero_of_norm_ge hfz hxr
    have hgev := gradient_eventuallyEq_zero hev
    have hP : P0R S.A (fS S δ r₁) x = 0 := by
      unfold P0R divMu
      have hfield : (fun y => muR n y • BR S.A y (gradient (fS S δ r₁) y)) =ᶠ[𝓝 x]
          fun _ => (0 : Space n) := by
        filter_upwards [hgev] with y hy
        simp [hy]
      rw [F2.divergence_congr hfield, hev.eq_of_nhds]
      simp [divergence]
    have hf0 : fS S δ r₁ x = 0 := hev.eq_of_nhds
    have hDf0 : DfS S δ r₁ x = 0 := by
      simp only [DfS, hS_eq_zero hδ hr₁ (Or.inr hxr.le), gradient_hS_eq_zero hδ hr₁ (Or.inr hxr),
        zero_smul, smul_zero, add_zero]
    rw [hP, hf0, hDf0]
    simp

/-- Lower bound of the left side of `carleman` for `f = ψ_δ ρ^m v`. -/
theorem fS_lhs_lower (S : HalfBallSolution n) (hn : 0 < n) {ε τ δ r₁ r₂ : ℝ} (hε : 0 < ε)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδr₂ : δ < r₂) (hr₂ : r₂ ≤ r₁ / 4) (hεr₁ : ε * r₁ ≤ 1 / 4)
    (hr₁R : r₁ < S.R) :
    Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) *
        (r₂⁻¹ * ∫ x in halfBall n r₂ \ halfBall n δ, S.v x ^ 2)
      ≤ ∫ x in {x : Space n | 0 < vcoord x},
          ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * fS S δ r₁ x ^ 2 := by
  have hr₁ : 0 < r₁ := by linarith
  have hδr : 4 * δ ≤ r₁ := by linarith
  obtain ⟨-, -, -, -, hfc, -⟩ := fS_carleman_hyps S hn hδ hδr hr₁R
  set W : Space n → ℝ := fun x => ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) *
    fS S δ r₁ x ^ 2 with hW
  have hfz_in : ∀ x : Space n, ‖x‖ < δ / 2 → fS S δ r₁ x = 0 := fun x hx => by
    simp [fS, psiS_eq_zero_of_le hδ hx.le]
  have hfz_out : ∀ x : Space n, r₁ ≤ ‖x‖ → fS S δ r₁ x = 0 := fun x hx => by
    simp [fS, psiS_eq_zero_of_ge hr₁ hx]
  have hWc : ContinuousOn W (closedHalfBall n S.R) := by
    refine continuousOn_closedHalfBall_of_vanish (a := δ / 2) (by positivity)
      (fun x hx => by simp [hW, hfz_in x hx]) fun x hx hx0 => ?_
    have h1 : ContinuousWithinAt (fS S δ r₁) (closedHalfBall n S.R) x :=
      (hfc.mono (fun y (hy : y ∈ closedHalfBall n S.R) => hy.2)) x hx
    exact (((continuous_norm.continuousAt.mul (continuousAt_muR hx0)).mul
      ((continuousAt_const.mul (continuousAt_phiR ε hx0)).rexp)).continuousWithinAt).mul
      (h1.pow 2)
  have hWi : IntegrableOn W {x | 0 < vcoord x} :=
    integrableOn_halfSpace_of_closedHalfBall hr₁R hWc (fun x hx => by simp [hW, hfz_out x hx])
  have hsub : halfBall n r₂ \ halfBall n δ ⊆ {x : Space n | 0 < vcoord x} := fun x hx => hx.1.2
  have hmeas : MeasurableSet (halfBall n r₂ \ halfBall n δ) :=
    (isOpen_halfBall r₂).measurableSet.diff (isOpen_halfBall δ).measurableSet
  have hr₂0 : 0 < r₂ := by linarith
  have hεr₂ : ε * r₂ ≤ 1 := by
    have : ε * r₂ ≤ ε * r₁ := mul_le_mul_of_nonneg_left (by linarith) hε.le
    linarith
  have hvi : IntegrableOn (fun x => S.v x ^ 2) (halfBall n r₂ \ halfBall n δ) :=
    (integrableOn_halfBall_of_continuousOn (by linarith) (S.v_continuousOn.pow 2)).mono_set
      Set.sdiff_subset
  have hpt : ∀ x ∈ halfBall n r₂ \ halfBall n δ,
      Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) * r₂⁻¹ * S.v x ^ 2 ≤ W x := by
    intro x hx
    have hxr₂ : ‖x‖ < r₂ := hx.1.1
    have hxδ : δ ≤ ‖x‖ := by
      by_contra h
      push Not at h
      exact hx.2 ⟨h, hx.1.2⟩
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hxδ; linarith
    have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hψ : psiS δ r₁ x = 1 := psiS_eq_one hδ hr₁ hxδ (by linarith)
    have hWx : W x = Real.exp (2 * τ * phiR ε x) * ‖x‖⁻¹ * S.v x ^ 2 := by
      have hfx : fS S δ r₁ x = ‖x‖ ^ mR n * S.v x := by simp [fS, hψ]
      have key := rho_mu_rpow_sq hn hx0
      simp only [hW, hfx]
      calc ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * (‖x‖ ^ mR n * S.v x) ^ 2
          = Real.exp (2 * τ * phiR ε x) * (‖x‖ * muR n x * (‖x‖ ^ mR n) ^ 2) * S.v x ^ 2 := by
            ring
        _ = Real.exp (2 * τ * phiR ε x) * ‖x‖⁻¹ * S.v x ^ 2 := by rw [key]
    rw [hWx]
    have he : Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) ≤ Real.exp (2 * τ * phiR ε x) := by
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact phi_antitone hε.le hρ hxr₂.le hεr₂
    have hinv : r₂⁻¹ ≤ ‖x‖⁻¹ := inv_anti₀ hρ hxr₂.le
    have hv := sq_nonneg (S.v x)
    have h1 : 0 ≤ Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) := (Real.exp_pos _).le
    have h2 : 0 ≤ r₂⁻¹ := by positivity
    gcongr
  calc Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) *
        (r₂⁻¹ * ∫ x in halfBall n r₂ \ halfBall n δ, S.v x ^ 2)
      = ∫ x in halfBall n r₂ \ halfBall n δ,
          Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) * r₂⁻¹ * S.v x ^ 2 := by
        rw [integral_const_mul]; ring
    _ ≤ ∫ x in halfBall n r₂ \ halfBall n δ, W x :=
        setIntegral_mono_on (hvi.const_mul _) (hWi.mono_set hsub) hmeas hpt
    _ ≤ ∫ x in {x : Space n | 0 < vcoord x}, W x := by
        refine setIntegral_mono_set hWi ?_ (Eventually.of_forall hsub)
        refine (ae_restrict_iff' (F1.measurableSet_halfSpace 0)).2
          (Eventually.of_forall fun x _ => ?_)
        have := muR_nonneg x
        simp only [hW]
        positivity

/-- Closed and open half-balls differ by a null set. -/
theorem setIntegral_closedHalfBall_eq (f : Space n → ℝ) (r : ℝ) :
    ∫ x in {x : Space n | ‖x‖ ≤ r ∧ 0 < vcoord x}, f x = ∫ x in halfBall n r, f x := by
  apply setIntegral_congr_set
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (t := Metric.sphere (0 : Space n) r) ?_
      (Measure.addHaar_sphere volume 0 r)
    intro x hx
    have h1 : ‖x‖ ≤ r := hx.1.1
    have h2 : ¬ (‖x‖ < r ∧ 0 < vcoord x) := hx.2
    have h3 : ‖x‖ = r := le_antisymm h1 (by
      by_contra h
      push Not at h
      exact h2 ⟨h, hx.1.2⟩)
    simpa [Metric.mem_sphere, dist_zero_right] using h3
  · have : halfBall n r \ {x : Space n | ‖x‖ ≤ r ∧ 0 < vcoord x} = ∅ :=
      Set.diff_eq_empty.2 fun x hx => ⟨hx.1.le, hx.2⟩
    rw [this, measure_empty]

/-- Upper bound of the commutator integral: the outer part gives `Kout e^{2τφ(r₁/2)}`, the
inner part `Kin e^{2τφ(δ/2)} δ⁻² ∫_{B⁺_δ} (v² + |∇v|²)`. Also the integrability needed by
`carleman`. -/
theorem FS_upper (S : HalfBallSolution n) (hn : 0 < n) {CT : ℝ} (hCT : 0 ≤ CT) {ε r₁ : ℝ}
    (hε : 0 < ε) (hr₁ : 0 < r₁) (hεr₁ : ε * r₁ ≤ 1 / 4) (hr₁R : r₁ < S.R) (hr₁1 : r₁ ≤ 1) :
    ∃ Kout Kin : ℝ, 0 ≤ Kout ∧ 0 ≤ Kin ∧ ∀ τ δ : ℝ, 0 ≤ τ → 0 < δ → 4 * δ ≤ r₁ →
      IntegrableOn (fun x => muR n x * Real.exp (2 * τ * phiR ε x) * FS S CT δ r₁ x ^ 2)
        {x | 0 < vcoord x} ∧
      ∫ x in {x : Space n | 0 < vcoord x},
          muR n x * Real.exp (2 * τ * phiR ε x) * FS S CT δ r₁ x ^ 2
        ≤ Kout * Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2)))
          + Kin * Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ *
            ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := psiS_deriv_bound (n := n)
  set U : Space n → ℝ := fun x => S.v x ^ 2 + ‖S.Dv x‖ ^ 2 with hU
  have hUc : ContinuousOn U (closedHalfBall n S.R) :=
    (S.v_continuousOn.pow 2).add (S.Dv_continuousOn.norm.pow 2)
  have hU0 : ∀ x, 0 ≤ U x := fun x => by positivity
  set E₁ : ℝ := ∫ x in halfBall n r₁, U x with hE₁
  have hE₁0 : 0 ≤ E₁ := setIntegral_nonneg (isOpen_halfBall _).measurableSet (fun x _ => hU0 x)
  set K0 : ℝ := 8 * CT ^ 2 * Cψ ^ 2 with hK0
  refine ⟨K0 * (r₁ ^ 2)⁻¹ * E₁, K0, by positivity, by positivity, fun τ δ hτ hδ hδr => ?_⟩
  have hr₁δ : δ < r₁ := by linarith
  set W : Space n → ℝ := fun x => muR n x * Real.exp (2 * τ * phiR ε x) * FS S CT δ r₁ x ^ 2
    with hW
  set ein : ℝ := Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) with hein
  set eout : ℝ := Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2))) with heout
  set Bin : Set (Space n) := {x | ‖x‖ ≤ δ ∧ 0 < vcoord x} with hBin
  set Bout : Set (Space n) := {x | ‖x‖ ≤ r₁ ∧ 0 < vcoord x} with hBout
  have hBinm : MeasurableSet Bin :=
    (isClosed_le continuous_norm continuous_const).measurableSet.inter
      (F1.measurableSet_halfSpace 0)
  have hBoutm : MeasurableSet Bout :=
    (isClosed_le continuous_norm continuous_const).measurableSet.inter
      (F1.measurableSet_halfSpace 0)
  -- vanishing of `FS`
  have hFz : ∀ x : Space n,
      (‖x‖ < δ / 2 ∨ (δ < ‖x‖ ∧ ‖x‖ < r₁ / 2) ∨ r₁ < ‖x‖) → FS S CT δ r₁ x = 0 := by
    intro x hz
    obtain ⟨h1, h2⟩ := psiS_deriv_eq_zero hδ hδr hz
    simp [FS, h1, h2]
  -- the common pointwise bound
  have hcommon : ∀ x : Space n, x ≠ 0 → ‖x‖ ≤ 1 →
      W x ≤ 2 * CT ^ 2 * Cψ ^ 2 * (‖x‖ ^ 2)⁻¹ * Real.exp (2 * τ * phiR ε x) * U x := by
    intro x hx0 hx1
    have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hD := hCψ δ r₁ hδ hδr x
    have hD0 : 0 ≤ ‖x‖ * ‖gradient (psiS δ r₁) x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) x‖ :=
      by positivity
    have hmu : muR n x * (‖x‖ ^ mR n) ^ 2 = (‖x‖ ^ 2)⁻¹ := by
      have key := rho_mu_rpow_sq hn hx0
      have e : ‖x‖ * (muR n x * (‖x‖ ^ mR n) ^ 2) = ‖x‖ * (‖x‖ ^ 2)⁻¹ := by
        rw [← mul_assoc, key]; field_simp
      exact mul_left_cancel₀ hρ.ne' e
    have hsq : (|S.v x| + ‖x‖ * ‖S.Dv x‖) ^ 2 ≤ 2 * U x := by
      have h1 : ‖x‖ * ‖S.Dv x‖ ≤ ‖S.Dv x‖ := by
        have := norm_nonneg (S.Dv x)
        nlinarith
      have h2 : 0 ≤ ‖x‖ * ‖S.Dv x‖ := by positivity
      have h3 : |S.v x| ^ 2 = S.v x ^ 2 := sq_abs _
      simp only [hU]
      nlinarith [sq_nonneg (|S.v x| - ‖x‖ * ‖S.Dv x‖), abs_nonneg (S.v x)]
    have hFS : FS S CT δ r₁ x ^ 2 ≤ CT ^ 2 * Cψ ^ 2 * (‖x‖ ^ mR n) ^ 2 * (2 * U x) := by
      have e : FS S CT δ r₁ x ^ 2 = CT ^ 2 *
          (‖x‖ * ‖gradient (psiS δ r₁) x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) x‖) ^ 2 *
          (‖x‖ ^ mR n) ^ 2 * (|S.v x| + ‖x‖ * ‖S.Dv x‖) ^ 2 := by
        simp only [FS]; ring
      rw [e]
      have hD2 : (‖x‖ * ‖gradient (psiS δ r₁) x‖ +
          ‖x‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) x‖) ^ 2 ≤ Cψ ^ 2 :=
        pow_le_pow_left₀ hD0 hD 2
      gcongr
    have hmu0 := muR_nonneg x
    have hE := Real.exp_pos (2 * τ * phiR ε x)
    calc W x = muR n x * Real.exp (2 * τ * phiR ε x) * FS S CT δ r₁ x ^ 2 := rfl
      _ ≤ muR n x * Real.exp (2 * τ * phiR ε x) *
          (CT ^ 2 * Cψ ^ 2 * (‖x‖ ^ mR n) ^ 2 * (2 * U x)) := by gcongr
      _ = 2 * CT ^ 2 * Cψ ^ 2 * (muR n x * (‖x‖ ^ mR n) ^ 2) * Real.exp (2 * τ * phiR ε x) *
          U x := by ring
      _ = 2 * CT ^ 2 * Cψ ^ 2 * (‖x‖ ^ 2)⁻¹ * Real.exp (2 * τ * phiR ε x) * U x := by rw [hmu]
  have hpt : ∀ x ∈ {x : Space n | 0 < vcoord x},
      W x ≤ K0 * ein * (δ ^ 2)⁻¹ * Bin.indicator U x + K0 * (r₁ ^ 2)⁻¹ * eout * Bout.indicator U x := by
    intro x hxt
    have hI1 : 0 ≤ Bin.indicator U x := Set.indicator_nonneg (fun y _ => hU0 y) x
    have hI2 : 0 ≤ Bout.indicator U x := Set.indicator_nonneg (fun y _ => hU0 y) x
    have hR0 : 0 ≤ K0 * ein * (δ ^ 2)⁻¹ * Bin.indicator U x
        + K0 * (r₁ ^ 2)⁻¹ * eout * Bout.indicator U x := by positivity
    by_cases hz : ‖x‖ < δ / 2 ∨ (δ < ‖x‖ ∧ ‖x‖ < r₁ / 2) ∨ r₁ < ‖x‖
    · have : W x = 0 := by simp [hW, hFz x hz]
      rw [this]; exact hR0
    · push Not at hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      have hρ : 0 < ‖x‖ := by linarith
      have hx0 : x ≠ 0 := norm_pos_iff.1 hρ
      have hx1 : ‖x‖ ≤ 1 := by linarith
      have hc := hcommon x hx0 hx1
      have hεx : ε * ‖x‖ ≤ 1 := by
        have : ε * ‖x‖ ≤ ε * r₁ := mul_le_mul_of_nonneg_left hz3 hε.le
        linarith
      by_cases hin : ‖x‖ ≤ δ
      · rw [Set.indicator_of_mem (show x ∈ Bin from ⟨hin, hxt⟩)]
        have he : Real.exp (2 * τ * phiR ε x) ≤ ein := by
          apply Real.exp_le_exp.2
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact phi_antitone hε.le (by positivity) hz1 hεx
        have hinv : (‖x‖ ^ 2)⁻¹ ≤ 4 * (δ ^ 2)⁻¹ := by
          rw [inv_le_comm₀ (by positivity) (by positivity)]
          have : (4 * (δ ^ 2)⁻¹)⁻¹ = δ ^ 2 / 4 := by field_simp
          rw [this]
          nlinarith
        have hU := hU0 x
        calc W x ≤ 2 * CT ^ 2 * Cψ ^ 2 * (‖x‖ ^ 2)⁻¹ * Real.exp (2 * τ * phiR ε x) * U x := hc
          _ ≤ 2 * CT ^ 2 * Cψ ^ 2 * (4 * (δ ^ 2)⁻¹) * ein * U x := by gcongr
          _ = K0 * ein * (δ ^ 2)⁻¹ * U x := by rw [hK0]; ring
          _ ≤ _ := by
            have := mul_nonneg (by positivity : 0 ≤ K0 * (r₁ ^ 2)⁻¹ * eout) hI2
            linarith
      · push Not at hin
        have hout : r₁ / 2 ≤ ‖x‖ := hz2 hin
        rw [Set.indicator_of_mem (show x ∈ Bout from ⟨hz3, hxt⟩)]
        have he : Real.exp (2 * τ * phiR ε x) ≤ eout := by
          apply Real.exp_le_exp.2
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact phi_antitone hε.le (by positivity) hout hεx
        have hinv : (‖x‖ ^ 2)⁻¹ ≤ 4 * (r₁ ^ 2)⁻¹ := by
          rw [inv_le_comm₀ (by positivity) (by positivity)]
          have : (4 * (r₁ ^ 2)⁻¹)⁻¹ = r₁ ^ 2 / 4 := by field_simp
          rw [this]
          nlinarith
        have hU := hU0 x
        calc W x ≤ 2 * CT ^ 2 * Cψ ^ 2 * (‖x‖ ^ 2)⁻¹ * Real.exp (2 * τ * phiR ε x) * U x := hc
          _ ≤ 2 * CT ^ 2 * Cψ ^ 2 * (4 * (r₁ ^ 2)⁻¹) * eout * U x := by gcongr
          _ = K0 * (r₁ ^ 2)⁻¹ * eout * U x := by rw [hK0]; ring
          _ ≤ _ := by
            have := mul_nonneg (by positivity : 0 ≤ K0 * ein * (δ ^ 2)⁻¹) hI1
            linarith
  -- integrability of `W`
  have hgψ : ContDiff ℝ ∞ (gradient (psiS (n := n) δ r₁)) := by
    rw [F2.gradient_eq_comp]
    exact (F2.toDualSymmCLE (n := n)).contDiff.comp ((psiS_contDiff δ r₁).fderiv_right (by simp))
  have hgψc : Continuous (gradient (psiS (n := n) δ r₁)) := hgψ.continuous
  have hHc : Continuous (fderiv ℝ (gradient (psiS (n := n) δ r₁))) :=
    hgψ.continuous_fderiv (by simp)
  have hWc : ContinuousOn W (closedHalfBall n S.R) := by
    refine continuousOn_closedHalfBall_of_vanish (a := δ / 2) (by positivity)
      (fun x hx => by simp [hW, hFz x (Or.inl hx)]) fun x hx hx0 => ?_
    have hρm : ContinuousAt (fun y : Space n => ‖y‖ ^ mR n) x :=
      ((contDiffAt_norm ℝ hx0 (n := 1)).rpow_const_of_ne (norm_ne_zero_iff.2 hx0)).continuousAt
    have hvx : ContinuousWithinAt S.v (closedHalfBall n S.R) x := S.v_continuousOn x hx
    have hDvx : ContinuousWithinAt S.Dv (closedHalfBall n S.R) x := S.Dv_continuousOn x hx
    have hFSc : ContinuousWithinAt (FS S CT δ r₁) (closedHalfBall n S.R) x := by
      show ContinuousWithinAt (fun y => CT * (‖y‖ * ‖gradient (psiS δ r₁) y‖ +
        ‖y‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) y‖) *
        (‖y‖ ^ mR n * (|S.v y| + ‖y‖ * ‖S.Dv y‖))) (closedHalfBall n S.R) x
      have habs : ContinuousWithinAt (fun y => |S.v y|) (closedHalfBall n S.R) x :=
        continuous_abs.continuousAt.comp_continuousWithinAt hvx
      exact ((continuousAt_const.mul ((continuous_norm.continuousAt.mul
        hgψc.continuousAt.norm).add ((continuous_norm.continuousAt.pow 2).mul
        hHc.continuousAt.norm))).continuousWithinAt).mul
        (hρm.continuousWithinAt.mul (habs.add
          (continuous_norm.continuousWithinAt.mul hDvx.norm)))
    exact (((continuousAt_muR hx0).mul
      ((continuousAt_const.mul (continuousAt_phiR ε hx0)).rexp)).continuousWithinAt).mul
      (hFSc.pow 2)
  have hρ₀ : (r₁ + S.R) / 2 < S.R := by linarith
  have hWi : IntegrableOn W {x | 0 < vcoord x} :=
    integrableOn_halfSpace_of_closedHalfBall hρ₀ hWc
      (fun x hx => by simp [hW, hFz x (Or.inr (Or.inr (by linarith)))])
  -- integrability of the bound
  have hKc : IsCompact {x : Space n | ‖x‖ ≤ r₁ ∧ 0 ≤ vcoord x} := by
    have e : {x : Space n | ‖x‖ ≤ r₁ ∧ 0 ≤ vcoord x}
        = Metric.closedBall 0 r₁ ∩ {x | 0 ≤ vcoord x} := by
      ext x
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [e]
    exact (isCompact_closedBall 0 r₁).inter_right
      (isClosed_le continuous_const F1.continuous_vcoord)
  have hUK : IntegrableOn U {x : Space n | ‖x‖ ≤ r₁ ∧ 0 ≤ vcoord x} :=
    (hUc.mono (halfBall_subset_closedHalfBall hr₁R)).integrableOn_compact hKc
  have hUout : IntegrableOn U Bout := hUK.mono_set fun x hx => ⟨hx.1, hx.2.le⟩
  have hUin : IntegrableOn U Bin := hUout.mono_set fun x hx => ⟨hx.1.trans hr₁δ.le, hx.2⟩
  have hi1 : Integrable (fun x => K0 * ein * (δ ^ 2)⁻¹ * Bin.indicator U x) :=
    (hUin.integrable_indicator hBinm).const_mul _
  have hi2 : Integrable (fun x => K0 * (r₁ ^ 2)⁻¹ * eout * Bout.indicator U x) :=
    (hUout.integrable_indicator hBoutm).const_mul _
  have hRi : IntegrableOn (fun x => K0 * ein * (δ ^ 2)⁻¹ * Bin.indicator U x
      + K0 * (r₁ ^ 2)⁻¹ * eout * Bout.indicator U x) {x | 0 < vcoord x} :=
    (hi1.add hi2).integrableOn
  refine ⟨hWi, ?_⟩
  have hmono := setIntegral_mono_on hWi hRi (F1.measurableSet_halfSpace 0) hpt
  rw [integral_add hi1.integrableOn hi2.integrableOn, integral_const_mul, integral_const_mul,
    setIntegral_indicator hBinm, setIntegral_indicator hBoutm,
    Set.inter_eq_right.2 (fun x (hx : x ∈ Bin) => hx.2),
    Set.inter_eq_right.2 (fun x (hx : x ∈ Bout) => hx.2),
    setIntegral_closedHalfBall_eq, setIntegral_closedHalfBall_eq] at hmono
  calc ∫ x in {x : Space n | 0 < vcoord x}, W x
      ≤ K0 * ein * (δ ^ 2)⁻¹ * (∫ x in halfBall n δ, U x)
        + K0 * (r₁ ^ 2)⁻¹ * eout * E₁ := hmono
    _ = K0 * (r₁ ^ 2)⁻¹ * E₁ * eout + K0 * ein * (δ ^ 2)⁻¹ * ∫ x in halfBall n δ, U x := by
        ring

/-- Upper bound of the boundary integral: on `{t = 0}`, `⟪A ∇f, e_d⟫ = ψ ρ^m ⟪A Dv, e_d⟫`
(the conormal is vertical and `∇(ψ ρ^m)` is radial), so the integrand is at most
`C e^{2τφ} g(ρ) ≤ C Bd`. -/
theorem fS_bdry_upper (S : HalfBallSolution n) (hn : 0 < n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) {ε r₁ : ℝ} (hε : 0 < ε) (hr₁ : 0 < r₁)
    (hr₁R : r₁ < S.R) (hr₁1 : r₁ ≤ 1) :
    ∃ Cbd : ℝ, 0 ≤ Cbd ∧ ∀ τ δ Bd : ℝ, 0 ≤ τ → 0 < δ → 4 * δ ≤ r₁ →
      (∀ ρ ∈ Set.Ioc 0 r₁, Real.exp (2 * τ * (-Real.log ρ + ε * ρ)) * g ρ ≤ Bd) →
      ∫ y : EuclideanSpace ℝ (Fin n),
          ‖lift y 0‖ ^ 2 * muR n (lift y 0) * Real.exp (2 * τ * phiR ε (lift y 0)) *
            (|⟪S.A (lift y 0) (DfS S δ r₁ (lift y 0)), ed n⟫_ℝ| *
              (‖lift y 0‖ * ‖DfS S δ r₁ (lift y 0)‖ + |fS S δ r₁ (lift y 0)|))
        ≤ Cbd * Bd := by
  obtain ⟨Ch, hCh0, hCh⟩ := gradient_hS (n := n) hn
  have hKc : IsCompact {x : Space n | ‖x‖ ≤ r₁ ∧ 0 ≤ vcoord x} := by
    have e : {x : Space n | ‖x‖ ≤ r₁ ∧ 0 ≤ vcoord x}
        = Metric.closedBall 0 r₁ ∩ {x | 0 ≤ vcoord x} := by
      ext x
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [e]
    exact (isCompact_closedBall 0 r₁).inter_right
      (isClosed_le continuous_const F1.continuous_vcoord)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (((S.v_continuousOn.norm).add (S.Dv_continuousOn.norm)).mono
      (halfBall_subset_closedHalfBall hr₁R))
  set V : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r₁)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨(Ch + 2) * |M| * V, by positivity, fun τ δ Bd hτ hδ hδr hBd => ?_⟩
  have hBd0 : 0 ≤ Bd := by
    have h := hBd r₁ ⟨hr₁, le_rfl⟩
    have : 0 < Real.exp (2 * τ * (-Real.log r₁ + ε * r₁)) * g r₁ :=
      mul_pos (Real.exp_pos _) (hg_pos r₁ hr₁)
    linarith
  set I : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    ‖lift y 0‖ ^ 2 * muR n (lift y 0) * Real.exp (2 * τ * phiR ε (lift y 0)) *
      (|⟪S.A (lift y 0) (DfS S δ r₁ (lift y 0)), ed n⟫_ℝ| *
        (‖lift y 0‖ * ‖DfS S δ r₁ (lift y 0)‖ + |fS S δ r₁ (lift y 0)|)) with hI
  have hI0 : ∀ y, 0 ≤ I y := fun y => by
    have := muR_nonneg (lift y 0)
    simp only [hI]
    positivity
  have hpt : ∀ y, I y ≤ (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r₁).indicator
      (fun _ => (Ch + 2) * |M| * Bd) y := by
    intro y
    set x := lift y 0 with hx
    have hxn : ‖x‖ = ‖y‖ := norm_lift_zero y
    have hxt : vcoord x = 0 := by rw [hx, vcoord_lift]
    -- the conormal derivative of `f` on the flat boundary
    have hcon : ‖x‖ < S.R → ⟪S.A x (DfS S δ r₁ x), ed n⟫_ℝ
        = hS δ r₁ x * ⟪S.A x (S.Dv x), ed n⟫_ℝ := by
      intro hxR
      obtain ⟨c, hc⟩ := (hCh δ r₁ hδ hδr x).1
      obtain ⟨k, hk⟩ := S.conormal x ⟨hxR, hxt⟩
      have hrad : ⟪S.A x (gradient (hS δ r₁) x), ed n⟫_ℝ = 0 := by
        rw [hc, map_smul, real_inner_smul_left, S.coeffs.symm, hk, real_inner_smul_right,
          F1.inner_ed]
        have : x (Fin.last n) = vcoord x := rfl
        rw [this, hxt]
        ring
      simp only [DfS, map_add, map_smul, inner_add_left, real_inner_smul_left, hrad]
      ring
    by_cases hy : ‖y‖ < r₁
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_ball, dist_zero_right] using hy)]
      have hxr : ‖x‖ < r₁ := by rw [hxn]; exact hy
      have hxR : ‖x‖ < S.R := lt_trans hxr hr₁R
      by_cases hx0 : x = 0
      · have h0 : hS δ r₁ x = 0 := hS_eq_zero hδ hr₁ (Or.inl (by rw [hx0, norm_zero]; positivity))
        have : I y = 0 := by
          simp only [hI, ← hx, hcon hxR, h0, zero_mul, abs_zero, mul_zero]
        rw [this]
        positivity
      · have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
        have hxK : x ∈ {x : Space n | ‖x‖ ≤ r₁ ∧ 0 ≤ vcoord x} := ⟨hxr.le, hxt.ge⟩
        have hMx : ‖S.v x‖ + ‖S.Dv x‖ ≤ M := by
          have h := hM x hxK
          simp only [Pi.add_apply] at h
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
          exact h
        have hvM : |S.v x| ≤ |M| := by
          have h1 := norm_nonneg (S.Dv x)
          have h2 : ‖S.v x‖ = |S.v x| := Real.norm_eq_abs _
          linarith [le_abs_self M]
        have hDvM : ‖S.Dv x‖ ≤ |M| := by
          have h1 := norm_nonneg (S.v x)
          linarith [le_abs_self M]
        have hψ0 := psiS_nonneg δ r₁ x
        have hψ1 := psiS_le_one δ r₁ x
        have hρm : 0 ≤ ‖x‖ ^ mR n := Real.rpow_nonneg hρ.le _
        have hhS : hS δ r₁ x = psiS δ r₁ x * ‖x‖ ^ mR n := rfl
        have hh0 : 0 ≤ hS δ r₁ x := by rw [hhS]; positivity
        have hhle : hS δ r₁ x ≤ ‖x‖ ^ mR n := by
          rw [hhS]; nlinarith
        have hneux : |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖ := hneu x ⟨hxR, hxt⟩ hx0
        have hgx : 0 < g ‖x‖ := hg_pos _ hρ
        -- the conormal factor
        have hA1 : |⟪S.A x (DfS S δ r₁ x), ed n⟫_ℝ| ≤ ‖x‖ ^ mR n * g ‖x‖ := by
          rw [hcon hxR, abs_mul, abs_of_nonneg hh0]
          exact mul_le_mul hhle hneux (abs_nonneg _) hρm
        -- the Dirichlet factor
        have hgr := (hCh δ r₁ hδ hδr x).2.1
        have hρ1 : ‖x‖ ≤ 1 := by linarith
        have hA2 : ‖x‖ * ‖DfS S δ r₁ x‖ + |fS S δ r₁ x| ≤ (Ch + 2) * |M| * ‖x‖ ^ mR n := by
          have h1 : ‖DfS S δ r₁ x‖ ≤ hS δ r₁ x * ‖S.Dv x‖ + |S.v x| * ‖gradient (hS δ r₁) x‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh0]
          have h2 : |fS S δ r₁ x| = hS δ r₁ x * |S.v x| := by
            have : fS S δ r₁ x = hS δ r₁ x * S.v x := rfl
            rw [this, abs_mul, abs_of_nonneg hh0]
          rw [h2]
          have h3 : ‖x‖ * ‖DfS S δ r₁ x‖
              ≤ ‖x‖ * (hS δ r₁ x * ‖S.Dv x‖) + |S.v x| * (‖x‖ * ‖gradient (hS δ r₁) x‖) := by
            have := mul_le_mul_of_nonneg_left h1 hρ.le
            nlinarith
          have h4 : |S.v x| * (‖x‖ * ‖gradient (hS δ r₁) x‖) ≤ |M| * (Ch * ‖x‖ ^ mR n) :=
            mul_le_mul hvM hgr (by positivity) (abs_nonneg _)
          have h5 : ‖x‖ * (hS δ r₁ x * ‖S.Dv x‖) ≤ 1 * (‖x‖ ^ mR n * |M|) := by
            apply mul_le_mul hρ1 (mul_le_mul hhle hDvM (norm_nonneg _) hρm) (by positivity)
              zero_le_one
          have h6 : hS δ r₁ x * |S.v x| ≤ ‖x‖ ^ mR n * |M| :=
            mul_le_mul hhle hvM (abs_nonneg _) hρm
          linarith
        -- the weight
        have hw : ‖x‖ ^ 2 * muR n x * (‖x‖ ^ mR n) ^ 2 = 1 := by
          have key := rho_mu_rpow_sq hn hx0
          have : ‖x‖ ^ 2 * muR n x * (‖x‖ ^ mR n) ^ 2
              = ‖x‖ * (‖x‖ * muR n x * (‖x‖ ^ mR n) ^ 2) := by ring
          rw [this, key, mul_inv_cancel₀ hρ.ne']
        have hBdx : Real.exp (2 * τ * phiR ε x) * g ‖x‖ ≤ Bd := hBd ‖x‖ ⟨hρ, hxr.le⟩
        have hmu := muR_nonneg x
        have hE := Real.exp_pos (2 * τ * phiR ε x)
        calc I y = ‖x‖ ^ 2 * muR n x * Real.exp (2 * τ * phiR ε x) *
              (|⟪S.A x (DfS S δ r₁ x), ed n⟫_ℝ| *
                (‖x‖ * ‖DfS S δ r₁ x‖ + |fS S δ r₁ x|)) := rfl
          _ ≤ ‖x‖ ^ 2 * muR n x * Real.exp (2 * τ * phiR ε x) *
              ((‖x‖ ^ mR n * g ‖x‖) * ((Ch + 2) * |M| * ‖x‖ ^ mR n)) := by
              gcongr
          _ = (‖x‖ ^ 2 * muR n x * (‖x‖ ^ mR n) ^ 2) * (Ch + 2) * |M| *
              (Real.exp (2 * τ * phiR ε x) * g ‖x‖) := by ring
          _ ≤ 1 * (Ch + 2) * |M| * Bd := by
              rw [hw]
              gcongr
          _ = (Ch + 2) * |M| * Bd := by ring
    · rw [Set.indicator_of_notMem (by simpa [Metric.mem_ball, dist_zero_right] using hy)]
      push Not at hy
      have hxr : r₁ ≤ ‖x‖ := by rw [hxn]; exact hy
      have h0 : hS δ r₁ x = 0 := hS_eq_zero hδ hr₁ (Or.inr hxr)
      by_cases hxR : ‖x‖ < S.R
      · have : I y = 0 := by
          simp only [hI, ← hx, hcon hxR, h0, zero_mul, abs_zero, mul_zero]
        rw [this]
      · push Not at hxR
        have hg0 : gradient (hS δ r₁) x = 0 :=
          gradient_hS_eq_zero hδ hr₁ (Or.inr (by linarith))
        have hD0 : DfS S δ r₁ x = 0 := by
          simp only [DfS, h0, hg0, zero_smul, smul_zero, add_zero]
        have : I y = 0 := by
          simp only [hI, ← hx, hD0, map_zero, inner_zero_left, abs_zero, zero_mul, mul_zero]
        rw [this]
  have hint_ind : Integrable ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r₁).indicator
      (fun _ => (Ch + 2) * |M| * Bd)) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator
      Metric.isOpen_ball.measurableSet
  calc ∫ y, I y ≤ ∫ y, (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r₁).indicator
        (fun _ => (Ch + 2) * |M| * Bd) y :=
        integral_mono_of_nonneg (Eventually.of_forall hI0) hint_ind (Eventually.of_forall hpt)
    _ = V * ((Ch + 2) * |M| * Bd) := by
        rw [integral_indicator_const _ Metric.isOpen_ball.measurableSet, smul_eq_mul]
        rfl
    _ = (Ch + 2) * |M| * V * Bd := by ring

/-- **Step 1 for a fixed inner cutoff radius `δ`.** Carleman (`carleman`) applied to
`f = ψ_δ ρ^m v`, where `ψ_δ` vanishes for `ρ ≤ δ/2` and for `ρ ≥ r₁` and equals `1` on
`[δ, r₁/2]`, with `P₀ f` bounded by `transfer`. The commutator near `ρ = r₁` gives the term
`C₀ e^{2τφ(r₁/2)}`, the boundary integral gives `C₀ τ² Bd` (every boundary term contains the
conormal datum, bounded by `g`), and the commutator near `ρ = δ` gives the last term. -/
theorem step1_fixed_delta (S : HalfBallSolution n) (hn : 0 < n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg_flat : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) :
    ∃ ε rs τ₀ : ℝ, 0 < ε ∧ 0 < rs ∧ rs < S.R ∧ rs ≤ 1 ∧ ε * rs ≤ 1 / 4 ∧ 0 < τ₀ ∧
      ∀ r₁ ∈ Set.Ioc 0 rs, ∃ C₀ Kin : ℝ, 0 < C₀ ∧ 0 ≤ Kin ∧
        ∀ τ : ℝ, τ₀ ≤ τ → ∀ r₂ ∈ Set.Ioc 0 (r₁ / 4), ∀ δ ∈ Set.Ioo 0 r₂, ∀ Bd : ℝ,
          (∀ ρ ∈ Set.Ioc 0 r₁, Real.exp (2 * τ * (-Real.log ρ + ε * ρ)) * g ρ ≤ Bd) →
          τ ^ 3 * Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) *
              (r₂⁻¹ * ∫ x in halfBall n r₂ \ halfBall n δ, S.v x ^ 2)
            ≤ C₀ * Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2))) + C₀ * τ ^ 2 * Bd
              + Kin * Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ *
                ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) := by
  obtain ⟨K₁, CT, hK₁, hCT, htr⟩ := transfer S hn
  obtain ⟨ε, rs, τ₀, C₅, hε, hrs, hrsR, hrs1, hεrs, hτ₀, hC₅, hcarl⟩ := carleman S hn K₁ hK₁
  refine ⟨ε, rs, τ₀, hε, hrs, hrsR, hrs1, hεrs, by linarith, fun r₁ hr₁ => ?_⟩
  have hr₁0 : 0 < r₁ := hr₁.1
  have hr₁R : r₁ < S.R := lt_of_le_of_lt hr₁.2 hrsR
  have hr₁1 : r₁ ≤ 1 := hr₁.2.trans hrs1
  have hεr₁ : ε * r₁ ≤ 1 / 4 := le_trans (mul_le_mul_of_nonneg_left hr₁.2 hε.le) hεrs
  obtain ⟨Kout, Kin, hKout, hKin, hFup⟩ := FS_upper S hn hCT hε hr₁0 hεr₁ hr₁R hr₁1
  obtain ⟨Cbd, hCbd, hbd⟩ := fS_bdry_upper S hn g hneu hg_pos hε hr₁0 hr₁R hr₁1
  refine ⟨C₅ * Kout + C₅ * Cbd + 1, C₅ * Kin, by positivity, by positivity,
    fun τ hτ r₂ hr₂ δ hδ Bd hBd => ?_⟩
  have hτ0 : 0 ≤ τ := by linarith
  have hδ0 : 0 < δ := hδ.1
  have hδr : 4 * δ ≤ r₁ := by linarith [hδ.2, hr₂.2]
  obtain ⟨hsupp, hDsupp, hC2, hgrad, hfc, hDfc⟩ := fS_carleman_hyps S hn hδ0 hδr hr₁R
  obtain ⟨hFi, hFle⟩ := hFup τ δ hτ0 hδ0 hδr
  have hP0 := P0_fS_bound S hn htr hCT hδ0 hδr hr₁R hr₁1
  have hc := hcarl τ hτ (fS S δ r₁) (FS S CT δ r₁) (DfS S δ r₁) (δ / 2) (by positivity)
    (fun x hx => ⟨(hsupp x hx).1, (hsupp x hx).2.trans hr₁.2⟩)
    (fun x hx => ⟨(hDsupp x hx).1, (hDsupp x hx).2.trans hr₁.2⟩)
    hC2 hgrad hfc hDfc hFi hP0
  have hlow := fS_lhs_lower S hn hε hτ0 hδ0 hδ.2 hr₂.2 hεr₁ hr₁R
  have hB := hbd τ δ Bd hτ0 hδ0 hδr hBd
  -- the gradient part of the left side is nonnegative
  have hgrad0 : 0 ≤ τ * ∫ x in {x : Space n | 0 < vcoord x},
      ‖x‖ ^ 3 * muR n x * Real.exp (2 * τ * phiR ε x) * ‖DfS S δ r₁ x‖ ^ 2 := by
    apply mul_nonneg hτ0
    refine setIntegral_nonneg (F1.measurableSet_halfSpace 0) fun x _ => ?_
    have : 0 ≤ muR n x := by unfold muR; positivity
    positivity
  have hBd0 : 0 ≤ Bd := by
    have h := hBd r₁ ⟨hr₁0, le_rfl⟩
    have : 0 < Real.exp (2 * τ * (-Real.log r₁ + ε * r₁)) * g r₁ :=
      mul_pos (Real.exp_pos _) (hg_pos r₁ hr₁0)
    linarith
  have hE1 : 0 ≤ Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2))) := (Real.exp_pos _).le
  have hτ3 : 0 ≤ τ ^ 3 := by positivity
  calc τ ^ 3 * Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) *
        (r₂⁻¹ * ∫ x in halfBall n r₂ \ halfBall n δ, S.v x ^ 2)
      = τ ^ 3 * (Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) *
        (r₂⁻¹ * ∫ x in halfBall n r₂ \ halfBall n δ, S.v x ^ 2)) := by ring
    _ ≤ τ ^ 3 * ∫ x in {x : Space n | 0 < vcoord x},
          ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * fS S δ r₁ x ^ 2 :=
        mul_le_mul_of_nonneg_left hlow hτ3
    _ ≤ C₅ * (∫ x in {x : Space n | 0 < vcoord x},
            muR n x * Real.exp (2 * τ * phiR ε x) * FS S CT δ r₁ x ^ 2)
          + C₅ * τ ^ 2 * (∫ y : EuclideanSpace ℝ (Fin n),
            ‖lift y 0‖ ^ 2 * muR n (lift y 0) * Real.exp (2 * τ * phiR ε (lift y 0)) *
              (|⟪S.A (lift y 0) (DfS S δ r₁ (lift y 0)), ed n⟫_ℝ| *
                (‖lift y 0‖ * ‖DfS S δ r₁ (lift y 0)‖ + |fS S δ r₁ (lift y 0)|))) := by
        linarith
    _ ≤ C₅ * (Kout * Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2)))
          + Kin * Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ *
            ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2)) + C₅ * τ ^ 2 * (Cbd * Bd) := by
        gcongr
    _ ≤ (C₅ * Kout + C₅ * Cbd + 1) * Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2)))
          + (C₅ * Kout + C₅ * Cbd + 1) * τ ^ 2 * Bd
          + C₅ * Kin * Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ *
            ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) := by
        have h1 : C₅ * Kout * Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2)))
            ≤ (C₅ * Kout + C₅ * Cbd + 1) *
              Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2))) := by
          apply mul_le_mul_of_nonneg_right _ hE1
          have : 0 ≤ C₅ * Cbd := by positivity
          linarith
        have h2 : C₅ * τ ^ 2 * (Cbd * Bd) ≤ (C₅ * Kout + C₅ * Cbd + 1) * τ ^ 2 * Bd := by
          have : 0 ≤ C₅ * Kout := by positivity
          have h3 : C₅ * τ ^ 2 * (Cbd * Bd) = (C₅ * Cbd) * τ ^ 2 * Bd := by ring
          rw [h3]
          apply mul_le_mul_of_nonneg_right _ hBd0
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
        nlinarith

/-- The inner commutator term vanishes as `δ → 0`, at a rate `δ`. -/
theorem inner_err_le {τ ε δ : ℝ} {M : ℕ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hεδ : ε * δ ≤ 1) (hM : 2 * τ + 3 ≤ M) :
    Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ * δ ^ M
      ≤ Real.exp (2 * τ * Real.log 2 + τ) * δ := by
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have h2 : (δ ^ 2)⁻¹ * δ ^ M = Real.exp (((M : ℝ) - 2) * Real.log δ) := by
    have e1 : δ ^ M = Real.exp (M * Real.log δ) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hδ M)]
    have e2 : (δ ^ 2)⁻¹ = Real.exp (-(2 * Real.log δ)) := by
      have : (2 : ℝ) * Real.log δ = ((2 : ℕ) : ℝ) * Real.log δ := by norm_num
      rw [Real.exp_neg, this, ← Real.log_pow, Real.exp_log (pow_pos hδ 2)]
    rw [e1, e2, ← Real.exp_add]
    congr 1
    ring
  have h1 : Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2)))
      = Real.exp (2 * τ * Real.log 2 + τ * (ε * δ) + (-(2 * τ)) * Real.log δ) := by
    rw [Real.log_div hδ.ne' two_ne_zero]
    congr 1
    ring
  have hδe : δ = Real.exp (Real.log δ) := (Real.exp_log hδ).symm
  rw [mul_assoc, h2, h1, ← Real.exp_add]
  conv_rhs => rw [hδe, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h3 : τ * (ε * δ) ≤ τ := by
    have := mul_le_mul_of_nonneg_left hεδ hτ
    linarith
  have h4 : ((M : ℝ) - 2) * Real.log δ + (-(2 * τ)) * Real.log δ ≤ Real.log δ := by
    have : (1 : ℝ) ≤ (M : ℝ) - 2 - 2 * τ := by linarith
    nlinarith
  linarith

/-- **Step 1 of the proof of Proposition R: the inequality (eq:Rmain), in `x` coordinates.**
With the outer cutoff in `[r₁/2, r₁]` and the inner cutoff removed with Lemma R1:
`τ³ e^{2τφ(r₂)} r₂⁻¹ ∫_{B⁺_{r₂}} v² ≤ C₀ e^{2τφ(r₁/2)} + C₀ τ² Bd`
for every bound `Bd` of `e^{2τφ(ρ)} g(ρ)` on `(0, r₁]`. -/
theorem step1 (S : HalfBallSolution n) (hn : 0 < n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg_flat : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) :
    ∃ ε rs τ₀ : ℝ, 0 < ε ∧ 0 < rs ∧ ε * rs ≤ 1 / 4 ∧ 0 < τ₀ ∧
      ∀ r₁ ∈ Set.Ioc 0 rs, ∃ C₀ : ℝ, 0 < C₀ ∧
        ∀ τ : ℝ, τ₀ ≤ τ → ∀ r₂ ∈ Set.Ioc 0 (r₁ / 4), ∀ Bd : ℝ,
          (∀ ρ ∈ Set.Ioc 0 r₁, Real.exp (2 * τ * (-Real.log ρ + ε * ρ)) * g ρ ≤ Bd) →
          τ ^ 3 * Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) *
              (r₂⁻¹ * ∫ x in halfBall n r₂, S.v x ^ 2)
            ≤ C₀ * Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2))) + C₀ * τ ^ 2 * Bd := by
  obtain ⟨ε, rs, τ₀, hε, hrs, hrsR, hrs1, hεrs, hτ₀, hA⟩ :=
    step1_fixed_delta S hn g hneu hg_pos hg_mono hg_flat
  refine ⟨ε, rs, τ₀, hε, hrs, hεrs, hτ₀, fun r₁ hr₁ => ?_⟩
  obtain ⟨C₀, Kin, hC₀, hKin, hA'⟩ := hA r₁ hr₁
  refine ⟨C₀, hC₀, fun τ hτ r₂ hr₂ Bd hBd => ?_⟩
  have hτ0 : 0 < τ := lt_of_lt_of_le hτ₀ hτ
  have hr₂0 : 0 < r₂ := hr₂.1
  have hr₁0 : 0 < r₁ := hr₁.1
  have hr₂R : r₂ < S.R := by linarith [hr₂.2, hr₁.2]
  have hr₂1 : r₂ ≤ 1 := by linarith [hr₂.2, hr₁.2]
  set L : ℝ := τ ^ 3 * Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) with hL
  have hL0 : 0 ≤ L := by positivity
  set RHS : ℝ := C₀ * Real.exp (2 * τ * (-Real.log (r₁ / 2) + ε * (r₁ / 2))) + C₀ * τ ^ 2 * Bd
    with hRHS
  -- infinite order vanishing with `M ≥ 2τ + 3`
  set M : ℕ := ⌈2 * τ⌉₊ + 3 with hM
  have hMτ : 2 * τ + 3 ≤ (M : ℝ) := by
    rw [hM]; push_cast; linarith [Nat.le_ceil (2 * τ)]
  obtain ⟨CM, rm, hrm, hCM⟩ := grad_infinite_order S hn g hneu hg_pos hg_mono hg_flat M
  set E₀ : ℝ := Real.exp (2 * τ * Real.log 2 + τ) with hE₀
  set Cerr : ℝ := Kin * |CM| * E₀ + L * r₂⁻¹ * |CM| with hCerr
  have hCerr0 : 0 ≤ Cerr := by positivity
  set δ₀ : ℝ := min (min (r₂ / 2) rm) (min 1 (1 / (ε + 1))) with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    have : 0 < 1 / (ε + 1) := by positivity
    exact lt_min (lt_min (by linarith) hrm) (lt_min one_pos this)
  have hvi : IntegrableOn (fun x => S.v x ^ 2) (halfBall n r₂) :=
    integrableOn_halfBall_of_continuousOn hr₂R (S.v_continuousOn.pow 2)
  -- the estimate for every small `δ`
  have hbound : ∀ δ, 0 < δ → δ ≤ δ₀ →
      L * (r₂⁻¹ * ∫ x in halfBall n r₂, S.v x ^ 2) ≤ RHS + Cerr * δ := by
    intro δ hδ hδle
    have hδr₂ : δ < r₂ := by
      have : δ ≤ r₂ / 2 := hδle.trans ((min_le_left _ _).trans (min_le_left _ _))
      linarith
    have hδrm : δ ≤ rm := hδle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hδ1 : δ ≤ 1 := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hδε : δ ≤ 1 / (ε + 1) := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hεδ : ε * δ ≤ 1 := by
      rw [le_div_iff₀ (by linarith)] at hδε
      nlinarith
    have key := hA' τ hτ r₂ hr₂ δ ⟨hδ, hδr₂⟩ Bd hBd
    have hsub : halfBall n δ ⊆ halfBall n r₂ := fun x hx => ⟨lt_trans hx.1 hδr₂, hx.2⟩
    rw [setIntegral_sdiff (isOpen_halfBall δ).measurableSet hvi hsub] at key
    have hE := hCM δ ⟨hδ, hδrm⟩
    have hv_le : ∫ x in halfBall n δ, S.v x ^ 2 ≤ ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) :=
      setIntegral_mono_on
        (integrableOn_halfBall_of_continuousOn (by linarith) (S.v_continuousOn.pow 2))
        (integrableOn_halfBall_of_continuousOn (by linarith)
          ((S.v_continuousOn.pow 2).add (S.Dv_continuousOn.norm.pow 2)))
        (isOpen_halfBall δ).measurableSet (fun x _ => by nlinarith [sq_nonneg ‖S.Dv x‖])
    have hEabs : ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ |CM| * δ ^ M :=
      hE.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hδ.le _))
    have herr := inner_err_le (M := M) hτ0.le hε.le hδ hδ1 hεδ hMτ
    have hexp0 : 0 ≤ Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ := by
      positivity
    -- the inner term
    have hin : Kin * Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ *
          ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2)
        ≤ Kin * |CM| * E₀ * δ := by
      calc Kin * Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ *
            ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2)
          = Kin * (Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹) *
            ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) := by ring
        _ ≤ Kin * (Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹) *
            (|CM| * δ ^ M) := by gcongr
        _ = Kin * |CM| * (Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ *
            δ ^ M) := by ring
        _ ≤ Kin * |CM| * (E₀ * δ) := by gcongr
        _ = Kin * |CM| * E₀ * δ := by ring
    -- the missing small ball
    have hball : L * (r₂⁻¹ * ∫ x in halfBall n δ, S.v x ^ 2) ≤ L * r₂⁻¹ * |CM| * δ := by
      have hδM : δ ^ M ≤ δ := by
        have hM1 : 1 ≤ M := by omega
        calc δ ^ M ≤ δ ^ 1 := pow_le_pow_of_le_one hδ.le hδ1 hM1
          _ = δ := pow_one δ
      have h1 : ∫ x in halfBall n δ, S.v x ^ 2 ≤ |CM| * δ := by
        calc ∫ x in halfBall n δ, S.v x ^ 2 ≤ |CM| * δ ^ M := hv_le.trans hEabs
          _ ≤ |CM| * δ := mul_le_mul_of_nonneg_left hδM (abs_nonneg _)
      have h2 : 0 ≤ L * r₂⁻¹ := by positivity
      calc L * (r₂⁻¹ * ∫ x in halfBall n δ, S.v x ^ 2)
          = L * r₂⁻¹ * ∫ x in halfBall n δ, S.v x ^ 2 := by ring
        _ ≤ L * r₂⁻¹ * (|CM| * δ) := mul_le_mul_of_nonneg_left h1 h2
        _ = L * r₂⁻¹ * |CM| * δ := by ring
    have hsplit : L * (r₂⁻¹ * ∫ x in halfBall n r₂, S.v x ^ 2)
        = L * (r₂⁻¹ * ((∫ x in halfBall n r₂, S.v x ^ 2) - ∫ x in halfBall n δ, S.v x ^ 2))
          + L * (r₂⁻¹ * ∫ x in halfBall n δ, S.v x ^ 2) := by ring
    rw [hsplit]
    calc _ ≤ (RHS + Kin * Real.exp (2 * τ * (-Real.log (δ / 2) + ε * (δ / 2))) * (δ ^ 2)⁻¹ *
              ∫ x in halfBall n δ, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2)) + L * r₂⁻¹ * |CM| * δ :=
          add_le_add key hball
      _ ≤ (RHS + Kin * |CM| * E₀ * δ) + L * r₂⁻¹ * |CM| * δ := by gcongr
      _ = RHS + Cerr * δ := by rw [hCerr]; ring
  refine le_of_forall_pos_le_add fun η hη => ?_
  set δ : ℝ := min δ₀ (η / (Cerr + 1)) with hδ
  have hδpos : 0 < δ := lt_min hδ₀pos (by positivity)
  have h1 := hbound δ hδpos (min_le_left _ _)
  have h2 : Cerr * δ ≤ η := by
    have hδη : δ ≤ η / (Cerr + 1) := min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at hδη
    nlinarith
  linarith

/-! ### Assembly helpers -/

theorem exp_neg_log_div_two {y : ℝ} (hy : 0 < y) :
    Real.exp (-Real.log (1 / y) / 2) = Real.sqrt y := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, one_div, Real.log_inv]
  congr 1
  ring

theorem exp_neg_two_le_quarter : Real.exp (-2) ≤ 1 / 4 := by
  have h2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have h : (4 : ℝ) ≤ Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith
  rw [Real.exp_neg]
  rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num
  linarith

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  rw [Real.log_le_iff_le_exp (by norm_num)]
  linarith

/-- The `L²` bound of Steps 1–2: `∫_{B⁺_r} v² ≤ r √(g(r))` for small `r`. -/
theorem l2_decay (S : HalfBallSolution n) (hn : 0 < n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg : RegularProfile g) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Set.Ioc 0 r₀,
      ∫ x in halfBall n r, S.v x ^ 2 ≤ r * Real.sqrt (g r) := by
  have hg_flat := flat_of_regular g hg_pos hg_mono hg S.R S.R_pos
  obtain ⟨ε, rs, τ₀, hε, hrs, hεrs, hτ₀, hstep1⟩ := step1 S hn g hneu hg_pos hg_mono hg_flat
  obtain ⟨σ₀, hconv⟩ := hg.convex
  obtain ⟨C, σ₁, hgrowth⟩ := hg.growth
  obtain ⟨smin, hsmin⟩ := step2 (fun σ => Real.log (1 / g (Real.exp (-σ)))) σ₀ hconv hg.super
    C σ₁ hgrowth ε hε
  set s₁ : ℝ := max smin (-Real.log rs) with hs₁
  set r₁ : ℝ := Real.exp (-s₁) with hr₁
  have hr₁pos : 0 < r₁ := Real.exp_pos _
  have hr₁rs : r₁ ≤ rs := by
    have h1 : -s₁ ≤ Real.log rs := by
      have : -Real.log rs ≤ s₁ := le_max_right _ _
      linarith
    calc r₁ = Real.exp (-s₁) := rfl
      _ ≤ Real.exp (Real.log rs) := Real.exp_le_exp.2 h1
      _ = rs := Real.exp_log hrs
  obtain ⟨C₀, hC₀, hC₀bd⟩ := hstep1 r₁ ⟨hr₁pos, hr₁rs⟩
  have hεr₁ : ε * Real.exp (-s₁) ≤ 1 := by
    have : ε * r₁ ≤ ε * rs := mul_le_mul_of_nonneg_left hr₁rs hε.le
    have h' : ε * Real.exp (-s₁) = ε * r₁ := rfl
    linarith
  set I : ℝ → ℝ := fun s₂ => Real.exp s₂ * ∫ x in halfBall n (Real.exp (-s₂)), S.v x ^ 2
    with hI
  have hH : ∀ τ ≥ τ₀, ∀ s₂ ≥ s₁ + 2, ∀ Bd : ℝ,
      (∀ s ≥ s₁, Real.exp (2 * τ * GR ε s - Real.log (1 / g (Real.exp (-s)))) ≤ Bd) →
      τ ^ 3 * Real.exp (2 * τ * GR ε s₂) * I s₂
        ≤ C₀ * Real.exp (2 * τ * GR ε (s₁ + 1)) + C₀ * τ ^ 2 * Bd := by
    intro τ hτ s₂ hs₂ Bd hBd
    have hτpos : 0 < τ := lt_of_lt_of_le hτ₀ hτ
    have hr₂ : Real.exp (-s₂) ∈ Set.Ioc 0 (r₁ / 4) := by
      refine ⟨Real.exp_pos _, ?_⟩
      have e1 : Real.exp (-s₂) ≤ Real.exp (-s₁ + -2) := Real.exp_le_exp.2 (by linarith)
      rw [Real.exp_add] at e1
      have e2 := exp_neg_two_le_quarter
      have e3 : Real.exp (-s₁) * Real.exp (-2) ≤ Real.exp (-s₁) * (1 / 4) :=
        mul_le_mul_of_nonneg_left e2 (Real.exp_pos _).le
      calc Real.exp (-s₂) ≤ Real.exp (-s₁) * Real.exp (-2) := e1
        _ ≤ Real.exp (-s₁) * (1 / 4) := e3
        _ = r₁ / 4 := by rw [hr₁]; ring
    have hBd' : ∀ ρ ∈ Set.Ioc 0 r₁, Real.exp (2 * τ * (-Real.log ρ + ε * ρ)) * g ρ ≤ Bd := by
      intro ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hs : s₁ ≤ -Real.log ρ := by
        have : Real.log ρ ≤ Real.log r₁ := Real.log_le_log hρ0 hρ.2
        rw [hr₁, Real.log_exp] at this
        linarith
      have h := hBd (-Real.log ρ) hs
      have e1 : Real.exp (-(-Real.log ρ)) = ρ := by rw [neg_neg, Real.exp_log hρ0]
      have e2 : GR ε (-Real.log ρ) = -Real.log ρ + ε * ρ := by
        unfold GR; rw [e1]
      rw [e1, e2, Real.exp_sub, Real.exp_log (by have := hg_pos ρ hρ0; positivity)] at h
      have hgρ : 0 < g ρ := hg_pos ρ hρ0
      calc Real.exp (2 * τ * (-Real.log ρ + ε * ρ)) * g ρ
          = Real.exp (2 * τ * (-Real.log ρ + ε * ρ)) / (1 / g ρ) := by field_simp
        _ ≤ Bd := h
    have key := hC₀bd τ hτ _ hr₂ Bd hBd'
    have e1 : -Real.log (Real.exp (-s₂)) + ε * Real.exp (-s₂) = GR ε s₂ := by
      rw [Real.log_exp]; unfold GR; ring
    have e2 : (Real.exp (-s₂))⁻¹ = Real.exp s₂ := by rw [Real.exp_neg, inv_inv]
    have e3 : -Real.log (r₁ / 2) + ε * (r₁ / 2) = GR ε (s₁ + Real.log 2) := by
      have hexp : Real.exp (-(s₁ + Real.log 2)) = r₁ / 2 := by
        rw [show -(s₁ + Real.log 2) = -s₁ - Real.log 2 by ring, Real.exp_sub,
          Real.exp_log (by norm_num)]
      have hlog : Real.log (r₁ / 2) = -s₁ - Real.log 2 := by
        rw [Real.log_div hr₁pos.ne' (by norm_num), hr₁, Real.log_exp]
      unfold GR
      rw [hexp, hlog]
      ring
    have e4 : GR ε (s₁ + Real.log 2) ≤ GR ε (s₁ + 1) :=
      GR_mono hε.le hεr₁ (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)])
        (by linarith [log_two_le_one])
    have e5 : Real.exp (2 * τ * GR ε (s₁ + Real.log 2)) ≤ Real.exp (2 * τ * GR ε (s₁ + 1)) :=
      Real.exp_le_exp.2 (by nlinarith)
    rw [e1, e2, e3] at key
    calc τ ^ 3 * Real.exp (2 * τ * GR ε s₂) * I s₂
        = τ ^ 3 * Real.exp (2 * τ * GR ε s₂) *
            (Real.exp s₂ * ∫ x in halfBall n (Real.exp (-s₂)), S.v x ^ 2) := rfl
      _ ≤ C₀ * Real.exp (2 * τ * GR ε (s₁ + Real.log 2)) + C₀ * τ ^ 2 * Bd := key
      _ ≤ C₀ * Real.exp (2 * τ * GR ε (s₁ + 1)) + C₀ * τ ^ 2 * Bd := by
          have := mul_le_mul_of_nonneg_left e5 hC₀.le
          linarith
  have hev := hsmin s₁ (le_max_left _ _) C₀ τ₀ hC₀ hτ₀ I hH
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.1 hev
  refine ⟨Real.exp (-S₀), Real.exp_pos _, fun r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  have hs : S₀ ≤ -Real.log r := by
    have : Real.log r ≤ Real.log (Real.exp (-S₀)) := Real.log_le_log hr0 hr.2
    rw [Real.log_exp] at this
    linarith
  have h := hS₀ (-Real.log r) hs
  have e1 : Real.exp (-(-Real.log r)) = r := by rw [neg_neg, Real.exp_log hr0]
  simp only [hI, e1] at h
  rw [exp_neg_log_div_two (hg_pos r hr0), Real.exp_neg, Real.exp_log hr0] at h
  have := mul_le_mul_of_nonneg_left h hr0.le
  rwa [← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul] at this

end RPkg

/-! ## Package R: interior decay from the refined data (Proposition R) -/

/-- **Proposition R.** Small conormal data, bounded by a regular nondecreasing profile `g`,
force interior decay at rate `√g`. -/
theorem HalfBallSolution.interior_decay (S : HalfBallSolution n) (hn : 0 < n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg : RegularProfile g) :
    ∃ Cd r₀ : ℝ, 0 < Cd ∧ 0 < r₀ ∧ ∀ r ∈ Set.Ioc 0 r₀,
      ∫ x in halfBall n r, (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2) ≤ Cd * Real.sqrt (g (Cd * r)) := by
  -- `0 < n` is necessary: for `n = 0` the flat piece is `{0}`, the Neumann hypothesis is vacuous,
  -- and `v x = x 0`, `g r = exp (-1 / r²)` is a counterexample (the left side is `4 r³ / 3`).
  obtain ⟨r₀', hr₀', hl2⟩ := RPkg.l2_decay S hn g hneu hg_pos hg_mono hg
  obtain ⟨Cc, rc, hCc, hrc, hcacc⟩ := RPkg.caccioppoli S g hneu hg_pos hg_mono
  obtain ⟨Cg1, hCg1⟩ := RPkg.flat_of_regular g hg_pos hg_mono hg S.R S.R_pos 1
  set r₀ : ℝ := min (min (r₀' / 2) rc) (min (1 / 2) (min (S.R / 4) (1 / (2 * (|Cg1| + 1)))))
    with hr₀
  have hr₀pos : 0 < r₀ := by
    have h1 : 0 < r₀' / 2 := by positivity
    have h2 : 0 < S.R / 4 := by have := S.R_pos; positivity
    have h3 : 0 < 1 / (2 * (|Cg1| + 1)) := by positivity
    exact lt_min (lt_min h1 hrc) (lt_min (by norm_num) (lt_min h2 h3))
  refine ⟨max 2 (1 + 2 * Cc), r₀, lt_of_lt_of_le two_pos (le_max_left _ _), hr₀pos,
    fun r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  have hrr₀ : r ≤ r₀ := hr.2
  have hr_a : r ≤ r₀' / 2 := hrr₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr_c : r ≤ rc := hrr₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr_h : r ≤ 1 / 2 := hrr₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr_R : r ≤ S.R / 4 :=
    hrr₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr_g : r ≤ 1 / (2 * (|Cg1| + 1)) :=
    hrr₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hRpos := S.R_pos
  have h2r_R : 2 * r < S.R := by linarith
  -- `g(2r) ≤ 1`
  have hg2r_pos : 0 < g (2 * r) := hg_pos _ (by linarith)
  have hg2r_le : g (2 * r) ≤ 1 := by
    have h := hCg1 (2 * r) ⟨by linarith, h2r_R⟩
    rw [pow_one] at h
    have h1 : Cg1 * (2 * r) ≤ (|Cg1| + 1) * (2 * r) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cg1]) (by linarith)
    have h2 : (|Cg1| + 1) * (2 * r) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hr_g
      linarith
    linarith
  have hgr_le : g r ≤ g (2 * r) :=
    hg_mono (Set.mem_Ioi.2 hr0) (Set.mem_Ioi.2 (by linarith)) (by linarith)
  have hsq_mono : Real.sqrt (g r) ≤ Real.sqrt (g (2 * r)) := Real.sqrt_le_sqrt hgr_le
  have hg_le_sqrt : g (2 * r) ≤ Real.sqrt (g (2 * r)) := by
    have h1 : g (2 * r) ^ 2 ≤ g (2 * r) := by nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hg2r_pos.le] at h2
  -- the two `L²` bounds and Caccioppoli
  have hA : ∫ x in halfBall n r, S.v x ^ 2 ≤ r * Real.sqrt (g r) :=
    hl2 r ⟨hr0, by linarith⟩
  have hB : ∫ x in halfBall n (2 * r), S.v x ^ 2 ≤ 2 * r * Real.sqrt (g (2 * r)) :=
    hl2 (2 * r) ⟨by linarith, by linarith⟩
  have hC := hcacc r ⟨hr0, hr_c⟩
  -- splitting the integral
  have hrR : r < S.R := by linarith
  have hint1 : IntegrableOn (fun x => S.v x ^ 2) (halfBall n r) :=
    RPkg.integrableOn_halfBall_of_continuousOn hrR (S.v_continuousOn.pow 2)
  have hint2 : IntegrableOn (fun x => ‖S.Dv x‖ ^ 2) (halfBall n r) :=
    RPkg.integrableOn_halfBall_of_continuousOn hrR (S.Dv_continuousOn.norm.pow 2)
  have hsplit : ∫ x in halfBall n r, (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2)
      = (∫ x in halfBall n r, S.v x ^ 2) + r ^ 2 * ∫ x in halfBall n r, ‖S.Dv x‖ ^ 2 := by
    rw [integral_add hint1 (hint2.const_mul _), integral_const_mul]
  rw [hsplit]
  have hrn : r ^ (n + 2) ≤ 1 := pow_le_one₀ hr0.le (by linarith)
  have hsq_nonneg := Real.sqrt_nonneg (g (2 * r))
  have hbound : (∫ x in halfBall n r, S.v x ^ 2) + r ^ 2 * ∫ x in halfBall n r, ‖S.Dv x‖ ^ 2
      ≤ (1 + 2 * Cc) * Real.sqrt (g (2 * r)) := by
    have h1 : r * Real.sqrt (g r) ≤ Real.sqrt (g (2 * r)) := by
      have := mul_le_mul hr_h hsq_mono (Real.sqrt_nonneg _) (by norm_num)
      nlinarith
    have h2 : 2 * r * Real.sqrt (g (2 * r)) ≤ Real.sqrt (g (2 * r)) := by nlinarith
    have h3 : r ^ (n + 2) * g (2 * r) ≤ Real.sqrt (g (2 * r)) := by
      have := mul_le_mul hrn hg_le_sqrt hg2r_pos.le (by norm_num)
      linarith
    have h4 : Cc * ((∫ x in halfBall n (2 * r), S.v x ^ 2) + r ^ (n + 2) * g (2 * r))
        ≤ Cc * (2 * Real.sqrt (g (2 * r))) := by
      apply mul_le_mul_of_nonneg_left _ hCc.le
      linarith
    nlinarith
  have hCd : 1 + 2 * Cc ≤ max 2 (1 + 2 * Cc) := le_max_right _ _
  have hmono : Real.sqrt (g (2 * r)) ≤ Real.sqrt (g (max 2 (1 + 2 * Cc) * r)) := by
    apply Real.sqrt_le_sqrt
    apply hg_mono (Set.mem_Ioi.2 (by linarith)) (Set.mem_Ioi.2 (by positivity))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr0.le
  calc _ ≤ (1 + 2 * Cc) * Real.sqrt (g (2 * r)) := hbound
    _ ≤ max 2 (1 + 2 * Cc) * Real.sqrt (g (max 2 (1 + 2 * Cc) * r)) :=
        mul_le_mul hCd hmono hsq_nonneg (by positivity)

end MazyaRefinedCauchy
