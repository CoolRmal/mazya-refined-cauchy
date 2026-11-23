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

**The frozen statement is false for `n = 0`** (see the comment in the proof of
`HalfBallSolution.interior_decay`); the proof below covers `0 < n`.
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
theorem grad_infinite_order (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg_flat : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) :
    ∀ M : ℕ, ∃ Cm rm : ℝ, 0 < rm ∧ ∀ r ∈ Set.Ioc 0 rm,
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cm * r ^ M := by
  intro M
  obtain ⟨Cm, hCm⟩ := S.integral_sq_le_pow g hneu hg_flat (M + 2)
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
  sorry

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
  sorry

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

/-- Scale-invariant derivative bounds for `ψ_δ`, uniform in `δ` and `r₁`. -/
theorem psiS_deriv_bound : ∃ Cψ : ℝ, 0 ≤ Cψ ∧ ∀ δ r₁ : ℝ, 0 < δ → 4 * δ ≤ r₁ → ∀ x : Space n,
    ‖x‖ * ‖gradient (psiS δ r₁) x‖ + ‖x‖ ^ 2 * ‖fderiv ℝ (gradient (psiS δ r₁)) x‖ ≤ Cψ := by
  sorry

/-- `∇ψ_δ` and `∇²ψ_δ` vanish where `ψ_δ` is locally constant. -/
theorem psiS_deriv_eq_zero {δ r₁ : ℝ} (hδ : 0 < δ) (hδr : 4 * δ ≤ r₁) {x : Space n}
    (hx : ‖x‖ < δ / 2 ∨ (δ < ‖x‖ ∧ ‖x‖ < r₁ / 2) ∨ r₁ < ‖x‖) :
    gradient (psiS δ r₁) x = 0 ∧ fderiv ℝ (gradient (psiS δ r₁)) x = 0 := by
  sorry

/-- `h = ψ_δ ρ^m` is smooth (it vanishes near `0`). -/
theorem hS_contDiff {δ r₁ : ℝ} (hδ : 0 < δ) (hn : 0 < n) : ContDiff ℝ ∞ (hS (n := n) δ r₁) := by
  sorry

/-- `∇h` is radial, vanishes where `ψ_δ` is locally zero, and `ρ |∇h| ≤ (Cψ + m) ρ^m`. -/
theorem gradient_hS (hn : 0 < n) : ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ δ r₁ : ℝ, 0 < δ → 4 * δ ≤ r₁ →
    ∀ x : Space n, (∃ c : ℝ, gradient (hS δ r₁) x = c • x) ∧
      ‖x‖ * ‖gradient (hS δ r₁) x‖ ≤ Ch * ‖x‖ ^ mR n ∧
      ((‖x‖ < δ / 2 ∨ r₁ < ‖x‖) → gradient (hS δ r₁) x = 0) := by
  sorry

/-- The hypotheses of `carleman` for `f = ψ_δ ρ^m v` and `Df = h Dv + v ∇h`. -/
theorem fS_carleman_hyps (S : HalfBallSolution n) (hn : 0 < n) {δ r₁ : ℝ} (hδ : 0 < δ)
    (hδr : 4 * δ ≤ r₁) (hr₁R : r₁ < S.R) :
    (∀ x, fS S δ r₁ x ≠ 0 → δ / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ r₁) ∧
    (∀ x, DfS S δ r₁ x ≠ 0 → δ / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ r₁) ∧
    (∀ x, 0 < vcoord x → ContDiffAt ℝ 2 (fS S δ r₁) x) ∧
    (∀ x, 0 < vcoord x → gradient (fS S δ r₁) x = DfS S δ r₁ x) ∧
    ContinuousOn (fS S δ r₁) {x | 0 ≤ vcoord x} ∧
    ContinuousOn (DfS S δ r₁) {x | 0 ≤ vcoord x} := by
  sorry

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
  sorry

/-- Lower bound of the left side of `carleman` for `f = ψ_δ ρ^m v`. -/
theorem fS_lhs_lower (S : HalfBallSolution n) (hn : 0 < n) {ε τ δ r₁ r₂ : ℝ} (hε : 0 < ε)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδr₂ : δ < r₂) (hr₂ : r₂ ≤ r₁ / 4) (hεr₁ : ε * r₁ ≤ 1 / 4)
    (hr₁R : r₁ < S.R) :
    Real.exp (2 * τ * (-Real.log r₂ + ε * r₂)) *
        (r₂⁻¹ * ∫ x in halfBall n r₂ \ halfBall n δ, S.v x ^ 2)
      ≤ ∫ x in {x : Space n | 0 < vcoord x},
          ‖x‖ * muR n x * Real.exp (2 * τ * phiR ε x) * fS S δ r₁ x ^ 2 := by
  sorry

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
  sorry

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
  sorry

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
  obtain ⟨CM, rm, hrm, hCM⟩ := grad_infinite_order S g hneu hg_pos hg_mono hg_flat M
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
theorem HalfBallSolution.interior_decay (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg : RegularProfile g) :
    ∃ Cd r₀ : ℝ, 0 < Cd ∧ 0 < r₀ ∧ ∀ r ∈ Set.Ioc 0 r₀,
      ∫ x in halfBall n r, (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2) ≤ Cd * Real.sqrt (g (Cd * r)) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- The statement is FALSE for `n = 0`: then `flatPiece 0 R = {0}`, so `hneu` is vacuous.
    -- Counterexample: `A = id`, `B = 0`, `C = 0`, `R = 1`, `v x = x 0`, `Dv = e_d`,
    -- `g r = exp (-1 / r²)` (a regular profile with `Λ(σ) = e^{2σ}`). The left side equals
    -- `∫₀^r (t² + r²) dt = 4 r³ / 3`, while `Cd √(g (Cd r)) = Cd exp (-1 / (2 Cd² r²)) = o(r³)`.
    sorry
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
