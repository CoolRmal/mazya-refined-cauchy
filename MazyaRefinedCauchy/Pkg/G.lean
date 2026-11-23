module

public import MazyaRefinedCauchy.Setup
public import Mathlib
public import MazyaRefinedCauchy.Pkg.F5


@[expose] public section

/-!
# Work package G

The theorems stated in this file are the frozen contract of package G (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package G: glue lemmas used by the assembly -/

/-- Restricting a half-ball solution to a smaller radius. -/
noncomputable def HalfBallSolution.shrink (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) : HalfBallSolution n where
  A := S.A
  B := S.B
  C := S.C
  lam := S.lam
  K := S.K
  coeffs := S.coeffs
  A_zero := S.A_zero
  R := R'
  R_pos := hR'
  conormal := fun x hx => S.conormal x ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  v := S.v
  Dv := S.Dv
  v_contDiffOn := S.v_contDiffOn.mono fun _ hx => ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  v_continuousOn := S.v_continuousOn.mono fun _ hx => ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  Dv_continuousOn := S.Dv_continuousOn.mono fun _ hx => ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  gradient_eq := fun x hx => S.gradient_eq x ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  eqn := fun x hx => S.eqn x ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩
  dirichlet_flat := fun N => (S.dirichlet_flat N).imp fun _ hC x hx =>
    hC x ⟨lt_of_lt_of_le hx.1 hle, hx.2⟩

theorem HalfBallSolution.shrink_R (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) : (S.shrink R' hR' hle).R = R' := rfl

theorem HalfBallSolution.shrink_data (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) :
    (S.shrink R' hR' hle).A = S.A ∧ (S.shrink R' hR' hle).v = S.v ∧
      (S.shrink R' hR' hle).Dv = S.Dv := ⟨rfl, rfl, rfl⟩

namespace GAux

/-! ### Helpers for `RegularProfile.scale`

Write `Λ_g(σ) = log (1 / g (e^{-σ}))` and `c = log κ ≥ 0`. For the rescaled profile
`h(r) = κ g(κ r)` one has `Λ_h(σ) = Λ_g(σ - c) - c`. The three lemmas below transfer
convexity, superlinearity and the growth bound along `f ↦ (σ ↦ f (σ - c) - c)`. -/

/-- The key identity `Λ_{κ g(κ ·)}(σ) = Λ_g(σ - log κ) - log κ`. -/
theorem log_one_div_scale (g : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (σ : ℝ) :
    Real.log (1 / (κ * g (κ * Real.exp (-σ)))) =
      Real.log (1 / g (Real.exp (-(σ - Real.log κ)))) - Real.log κ := by
  have h1 : κ * Real.exp (-σ) = Real.exp (-(σ - Real.log κ)) := by
    rw [show -(σ - Real.log κ) = Real.log κ + -σ by ring, Real.exp_add, Real.exp_log hκ]
  rw [h1]
  have hy : 0 < g (Real.exp (-(σ - Real.log κ))) := hg_pos _ (Real.exp_pos _)
  rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul hκ.ne' hy.ne']
  ring

/-- Convexity is preserved by `f ↦ (σ ↦ f (σ - c) - c)`. -/
theorem convexOn_shift {f : ℝ → ℝ} {σ₀ : ℝ} (hf : ConvexOn ℝ (Set.Ici σ₀) f) (c : ℝ) :
    ConvexOn ℝ (Set.Ici (σ₀ + c)) (fun σ => f (σ - c) - c) := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : x - c ∈ Set.Ici σ₀ := by
    simp only [Set.mem_Ici] at hx ⊢
    linarith
  have hy' : y - c ∈ Set.Ici σ₀ := by
    simp only [Set.mem_Ici] at hy ⊢
    linarith
  have key := hf.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at key ⊢
  have e : a * x + b * y - c = a * (x - c) + b * (y - c) := by linear_combination c * hab
  have hac : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  rw [e]
  linarith

/-- Superlinearity is preserved by `f ↦ (σ ↦ f (σ - c) - c)` (for `c ≥ 0`). -/
theorem tendsto_shift {f : ℝ → ℝ} (hf : Tendsto (fun σ => f σ / σ) atTop atTop) (c : ℝ)
    (hc : 0 ≤ c) : Tendsto (fun σ => (f (σ - c) - c) / σ) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨T, hT⟩ := tendsto_atTop_atTop.1 hf (|b| + 1)
  refine ⟨max (max T 1 + c) ((|b| + 2) * c + 1), fun σ hσ => ?_⟩
  have h1 : max T 1 + c ≤ σ := le_trans (le_max_left _ _) hσ
  have h2 : (|b| + 2) * c + 1 ≤ σ := le_trans (le_max_right _ _) hσ
  have hτ : T ≤ σ - c := by linarith [le_max_left T 1]
  have hτpos : 0 < σ - c := by linarith [le_max_right T 1]
  have hσpos : 0 < σ := by linarith
  have hB := hT (σ - c) hτ
  rw [le_div_iff₀ hτpos] at hB
  rw [le_div_iff₀ hσpos]
  have hb : b ≤ |b| := le_abs_self b
  nlinarith [mul_nonneg (sub_nonneg.2 hb) hσpos.le, abs_nonneg b]

/-- A superlinear function tends to `+∞`. -/
theorem tendsto_atTop_of_div {f : ℝ → ℝ} (hf : Tendsto (fun σ => f σ / σ) atTop atTop) :
    Tendsto f atTop atTop := by
  have h2 : Tendsto (fun σ => f σ / σ * σ) atTop atTop := hf.atTop_mul_atTop₀ tendsto_id
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with σ hσ
  field_simp

/-- The growth bound `f(σ + t) ≤ e^{Ct} f(σ)` is preserved by `f ↦ (σ ↦ f (σ - c) - c)`
(for `c ≥ 0` and superlinear `f`), with the constant `2 max C 0`. -/
theorem growth_shift {f : ℝ → ℝ} (hf_super : Tendsto (fun σ => f σ / σ) atTop atTop)
    {C σ₁ : ℝ} (hf : ∀ σ ≥ σ₁, ∀ t ≥ 0, f (σ + t) ≤ Real.exp (C * t) * f σ) (c : ℝ)
    (hc : 0 ≤ c) :
    ∃ C' σ₂ : ℝ, ∀ σ ≥ σ₂, ∀ t ≥ 0,
      f (σ + t - c) - c ≤ Real.exp (C' * t) * (f (σ - c) - c) := by
  obtain ⟨T, hT⟩ :=
    eventually_atTop.1 ((tendsto_atTop_of_div hf_super).eventually (eventually_ge_atTop (2 * c)))
  refine ⟨2 * max C 0, max (σ₁ + c) (T + c), fun σ hσ t ht => ?_⟩
  have hσ1 : σ₁ ≤ σ - c := by linarith [le_max_left (σ₁ + c) (T + c)]
  have hσ2 : T ≤ σ - c := by linarith [le_max_right (σ₁ + c) (T + c)]
  have hL : 2 * c ≤ f (σ - c) := hT _ hσ2
  have hgr := hf (σ - c) hσ1 t ht
  rw [show σ - c + t = σ + t - c by ring] at hgr
  have hE1 : 1 ≤ Real.exp (max C 0 * t) :=
    Real.one_le_exp (mul_nonneg (le_max_right _ _) ht)
  have hCE : Real.exp (C * t) ≤ Real.exp (max C 0 * t) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)
  have hE2 : Real.exp (2 * max C 0 * t) =
      Real.exp (max C 0 * t) * Real.exp (max C 0 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hE2]
  have h1 : f (σ + t - c) ≤ Real.exp (max C 0 * t) * f (σ - c) :=
    hgr.trans (mul_le_mul_of_nonneg_right hCE (by linarith))
  have h_inner : 0 ≤ Real.exp (max C 0 * t) * (f (σ - c) - c) - c := by
    nlinarith [mul_le_mul_of_nonneg_right hE1 (show 0 ≤ f (σ - c) - c by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hE1) h_inner]

end GAux

/-- Rescaling a regular profile: `r ↦ κ g(κ r)` is again regular, positive and nondecreasing. -/
theorem RegularProfile.scale (g : ℝ → ℝ) (κ : ℝ) (hκ : 1 ≤ κ) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (hg_mono : MonotoneOn g (Set.Ioi 0)) (hg : RegularProfile g) :
    RegularProfile (fun r => κ * g (κ * r)) := by
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ
  have hc : 0 ≤ Real.log κ := Real.log_nonneg hκ
  have key := GAux.log_one_div_scale g κ hκpos hg_pos
  obtain ⟨σ₀, hconv⟩ := hg.convex
  obtain ⟨C, σ₁, hgrowth⟩ := hg.growth
  refine ⟨⟨σ₀ + Real.log κ, ?_⟩, ?_, ?_⟩
  · simp only [key]
    exact GAux.convexOn_shift hconv _
  · simp only [key]
    exact GAux.tendsto_shift hg.super _ hc
  · simp only [key]
    exact GAux.growth_shift hg.super hgrowth _ hc

/-- If `r log(1/g(r)) → ∞`, then `r⁻² √(g(Cr))` is eventually below every `e^{-N/r}`. -/
theorem superexp_of_tendsto (g : ℝ → ℝ) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (hg : Tendsto (fun r => r * Real.log (1 / g r)) (𝓝[>] 0) atTop) (C : ℝ) (hC : 0 < C)
    (N : ℝ) : ∀ᶠ r in 𝓝[>] 0, (r ^ 2)⁻¹ * Real.sqrt (g (C * r)) ≤ Real.exp (-N / r) := by
  have hCr : Tendsto (fun r => C * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun r => C * r) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const_mul C).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hC hr
  have h := (hg.comp hCr).eventually (eventually_ge_atTop (2 * C * (N + 2)))
  filter_upwards [h, self_mem_nhdsWithin] with r hr hr0
  simp only [Function.comp_apply] at hr
  have hr0' : 0 < r := hr0
  have hy : 0 < g (C * r) := hg_pos _ (mul_pos hC hr0')
  rw [one_div, Real.log_inv] at hr
  -- `hr : 2 C (N + 2) ≤ C r (-log g(C r))`
  have h1 : 2 * (N + 2) ≤ r * -Real.log (g (C * r)) := by
    have h' : C * (2 * (N + 2)) ≤ C * (r * -Real.log (g (C * r))) := by linarith
    exact le_of_mul_le_mul_left h' hC
  have h2 : Real.log (g (C * r)) ≤ -(2 * (N + 2)) / r := by
    rw [le_div_iff₀ hr0']
    linarith
  have h3 : g (C * r) ≤ Real.exp (-(N + 2) / r) ^ 2 := by
    calc g (C * r) ≤ Real.exp (-(2 * (N + 2)) / r) := (Real.log_le_iff_le_exp hy).1 h2
      _ = Real.exp (-(N + 2) / r) ^ 2 := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
  have hsqrt : Real.sqrt (g (C * r)) ≤ Real.exp (-(N + 2) / r) := by
    calc Real.sqrt (g (C * r)) ≤ Real.sqrt (Real.exp (-(N + 2) / r) ^ 2) :=
          Real.sqrt_le_sqrt h3
      _ = Real.exp (-(N + 2) / r) := Real.sqrt_sq (Real.exp_pos _).le
  -- `e^{-1/r} ≤ r`, hence `e^{-2/r} ≤ r²`
  have h4 : Real.exp (-(1 / r)) ≤ r := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hr0', ← one_div]
    linarith [Real.add_one_le_exp (1 / r)]
  have h5 : Real.exp (-2 / r) ≤ r ^ 2 := by
    have e : Real.exp (-2 / r) = Real.exp (-(1 / r)) * Real.exp (-(1 / r)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e, sq]
    exact mul_le_mul h4 h4 (Real.exp_pos _).le hr0'.le
  have h6 : (r ^ 2)⁻¹ * Real.exp (-2 / r) ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact h5
  calc (r ^ 2)⁻¹ * Real.sqrt (g (C * r)) ≤ (r ^ 2)⁻¹ * Real.exp (-(N + 2) / r) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = ((r ^ 2)⁻¹ * Real.exp (-2 / r)) * Real.exp (-N / r) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ 1 * Real.exp (-N / r) := mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    _ = Real.exp (-N / r) := one_mul _

end MazyaRefinedCauchy
