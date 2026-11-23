module

public import MazyaRefinedCauchy.Interfaces

/-!
# Theorem I(a)

Assembly of the proof from the package interfaces in `MazyaRefinedCauchy.Interfaces`.

The route:

1. `exists_regular_majorant` (F5) replaces `h` by a positive, nondecreasing, regular majorant `g`
   on `(0, r₀)` with `r log(1/g(r)) → ∞`.
2. `collar_reduction` (C), applied with `R₁ = r₀ / (2κ)`, gives a half-ball solution `S` and the
   collar map `F`.
3. The conormal comparison of the collar step, `‖F X‖ ≤ κ‖X‖`, `‖X‖ ≤ κ‖F X‖` and the monotonicity
   of `g` give the Neumann bound `|⟪A ∇v, e_d⟫| ≤ κ g(κ |X|)` for `S`.
4. `RegularProfile.scale` (G) and `HalfBallSolution.interior_decay` (R) give interior decay at rate
   `√(κ g(κ Cd r))`; `superexp_of_tendsto` (G) turns this into decay faster than every
   `e^{-N/r}` for the solution restricted to a smaller half-ball.
5. `HalfBallSolution.vanish_of_superexp` (PL) makes `v` vanish on a ball tangent to the flat
   boundary at `0`; `weak_ucp` (U) spreads this to the whole half-ball.
6. The covering clause of `collar_reduction` transports the vanishing back to `u` near `0`.
-/

public section

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazyaRefinedCauchy

namespace MainAAux

variable {n : ℕ}

/-- The vertical coordinate is continuous. -/
private lemma continuous_vcoord : Continuous (vcoord : Space n → ℝ) := by
  show Continuous fun x : Space n => x (Fin.last n)
  fun_prop

/-- The vertical coordinate is linear. -/
private lemma isLinearMap_vcoord : IsLinearMap ℝ (vcoord : Space n → ℝ) :=
  { map_add := fun x y => by simp [vcoord]
    map_smul := fun c x => by simp [vcoord] }

private lemma halfBall_eq (R : ℝ) :
    halfBall n R = Metric.ball (0 : Space n) R ∩ {x | 0 < vcoord x} := by
  ext x
  simp [halfBall]

/-- Half-balls are open. -/
private lemma isOpen_halfBall (R : ℝ) : IsOpen (halfBall n R) := by
  rw [halfBall_eq]
  exact Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_vcoord)

/-- Half-balls are convex. -/
private lemma convex_halfBall (R : ℝ) : Convex ℝ (halfBall n R) := by
  rw [halfBall_eq]
  exact (convex_ball 0 R).inter (convex_halfSpace_gt isLinearMap_vcoord 0)

private lemma vcoord_smul_ed (s : ℝ) : vcoord (s • ed n) = s := by
  simp [vcoord, ed]

private lemma norm_smul_ed (s : ℝ) : ‖s • ed n‖ = |s| := by
  simp [ed, norm_smul]

/-- The energy density of a half-ball solution is integrable on every strictly smaller half-ball:
the closure of the smaller half-ball is a compact subset of `closedHalfBall n S.R`, on which `v`
and `Dv` are continuous. -/
private lemma integrableOn_halfBall (S : HalfBallSolution n) {r : ℝ} (hr : r < S.R) (c : ℝ) :
    IntegrableOn (fun x => S.v x ^ 2 + c * ‖S.Dv x‖ ^ 2) (halfBall n r) := by
  have hK : IsCompact (Metric.closedBall (0 : Space n) r ∩ {x | 0 ≤ vcoord x}) :=
    (isCompact_closedBall 0 r).inter_right (isClosed_le continuous_const continuous_vcoord)
  have hsub : Metric.closedBall (0 : Space n) r ∩ {x | 0 ≤ vcoord x} ⊆ closedHalfBall n S.R :=
    fun x hx => ⟨lt_of_le_of_lt (mem_closedBall_zero_iff.1 hx.1) hr, hx.2⟩
  have hcont : ContinuousOn (fun x => S.v x ^ 2 + c * ‖S.Dv x‖ ^ 2) (closedHalfBall n S.R) :=
    (S.v_continuousOn.pow 2).add (continuousOn_const.mul (S.Dv_continuousOn.norm.pow 2))
  refine ((hcont.mono hsub).integrableOn_compact hK).mono_set ?_
  intro x hx
  exact ⟨mem_closedBall_zero_iff.2 hx.1.le, hx.2.le⟩

/-- A function bounded by `A e^{-N/r}` for `r < δ` and by a constant for `δ ≤ r < R'` is bounded by
a multiple of `e^{-N/r}` on all of `(0, R')`. -/
private lemma exists_bound_exp {φ : ℝ → ℝ} {R' δ A B N : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hsmall : ∀ r ∈ Set.Ioo 0 R', r < δ → φ r ≤ A * Real.exp (-N / r))
    (hlarge : ∀ r ∈ Set.Ioo 0 R', δ ≤ r → φ r ≤ B) :
    ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 R', φ r ≤ Cn * Real.exp (-N / r) := by
  refine ⟨A + B * Real.exp (|N| / δ), fun r hr => ?_⟩
  have hexp_pos : 0 < Real.exp (-N / r) := Real.exp_pos _
  have hBe : 0 ≤ B * Real.exp (|N| / δ) := mul_nonneg hB (Real.exp_pos _).le
  rcases lt_or_ge r δ with hrδ | hrδ
  · calc φ r ≤ A * Real.exp (-N / r) := hsmall r hr hrδ
      _ ≤ (A + B * Real.exp (|N| / δ)) * Real.exp (-N / r) := by
        gcongr
        linarith
  · have hr0 : 0 < r := hr.1
    have h1 : 1 ≤ Real.exp (|N| / δ) * Real.exp (-N / r) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have h2 : N / r ≤ |N| / δ :=
        calc N / r ≤ |N| / r := by gcongr; exact le_abs_self N
          _ ≤ |N| / δ := by gcongr
      have h3 : -N / r = -(N / r) := by ring
      linarith
    have hAe : 0 ≤ A * Real.exp (-N / r) := mul_nonneg hA hexp_pos.le
    calc φ r ≤ B := hlarge r hr hrδ
      _ ≤ B * (Real.exp (|N| / δ) * Real.exp (-N / r)) := le_mul_of_one_le_right hB h1
      _ = B * Real.exp (|N| / δ) * Real.exp (-N / r) := by ring
      _ ≤ (A + B * Real.exp (|N| / δ)) * Real.exp (-N / r) := by
        rw [add_mul]
        linarith

end MainAAux

/-- **Theorem I(a).** Let `L u = div(a ∇u) + b · ∇u + c u`, where the matrix field `a` is smooth,
symmetric and uniformly elliptic, and `b`, `c` are continuous. Let `u` be `C²` in the domain above
the graph of a smooth `Γ`, with `u` and `∇u` (written `Du`) continuous up to the graph, and
`L u = 0` in the domain. Suppose the Dirichlet data vanish to infinite order at `0`, and the
conormal derivative `a ∇u · n` is bounded by `h(|x|)` on the graph, where `h(r) ≤ e^{-M/r}` for
small `r`, for every `M` (for positive `h` this says `r log(1/h(r)) → ∞`). Then `u = 0` near
`0`. -/
theorem mainA {n : ℕ} (hn : 0 < n)
    (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ) (hΓ0 : Γ 0 = 0) (ρ : ℝ) (hρ : 0 < ρ)
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
    (h : ℝ → ℝ)
    (hNeu : ∀ x ∈ boundaryPiece Γ ρ, |⟪a x (Du x), outerNormal Γ x⟫_ℝ| ≤ h ‖x‖)
    (hh : ∀ M : ℝ, ∀ᶠ r in 𝓝[>] 0, h r ≤ Real.exp (-M / r)) :
    ∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → u x = 0 := by
  -- Step 1: a regular majorant `g` of `h`.
  obtain ⟨g, r₀, hr₀, hgh, hg_pos, hg_mono, hg_reg, hg_lim⟩ := exists_regular_majorant h hh
  -- Step 2: the conormal collar.
  obtain ⟨κ, hκ, hcol⟩ := collar_reduction hn Γ hΓ hΓ0 ρ hρ a ha ha_symm ha_ell b hb c hc u Du hu
    hu_cont hDu_cont hDu hL hDir
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ
  obtain ⟨S, F, hSR, hmap, hflat, hcover, -, -⟩ := hcol (r₀ / (2 * κ)) (by positivity)
  -- Step 3: the Neumann bound for `S` with the profile `r ↦ κ g(κ r)`.
  have hneuS : ∀ x ∈ flatPiece n S.R, x ≠ 0 →
      |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ (fun r => κ * g (κ * r)) ‖x‖ := by
    intro x hx hx0
    obtain ⟨hFx, hFle, hle, hcmp⟩ := hflat x hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hFpos : 0 < ‖F x‖ := by
      by_contra hcon
      have hF0 : ‖F x‖ = 0 := le_antisymm (not_lt.1 hcon) (norm_nonneg _)
      rw [hF0, mul_zero] at hle
      linarith
    have hFlt : ‖F x‖ < r₀ := by
      have hxR : ‖x‖ < S.R := hx.1
      calc ‖F x‖ ≤ κ * ‖x‖ := hFle
        _ < κ * S.R := by gcongr
        _ ≤ κ * (r₀ / (2 * κ)) := by gcongr
        _ = r₀ / 2 := by field_simp
        _ < r₀ := by linarith
    have h1 : h ‖F x‖ ≤ g ‖F x‖ := hgh _ ⟨hFpos, hFlt⟩
    have h2 : g ‖F x‖ ≤ g (κ * ‖x‖) :=
      hg_mono (Set.mem_Ioi.2 hFpos) (Set.mem_Ioi.2 (mul_pos hκpos hxpos)) hFle
    have h3 := hNeu (F x) hFx
    calc |⟪S.A x (S.Dv x), ed n⟫_ℝ|
        ≤ κ * |⟪a (F x) (Du (F x)), outerNormal Γ (F x)⟫_ℝ| := hcmp
      _ ≤ κ * g (κ * ‖x‖) := by
        gcongr
        linarith
  have hgS_pos : ∀ r, 0 < r → 0 < (fun r => κ * g (κ * r)) r :=
    fun r hr => mul_pos hκpos (hg_pos _ (mul_pos hκpos hr))
  have hgS_mono : MonotoneOn (fun r => κ * g (κ * r)) (Set.Ioi 0) := by
    intro r hr s hs hrs
    exact mul_le_mul_of_nonneg_left
      (hg_mono (Set.mem_Ioi.2 (mul_pos hκpos hr)) (Set.mem_Ioi.2 (mul_pos hκpos hs))
        (mul_le_mul_of_nonneg_left hrs hκpos.le)) hκpos.le
  have hgS_reg : RegularProfile (fun r => κ * g (κ * r)) :=
    RegularProfile.scale g κ hκ hg_pos hg_mono hg_reg
  -- Step 4: interior decay.
  obtain ⟨Cd, r₁, hCd, hr₁, hdec⟩ := S.interior_decay _ hneuS hgS_pos hgS_mono hgS_reg
  -- Step 5: decay faster than every `e^{-N/r}` on a smaller half-ball.
  have hR'pos : 0 < min (S.R / 2) (min r₁ 1) := lt_min (half_pos S.R_pos) (lt_min hr₁ one_pos)
  have hR'le : min (S.R / 2) (min r₁ 1) ≤ S.R := (min_le_left _ _).trans (half_le_self S.R_pos.le)
  have hbound : ∀ r ∈ Set.Ioo 0 (min (S.R / 2) (min r₁ 1)),
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2)
        ≤ Cd * ((r ^ 2)⁻¹ * Real.sqrt (κ * g (κ * (Cd * r)))) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hrR' : r < min (S.R / 2) (min r₁ 1) := hr.2
    have hrR : r < S.R := lt_of_lt_of_le hrR' hR'le
    have hr1 : r ≤ 1 := hrR'.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hrr₁ : r ≤ r₁ := hrR'.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hint1 : IntegrableOn (fun x => S.v x ^ 2 + ‖S.Dv x‖ ^ 2) (halfBall n r) := by
      simpa using MainAAux.integrableOn_halfBall S hrR 1
    have hint2 : IntegrableOn (fun x => S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2) (halfBall n r) :=
      MainAAux.integrableOn_halfBall S hrR (r ^ 2)
    have hmeas : MeasurableSet (halfBall n r) := (MainAAux.isOpen_halfBall r).measurableSet
    have hinv : 1 ≤ (r ^ 2)⁻¹ := (one_le_inv₀ (by positivity)).2 (pow_le_one₀ hr0.le hr1)
    have hdec' : ∫ x in halfBall n r, (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2)
        ≤ Cd * Real.sqrt (κ * g (κ * (Cd * r))) := hdec r ⟨hr0, hrr₁⟩
    calc ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2)
        ≤ ∫ x in halfBall n r, (r ^ 2)⁻¹ * (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2) := by
          refine setIntegral_mono_on hint1 (Integrable.const_mul hint2 _) hmeas ?_
          intro x _
          have hexp : (r ^ 2)⁻¹ * (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2)
              = (r ^ 2)⁻¹ * S.v x ^ 2 + ‖S.Dv x‖ ^ 2 := by
            rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
          rw [hexp]
          have : S.v x ^ 2 ≤ (r ^ 2)⁻¹ * S.v x ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hinv
          linarith
      _ = (r ^ 2)⁻¹ * ∫ x in halfBall n r, (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2) :=
          integral_const_mul _ _
      _ ≤ (r ^ 2)⁻¹ * (Cd * Real.sqrt (κ * g (κ * (Cd * r)))) := by
          gcongr
      _ = Cd * ((r ^ 2)⁻¹ * Real.sqrt (κ * g (κ * (Cd * r)))) := by ring
  have hdecay : ∀ N : ℝ, ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 (S.shrink _ hR'pos hR'le).R,
      ∫ x in halfBall n r, ((S.shrink _ hR'pos hR'le).v x ^ 2
        + ‖(S.shrink _ hR'pos hR'le).Dv x‖ ^ 2) ≤ Cn * Real.exp (-N / r) := by
    intro N
    show ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 (min (S.R / 2) (min r₁ 1)),
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cn * Real.exp (-N / r)
    obtain ⟨δ, hδpos, hδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (superexp_of_tendsto g hg_pos hg_lim (κ * Cd) (mul_pos hκpos hCd) N)
    have hδ0 : 0 < δ := hδpos
    refine MainAAux.exists_bound_exp (φ := fun r => ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2))
      (A := Cd * Real.sqrt κ)
      (B := Cd * ((δ ^ 2)⁻¹ * Real.sqrt (κ * g (κ * (Cd * min (S.R / 2) (min r₁ 1))))))
      hδ0 (by positivity) (by positivity) ?_ ?_
    · intro r hr hrδ
      have h1 := hbound r hr
      have h2 : (r ^ 2)⁻¹ * Real.sqrt (g (κ * Cd * r)) ≤ Real.exp (-N / r) := hδ ⟨hr.1, hrδ⟩
      have h3 : Real.sqrt (κ * g (κ * (Cd * r))) = Real.sqrt κ * Real.sqrt (g (κ * Cd * r)) := by
        rw [Real.sqrt_mul hκpos.le, mul_assoc]
      calc (∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2))
          ≤ Cd * ((r ^ 2)⁻¹ * Real.sqrt (κ * g (κ * (Cd * r)))) := h1
        _ = (Cd * Real.sqrt κ) * ((r ^ 2)⁻¹ * Real.sqrt (g (κ * Cd * r))) := by rw [h3]; ring
        _ ≤ (Cd * Real.sqrt κ) * Real.exp (-N / r) := by gcongr
    · intro r hr hrδ
      have h1 := hbound r hr
      have hr0 : 0 < r := hr.1
      have hmono : g (κ * (Cd * r)) ≤ g (κ * (Cd * min (S.R / 2) (min r₁ 1))) :=
        hg_mono (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
          (by gcongr; exact hr.2.le)
      calc (∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2))
          ≤ Cd * ((r ^ 2)⁻¹ * Real.sqrt (κ * g (κ * (Cd * r)))) := h1
        _ ≤ Cd * ((δ ^ 2)⁻¹ * Real.sqrt (κ * g (κ * (Cd * min (S.R / 2) (min r₁ 1))))) := by
          gcongr
  obtain ⟨r', hr', hvan⟩ := (S.shrink _ hR'pos hR'le).vanish_of_superexp hdecay
  -- Step 6: a point of the half-ball near which `v` vanishes.
  have hspos : 0 < min r' (S.R / 2) := lt_min hr' (half_pos S.R_pos)
  have hx₀U : min r' (S.R / 2) • ed n ∈ halfBall n S.R := by
    refine ⟨?_, ?_⟩
    · rw [MainAAux.norm_smul_ed, abs_of_pos hspos]
      linarith [min_le_right r' (S.R / 2), half_lt_self S.R_pos]
    · rw [MainAAux.vcoord_smul_ed]
      exact hspos
  have hx₀ball : min r' (S.R / 2) • ed n ∈ Metric.ball (r' • ed n) r' := by
    rw [Metric.mem_ball, dist_eq_norm, ← sub_smul, MainAAux.norm_smul_ed, abs_lt]
    constructor <;> linarith [min_le_left r' (S.R / 2)]
  have hloc : ∀ᶠ x in 𝓝 (min r' (S.R / 2) • ed n), S.v x = 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx₀ball] with x hx
    exact hvan x hx
  -- Step 7: weak unique continuation in the half-ball.
  have hzero : ∀ x ∈ halfBall n S.R, S.v x = 0 := by
    refine weak_ucp (MainAAux.isOpen_halfBall S.R) (MainAAux.convex_halfBall S.R).isPreconnected
      S.A S.B S.C S.coeffs.contDiff_A.contDiffOn (fun x _ => S.coeffs.symm x) ?_
      S.coeffs.cont_B.continuousOn S.coeffs.cont_C.continuousOn S.v S.v_contDiffOn S.eqn
      _ hx₀U hloc
    intro x _ ξ hξ
    have hell := S.coeffs.ell x ξ
    have hξpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hlam := S.coeffs.lam_pos
    have : 0 < S.lam * ‖ξ‖ ^ 2 := by positivity
    linarith
  -- Step 8: back to `u` through the collar map.
  obtain ⟨ε, hε, hcov⟩ := hcover
  refine ⟨ε, hε, fun x hx hxε => ?_⟩
  obtain ⟨X, hX, rfl⟩ := hcov x hx hxε
  rw [← (hmap X hX).2]
  exact hzero X hX

end MazyaRefinedCauchy
