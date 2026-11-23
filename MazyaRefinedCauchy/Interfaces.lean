module

public import MazyaRefinedCauchy.Setup
public import Mathlib

@[expose] public section

/-!
# Interfaces between the steps of the proof

Each theorem below is the contract of one work package (see `BLUEPRINT.md`). The statements are
frozen while packages are proved in parallel; proofs are moved in when a package is complete.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F1: coordinates and integration by parts on half-spaces -/

/-- The point of `ℝⁿ⁺¹` with horizontal coordinates `y ∈ ℝⁿ` and vertical coordinate `t`. -/
noncomputable def lift (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Space n :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => y i) t)

theorem vcoord_lift (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) : vcoord (lift y t) = t := by
  sorry

theorem norm_lift_sq (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖lift y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  sorry

/-- Fubini in the splitting `ℝⁿ⁺¹ = ℝⁿ × ℝ`. -/
theorem integral_eq_integral_lift (f : Space n → ℝ) (hf : Integrable f) :
    ∫ x, f x = ∫ y : EuclideanSpace ℝ (Fin n), ∫ t : ℝ, f (lift y t) := by
  sorry

/-- Divergence theorem on the half-space `{t > η}` for a compactly supported field that is `C¹`
on a neighbourhood of the closed half-space; the outer normal is `-e_d`. -/
theorem integral_divergence_halfSpace (η : ℝ) (F : Space n → Space n)
    (hF : ∀ x, η ≤ vcoord x → ContDiffAt ℝ 1 F x) (hsupp : HasCompactSupport F) :
    ∫ x in {x : Space n | η < vcoord x}, divergence F x
      = -∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y η), ed n⟫_ℝ := by
  sorry

/-- Divergence theorem on `{t > 0}` for a compactly supported field that is `C¹` in the open
half-space and only continuous up to `{t = 0}`, provided its divergence is integrable. -/
theorem integral_divergence_halfSpace_of_continuousOn (F : Space n → Space n)
    (hF : ∀ x, 0 < vcoord x → ContDiffAt ℝ 1 F x)
    (hFc : ContinuousOn F {x | 0 ≤ vcoord x}) (hsupp : HasCompactSupport F)
    (hint : IntegrableOn (divergence F) {x | 0 < vcoord x}) :
    ∫ x in {x : Space n | 0 < vcoord x}, divergence F x
      = -∫ y : EuclideanSpace ℝ (Fin n), ⟪F (lift y 0), ed n⟫_ℝ := by
  sorry

/-- The integral of the divergence of a compactly supported `C¹` field vanishes. -/
theorem integral_divergence_eq_zero (F : Space n → Space n) (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) : ∫ x, divergence F x = 0 := by
  sorry

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

/-- Lemma 2.1(1): conjugation. -/
theorem carleman_conj (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 1 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 1 B x)
    (hφ : ContDiffAt ℝ 2 φ x) (hw : ContDiffAt ℝ 2 w x) :
    Real.exp (τ * φ x)
        * divMu μ (fun y => B y (gradient (fun z => Real.exp (-τ * φ z) * w z) y)) x
      = carlS μ B φ τ w x + carlT μ B φ τ w x := by
  sorry

/-- Lemma 2.1(2), pointwise: `2 (S w)(T w) μ = J + div(flux)`. Requires `B` symmetric. -/
theorem carleman_pointwise (μ : Space n → ℝ) (B : Space n → Space n →L[ℝ] Space n)
    (φ : Space n → ℝ) (τ : ℝ) (w : Space n → ℝ) (x : Space n)
    (hμ : ContDiffAt ℝ 2 μ x) (hμ0 : μ x ≠ 0) (hB : ContDiffAt ℝ 2 B x)
    (hsymm : ∀ y ξ η, ⟪B y ξ, η⟫_ℝ = ⟪ξ, B y η⟫_ℝ)
    (hφ : ContDiffAt ℝ 3 φ x) (hw : ContDiffAt ℝ 2 w x) :
    2 * carlS μ B φ τ w x * carlT μ B φ τ w x * μ x
      = carlJ μ B φ τ w x + divergence (carlFlux μ B φ τ w) x := by
  sorry

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
  sorry

/-! ## Package F3: compactness in `L²` -/

/-- Kolmogorov–Riesz type compactness: a sequence of continuous functions supported in a fixed
ball, bounded in `L²` and with uniformly controlled `L²` translations, has an `L²`-convergent
subsequence. -/
theorem exists_L2_convergent_subseq (f : ℕ → Space n → ℝ) (R M : ℝ)
    (hcont : ∀ j, Continuous (f j)) (hsupp : ∀ j x, R ≤ ‖x‖ → f j x = 0)
    (hbdd : ∀ j, ∫ x, f j x ^ 2 ≤ M)
    (htrans : ∀ j (h : Space n), ∫ x, (f j (x + h) - f j x) ^ 2 ≤ M * ‖h‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (g : Space n → ℝ), StrictMono φ ∧ MemLp g 2 ∧
      Tendsto (fun j => ∫ x, (f (φ j) x - g x) ^ 2) atTop (𝓝 0) := by
  sorry

/-! ## Package F4: harmonic functions: a sup bound from `L²` -/

/-- A harmonic function is bounded at the centre of a ball by its `L²` norm on the ball. -/
theorem harmonic_abs_le_L2 (n : ℕ) : ∃ Cn : ℝ, ∀ (u : Space n → ℝ) (x : Space n) (r : ℝ),
    0 < r → HarmonicOnNhd u (Metric.closedBall x r) →
      |u x| ≤ Cn * r ^ (-((n + 1 : ℝ) / 2)) * Real.sqrt (∫ y in Metric.ball x r, u y ^ 2) := by
  sorry

/-! ## Package F5: regular profiles and the majorant -/

/-- Regularity of a decay profile `h`: `Λ(σ) = log(1/h(e^{-σ}))` is eventually convex,
superlinear, and satisfies `Λ(σ + t) ≤ e^{Ct} Λ(σ)` for large `σ` and `t ≥ 0`. -/
structure RegularProfile (h : ℝ → ℝ) : Prop where
  convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => Real.log (1 / h (Real.exp (-σ))))
  super : Tendsto (fun σ => Real.log (1 / h (Real.exp (-σ))) / σ) atTop atTop
  growth : ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ t ≥ 0,
    Real.log (1 / h (Real.exp (-(σ + t)))) ≤ Real.exp (C * t) * Real.log (1 / h (Real.exp (-σ)))

/-- A profile with `r log(1/h(r)) → ∞` has a positive, nondecreasing, regular majorant with the
same property. -/
theorem exists_regular_majorant (h : ℝ → ℝ)
    (hh : Tendsto (fun r => r * Real.log (1 / h r)) (𝓝[>] 0) atTop) :
    ∃ g : ℝ → ℝ, ∃ r₀ > 0, (∀ r ∈ Set.Ioo 0 r₀, |h r| ≤ g r) ∧ (∀ r, 0 < r → 0 < g r) ∧
      MonotoneOn g (Set.Ioi 0) ∧ RegularProfile g ∧
      Tendsto (fun r => r * Real.log (1 / g r)) (𝓝[>] 0) atTop := by
  sorry

/-! ## Package F6: Carleman's quasianalyticity theorem -/

/-- **Denjoy–Carleman (Carleman's criterion).** A smooth function on `ℝ` whose derivatives are
bounded by `M k`, with `∑ M k ^ (-1/k) = ∞`, and which vanishes to infinite order at `0`, is
identically zero. -/
theorem denjoy_carleman (f : ℝ → ℂ) (M : ℕ → ℝ) (hf : ContDiff ℝ ∞ f) (hM : ∀ k, 0 < M k)
    (hbound : ∀ k x, ‖iteratedDeriv k f x‖ ≤ M k) (hzero : ∀ k, iteratedDeriv k f 0 = 0)
    (hdiv : ¬ Summable (fun k : ℕ => M k ^ (-(1 : ℝ) / k))) :
    ∀ x, f x = 0 := by
  sorry

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
  sorry

/-! ## Package R1: infinite order vanishing (Lemma R1) -/

/-- **Lemma R1.** Flat Dirichlet data and flat conormal data force infinite order vanishing. -/
theorem HalfBallSolution.integral_sq_le_pow (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg : ∀ N : ℕ, ∃ Cg : ℝ, ∀ r ∈ Set.Ioo 0 S.R, g r ≤ Cg * r ^ N) :
    ∀ M : ℕ, ∃ Cm : ℝ, ∀ r ∈ Set.Ioc 0 (S.R / 2), ∫ x in halfBall n r, S.v x ^ 2 ≤ Cm * r ^ M := by
  sorry

/-! ## Package R: interior decay from the refined data (Proposition R) -/

/-- **Proposition R.** Small conormal data, bounded by a regular nondecreasing profile `g`,
force interior decay at rate `√g`. -/
theorem HalfBallSolution.interior_decay (S : HalfBallSolution n) (g : ℝ → ℝ)
    (hneu : ∀ x ∈ flatPiece n S.R, x ≠ 0 → |⟪S.A x (S.Dv x), ed n⟫_ℝ| ≤ g ‖x‖)
    (hg_pos : ∀ r, 0 < r → 0 < g r) (hg_mono : MonotoneOn g (Set.Ioi 0))
    (hg : RegularProfile g) :
    ∃ Cd r₀ : ℝ, 0 < Cd ∧ 0 < r₀ ∧ ∀ r ∈ Set.Ioc 0 r₀,
      ∫ x in halfBall n r, (S.v x ^ 2 + r ^ 2 * ‖S.Dv x‖ ^ 2) ≤ Cd * Real.sqrt (g (Cd * r)) := by
  sorry

/-! ## Package PL: inversion and the Phragmén–Lindelöf principle (Proposition PL) -/

/-- **Proposition PL.** Interior decay faster than every `e^{-N/r}` forces the solution to vanish
on a ball tangent to the flat boundary at `0`. -/
theorem HalfBallSolution.vanish_of_superexp (S : HalfBallSolution n)
    (hdecay : ∀ N : ℝ, ∃ Cn : ℝ, ∀ r ∈ Set.Ioo 0 S.R,
      ∫ x in halfBall n r, (S.v x ^ 2 + ‖S.Dv x‖ ^ 2) ≤ Cn * Real.exp (-N / r)) :
    ∃ r' > 0, ∀ x ∈ Metric.ball (r' • ed n) r', S.v x = 0 := by
  sorry

/-! ## Package L: the Laplacian, quasianalyticity (Lemma DC) -/

/-- The inner unit normal of the graph of `Γ` at `0`. -/
noncomputable def innerNormalZero (Γ : (Fin n → ℝ) → ℝ) : Space n :=
  -outerNormal Γ 0

/-- Balls tangent to the boundary at `0` from inside lie in the domain. -/
theorem tangent_ball_subset_domain (hn : 0 < n) (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ)
    (hΓ0 : Γ 0 = 0) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R₀ > 0, ∀ R ∈ Set.Ioc 0 R₀, Metric.ball (R • innerNormalZero Γ) R ⊆ domain Γ ρ := by
  sorry

/-- **Kelvin transform.** If `u` is harmonic on an open set `W` not containing `0`, then
`|y|^{1-n} u(y/|y|²)` is harmonic on the image of `W` under inversion. -/
theorem kelvin_harmonicOnNhd {W : Set (Space n)} (hW : IsOpen W) (h0 : (0 : Space n) ∉ W)
    (u : Space n → ℝ) (hu : HarmonicOnNhd u W) :
    HarmonicOnNhd (fun y => ‖y‖ ^ (1 - (n : ℝ)) * u (‖y‖⁻¹ ^ 2 • y))
      {y | y ≠ 0 ∧ ‖y‖⁻¹ ^ 2 • y ∈ W} := by
  sorry

/-- **Lemma DC.** A harmonic function on a half-space `{⟪y, ν⟫ > λ}` that decays like
`e^{-ψ(|y|)}`, with `∫^∞ ψ(s)/s² ds = ∞` and `ψ` regular, vanishes on `{⟪y, ν⟫ > λ + 1}`. -/
theorem harmonic_halfSpace_eq_zero (hn : 0 < n) (ν : Space n) (hν : ‖ν‖ = 1) (lam : ℝ)
    (hlam : 1 ≤ lam) (U : Space n → ℝ) (hU : HarmonicOnNhd U {y | lam < ⟪y, ν⟫_ℝ})
    (ψ : ℝ → ℝ) (Cu : ℝ) (hdecay : ∀ y, lam < ⟪y, ν⟫_ℝ → |U y| ≤ Cu * Real.exp (-ψ ‖y‖))
    (hψ_mono : MonotoneOn ψ (Set.Ici 1))
    (hψ_log : Tendsto (fun s => ψ s / Real.log s) atTop atTop)
    (hψ_convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => ψ (Real.exp σ)))
    (hψ_div : ¬ IntegrableOn (fun s => ψ s / s ^ 2) (Set.Ici 1)) :
    ∀ y, lam + 1 < ⟪y, ν⟫_ℝ → U y = 0 := by
  sorry

/-! ## Package G: glue lemmas used by the assembly -/

/-- Restricting a half-ball solution to a smaller radius. -/
noncomputable def HalfBallSolution.shrink (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) : HalfBallSolution n := by
  sorry

theorem HalfBallSolution.shrink_R (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) : (S.shrink R' hR' hle).R = R' := by
  sorry

theorem HalfBallSolution.shrink_data (S : HalfBallSolution n) (R' : ℝ) (hR' : 0 < R')
    (hle : R' ≤ S.R) :
    (S.shrink R' hR' hle).A = S.A ∧ (S.shrink R' hR' hle).v = S.v ∧
      (S.shrink R' hR' hle).Dv = S.Dv := by
  sorry

/-- Rescaling a regular profile: `r ↦ κ g(κ r)` is again regular, positive and nondecreasing. -/
theorem RegularProfile.scale (g : ℝ → ℝ) (κ : ℝ) (hκ : 1 ≤ κ) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (hg_mono : MonotoneOn g (Set.Ioi 0)) (hg : RegularProfile g) :
    RegularProfile (fun r => κ * g (κ * r)) := by
  sorry

/-- If `r log(1/g(r)) → ∞`, then `r⁻² √(g(Cr))` is eventually below every `e^{-N/r}`. -/
theorem superexp_of_tendsto (g : ℝ → ℝ) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (hg : Tendsto (fun r => r * Real.log (1 / g r)) (𝓝[>] 0) atTop) (C : ℝ) (hC : 0 < C)
    (N : ℝ) : ∀ᶠ r in 𝓝[>] 0, (r ^ 2)⁻¹ * Real.sqrt (g (C * r)) ≤ Real.exp (-N / r) := by
  sorry

/-! ## Package C: the conormal collar -/

/-- **Collar reduction.** The data of Theorem I yield a half-ball solution `S` and a map `F`
from the half-ball onto a neighbourhood of `0` in the domain, transporting `v` to `u`, the flat
piece to the boundary piece, and comparing conormal derivatives and `L²` norms. -/
theorem collar_reduction (hn : 0 < n) (Γ : (Fin n → ℝ) → ℝ) (hΓ : ContDiff ℝ ∞ Γ) (hΓ0 : Γ 0 = 0)
    (ρ : ℝ) (hρ : 0 < ρ)
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
    :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ R₁ > 0, ∃ (S : HalfBallSolution n) (F : Space n → Space n), S.R ≤ R₁ ∧
      (∀ X ∈ halfBall n S.R, F X ∈ domain Γ ρ ∧ S.v X = u (F X)) ∧
      (∀ X ∈ flatPiece n S.R, F X ∈ boundaryPiece Γ ρ ∧ ‖F X‖ ≤ κ * ‖X‖ ∧ ‖X‖ ≤ κ * ‖F X‖ ∧
        |⟪S.A X (S.Dv X), ed n⟫_ℝ| ≤ κ * |⟪a (F X) (Du (F X)), outerNormal Γ (F X)⟫_ℝ|) ∧
      (∃ ε > 0, ∀ x ∈ domain Γ ρ, ‖x‖ < ε → ∃ X ∈ halfBall n S.R, F X = x) ∧
      (∀ W : Set (Space n), IsOpen W → (W ∩ F '' halfBall n S.R).Nonempty →
        ∃ V : Set (Space n), IsOpen V ∧ V.Nonempty ∧ V ⊆ halfBall n S.R ∧ ∀ X ∈ V, F X ∈ W) ∧
      (∀ r ∈ Set.Ioc 0 S.R,
        ∫ x in domain Γ ρ ∩ Metric.ball 0 (r / κ), u x ^ 2 ≤ κ * ∫ X in halfBall n r, S.v X ^ 2) := by
  sorry

end MazyaRefinedCauchy
