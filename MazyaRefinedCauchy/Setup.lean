module

public import MazyaRefinedCauchy.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Common setting of the proof

This module fixes the objects shared by all steps of the proof:

* the vertical coordinate `vcoord` and the vertical unit vector `ed`;
* half-balls `halfBall n R = {‖x‖ < R, t > 0}` and `closedHalfBall n R = {‖x‖ < R, t ≥ 0}`;
* the divergence-form operator `ellOp A B C v = div(A ∇v) + B · ∇v + C v`;
* `GoodCoeffs`: global bounds on the coefficients;
* `HalfBallSolution`: a solution in a half-ball whose boundary is flat, whose conormal is
  vertical, and whose Dirichlet data are flat. The collar step (`Collar/*`) produces one from the
  data of Theorem I, and the later steps (`Refined/*`, `Inversion/*`) consume it.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-- The vertical coordinate `t = x (Fin.last n)` of a point of `ℝⁿ⁺¹`. -/
def vcoord (x : Space n) : ℝ := x (Fin.last n)

/-- The vertical unit vector `e_d`. -/
noncomputable def ed (n : ℕ) : Space n := EuclideanSpace.single (Fin.last n) 1

/-- The open half-ball `{x : ‖x‖ < R, t > 0}`. -/
def halfBall (n : ℕ) (R : ℝ) : Set (Space n) := {x | ‖x‖ < R ∧ 0 < vcoord x}

/-- The half-ball together with its flat boundary: `{x : ‖x‖ < R, t ≥ 0}`. -/
def closedHalfBall (n : ℕ) (R : ℝ) : Set (Space n) := {x | ‖x‖ < R ∧ 0 ≤ vcoord x}

/-- The flat boundary piece `{x : ‖x‖ < R, t = 0}`. -/
def flatPiece (n : ℕ) (R : ℝ) : Set (Space n) := {x | ‖x‖ < R ∧ vcoord x = 0}

/-- The divergence-form operator `L v = div(A ∇v) + B · ∇v + C v`. -/
noncomputable def ellOp (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n)
    (C : Space n → ℝ) (v : Space n → ℝ) (x : Space n) : ℝ :=
  divergence (fun y => A y (gradient v y)) x + ⟪B x, gradient v x⟫_ℝ + C x * v x

/-- Global bounds on the coefficients of `ellOp A B C`: `A` is `C²`, symmetric and uniformly
elliptic with constant `lam`, and `A`, its first two derivatives, `B` and `C` are bounded by `K`. -/
structure GoodCoeffs (A : Space n → Space n →L[ℝ] Space n) (B : Space n → Space n)
    (C : Space n → ℝ) (lam K : ℝ) : Prop where
  lam_pos : 0 < lam
  contDiff_A : ContDiff ℝ 2 A
  symm : ∀ x ξ η, ⟪A x ξ, η⟫_ℝ = ⟪ξ, A x η⟫_ℝ
  ell : ∀ x ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ
  bound_A : ∀ x, ‖A x‖ ≤ K
  bound_dA : ∀ x, ‖fderiv ℝ A x‖ ≤ K
  bound_d2A : ∀ x, ‖iteratedFDeriv ℝ 2 A x‖ ≤ K
  cont_B : Continuous B
  cont_C : Continuous C
  bound_B : ∀ x, ‖B x‖ ≤ K
  bound_C : ∀ x, |C x| ≤ K

/-- A solution in a half-ball with flat boundary, vertical conormal and flat Dirichlet data.

* the coefficients satisfy `GoodCoeffs` globally and `A 0 = id`;
* on the flat piece, `A x e_d` is a multiple of `e_d` (the conormal is vertical);
* `v` is `C²` in the half-ball, `v` and `Dv` are continuous up to the flat piece, `Dv = ∇v`
  inside, and `ellOp A B C v = 0` inside;
* the Dirichlet data vanish to infinite order at `0`. -/
structure HalfBallSolution (n : ℕ) where
  A : Space n → Space n →L[ℝ] Space n
  B : Space n → Space n
  C : Space n → ℝ
  lam : ℝ
  K : ℝ
  coeffs : GoodCoeffs A B C lam K
  A_zero : A 0 = ContinuousLinearMap.id ℝ (Space n)
  R : ℝ
  R_pos : 0 < R
  conormal : ∀ x ∈ flatPiece n R, ∃ c : ℝ, A x (ed n) = c • ed n
  v : Space n → ℝ
  Dv : Space n → Space n
  v_contDiffOn : ContDiffOn ℝ 2 v (halfBall n R)
  v_continuousOn : ContinuousOn v (closedHalfBall n R)
  Dv_continuousOn : ContinuousOn Dv (closedHalfBall n R)
  gradient_eq : ∀ x ∈ halfBall n R, gradient v x = Dv x
  eqn : ∀ x ∈ halfBall n R, ellOp A B C v x = 0
  dirichlet_flat : ∀ N : ℕ, ∃ Cn : ℝ, ∀ x ∈ flatPiece n R, |v x| ≤ Cn * ‖x‖ ^ N

end MazyaRefinedCauchy
