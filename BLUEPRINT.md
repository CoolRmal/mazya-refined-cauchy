# Blueprint

This file is the plan and progress log of the formalization. Each module lists its main
declarations, what they depend on, and their status (see the legend below the table).

Notation: `Space n = EuclideanSpace ℝ (Fin (n + 1))`, `d = n + 1 ≥ 2`, the last coordinate
`X (Fin.last n)` is written `t`, the open half-space is `{t > 0}`, and `e_d` is the last basis
vector. All analysis is done with classical (`C²`) solutions; no Sobolev spaces are used.

## Overall route

The proof of Theorem I in the informal note has two steps.

1. **Interior decay from the refined data** (Proposition R). In coordinates where the boundary is
   flat and its conormal is `e_d`, a Carleman estimate with the radial weight `e^{τ G(-log|X|)}`,
   `G(s) = s + ε e^{-s}`, has boundary terms that all contain the Neumann datum. Choosing
   `2τ + 1 = Λ'(s₂)` gives `∫_{B_r⁺} v² ≤ C h(Cr)^{1/2}`. The weight is singular at `0`, so the
   solution must first be shown to vanish to infinite order there (Lemma R1, a blow-up argument).
2. **From interior decay to vanishing.** For (a): inversion `X ↦ X/|X|²` maps a tangent ball onto
   a half-space, where a Carleman estimate with weight `y_d - C₀ log y_d` shows that solutions
   decaying faster than every exponential vanish (Proposition PL). For (b): the Kelvin transform,
   a partial Fourier transform and the Denjoy–Carleman theorem (Lemma DC).

Weak unique continuation then spreads the vanishing from a tangent ball to a neighbourhood of `0`.

## Work packages

The proof is split into packages with frozen interfaces, one file each in
`MazyaRefinedCauchy/Pkg/`. `MainA` and `MainB` derive the two theorems from the package statements
alone, and `Solution.lean` restates the theorems of `Challenge.lean` and proves them from `MainA`
and `MainB`. Every file is checked on its own, so packages can be proved in parallel.

| Package | File | Content | Uses | Status |
|---|---|---|---|---|
| Setup | `Setup.lean` | half-balls, the operator `ellOp`, `GoodCoeffs`, `HalfBallSolution` (output of the collar step) | | definitions |
| F1 | `Pkg/F1.lean` | splitting `Space n ≃ ℝⁿ × ℝ`; divergence theorem on `{t > η}`, up to `{t = 0}`, and on the whole space | | proved |
| F2 | `Pkg/F2.lean` | Lemma 2.1 of the note with a density `μ`: conjugation identity and pointwise Carleman identity | | proved |
| F3 | `Pkg/F3.lean` | Kolmogorov–Riesz precompactness in `L²` | | proved |
| F4 | `Pkg/F4.lean` | sup bound for harmonic functions from their `L²` norm | | proved |
| F5 | `Pkg/F5.lean` | regular nondecreasing majorant of an `h` with `r log(1/h(r)) → ∞` | | proved |
| F6 | `Pkg/F6.lean` | Carleman's quasianalyticity theorem (`Σ M_k^{-1/k} = ∞`) | | proved |
| G | `Pkg/G.lean` | shrinking a `HalfBallSolution`; rescaling a regular profile; super-exponential decay | F5 | proved |
| U | `Pkg/U.lean` | weak unique continuation (local Carleman estimate, touching-ball argument) | F1, F2 | proved |
| C | `Pkg/C.lean` | collar reduction to a flat boundary with conormal `e_d` (Lemma coords) | F1 | proved |
| R1 | `Pkg/R1.lean` | Lemma R1: flat Cauchy data imply `∫_{B_r⁺} v² = O(r^M)` for every `M` (blow-up) | F1, F3, F4, U, G | 2 sorry |
| R | `Pkg/R.lean` | Proposition R with Lemmas cyl and R2 (radial Carleman estimate) | F1, F2, F5, R1, G | 3 sorry |
| PL | `Pkg/PL.lean` | Proposition PL with Lemma inversion and Proposition carleman | F1, F2, G | 2 sorry |
| L | `Pkg/L.lean` | tangent ball, Kelvin transform, Lemma DC (partial Fourier transform) | F1, F4, F6 | 1 sorry |
| MainA | `MainA.lean` | Theorem I(a) from the package statements | all | assembled |
| MainB | `MainB.lean` | Theorem I(b) from the package statements | all | assembled |
| Solution | `Solution.lean` | the statements of `Challenge.lean`, proved from `MainA` and `MainB` | MainA, MainB | assembled |

Legend: **proved**: no `sorry` in the package or anything it uses (checked with `collectAxioms`:
only `propext`, `Classical.choice`, `Quot.sound`); **proved modulo X**: no `sorry` in the file, but
it uses a package that still has one; **assembled**: no `sorry` in the file, but it uses packages
still in progress; **k sorry**: the file compiles with `k` occurrences of `sorry`.

## Corrections to the package interfaces

The parallel work exposed three interface statements that were false as first written; each
was corrected, and the counterexamples are recorded next to the statements.

* `carleman_conj` (F2) lacked the symmetry of `B`. Without it the identity fails in every
  dimension `≥ 2` (`F2.not_carleman_conj_of_pos`); the note assumes `A` symmetric throughout.
* `HalfBallSolution.integral_sq_le_pow` (R1) and `HalfBallSolution.interior_decay` (R) now
  assume `0 < n`. For `n = 0` the flat piece is `{0}`, the Neumann hypothesis is vacuous, and
  `v x = x 0` is a counterexample. Both main theorems assume `0 < n` anyway.
