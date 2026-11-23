# Blueprint

This file is the plan and progress log of the formalization. Each module lists its main
declarations, what they depend on, and their status: **stated** (compiles with `sorry`),
**proved** (no `sorry`), or **planned**.

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

## Modules

### Foundations
| Module | Content | Status |
|---|---|---|
| `Defs` | Statement definitions, identical to `Challenge.lean` | proved |
| `Foundations/Coordinates` | splitting `Space n ≃ ℝⁿ × ℝ`, measure preservation, norms | planned |
| `Foundations/Calculus` | divergence product rules, chain rules, derivatives of `‖x‖`, `log‖x‖`, `x/‖x‖²` | planned |
| `Foundations/HalfSpaceIBP` | `∫_{t>η} div F = -∫_{t=η} F_d` for compactly supported `C¹` fields; whole-space version | planned |
| `Foundations/CarlemanIdentity` | Lemma 2.1 of the note with a density `μ`: conjugation identity and its integrated form on `{t > η}` | planned |
| `Foundations/Compactness` | Kolmogorov–Riesz type precompactness in `L²` from uniform translation bounds | planned |
| `Foundations/RadialMollifier` | harmonic functions equal their radial mollifications; sup bound from `L²` | planned |

### Unique continuation
| Module | Content | Status |
|---|---|---|
| `UCP/LocalCarleman` | interior Carleman estimate with weight `e^{τ e^{μψ}}`, `∇ψ ≠ 0` | planned |
| `UCP/WeakUCP` | a `C²` solution of a smooth elliptic equation vanishing on an open subset of a connected open set vanishes | planned |

### Step 1: refined data
| Module | Content | Status |
|---|---|---|
| `Collar/Map` | conormal collar `F(x', t) = γ(x') + t a(γ(x')) ν(x')`, local diffeomorphism | planned |
| `Collar/Transform` | the transformed equation; `Ã e_d ∥ e_d` on `{t = 0}`; boundary data; normalization `Ã(0) = I`; globalized coefficients | planned |
| `Refined/Setup` | `HalfBallSolution`: the interface produced by the collar step | planned |
| `Refined/Caccioppoli` | Caccioppoli inequality up to the flat boundary | planned |
| `Refined/InfiniteOrder` | Lemma R1: flat Cauchy data ⇒ `∫_{B_r⁺} v² = O(r^M)` for all `M` | planned |
| `Refined/RadialCarleman` | Lemma R2 in `X` coordinates | planned |
| `Refined/InteriorDecay` | Proposition R | planned |
| `Refined/Majorant` | regular nondecreasing majorant of an `h` with `r log(1/h) → ∞` | planned |

### Step 2
| Module | Content | Status |
|---|---|---|
| `Inversion/Transform` | the equation after `X ↦ X/|X|²` on a tangent ball; coefficient bounds | planned |
| `Inversion/HalfSpaceCarleman` | Proposition carleman (weight `y_d - C₀ log y_d`) | planned |
| `Inversion/PhragmenLindelof` | Proposition PL | planned |
| `Laplace/TangentBall` | a tangent ball at `0` lies in the domain | planned |
| `Laplace/Kelvin` | the Kelvin transform of a harmonic function is harmonic | planned |
| `Laplace/PartialFourier` | Fourier transform in the tangential variables; the ODE `∂_t² V = 4π²|ξ|² V` | planned |
| `Laplace/DenjoyCarleman` | Carleman's quasianalyticity theorem (`Σ M_k^{-1/k} = ∞`) | planned |
| `Laplace/LemmaDC` | Lemma DC | planned |

### Main theorems
| Module | Content | Status |
|---|---|---|
| `MainA` | Theorem I(a) | planned |
| `MainB` | Theorem I(b) | planned |
| `Solution.lean` | the advertised statements, proved from `MainA`, `MainB` | stated |
