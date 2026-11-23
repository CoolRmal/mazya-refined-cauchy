# Maz'ya's refined Cauchy problem at a boundary point, in Lean

A Lean 4 / Mathlib formalization of two uniqueness theorems for elliptic equations whose
Cauchy data are small at a single boundary point. They concern Problem 5.3 in
V. Maz'ya, [*Seventy five (thousand) unsolved problems in analysis and partial differential
equations*](https://users.mai.liu.se/vlama82/pdf/Problems2018l_0312.pdf) (2018).

**Status: work in progress.** The statements in [`Challenge.lean`](Challenge.lean) are final
candidates; the proofs are being formalized. `Solution.lean` still contains `sorry`, so the
Comparator check in CI is expected to fail until the development is complete.

## The statements

Near the boundary point `0`, the domain is the part of the ball `B(0, ρ)` above the graph of a
smooth function `Γ` with `Γ(0) = 0`. The solution `u` is `C²` in the domain, and `u` and `∇u` are
continuous up to the graph. The Dirichlet data vanish to infinite order at `0`:
`|u(x)| ≤ C_N |x|^N` on the graph, for every `N`. Only the Neumann data are assumed small:
`|a∇u · n| ≤ h(|x|)` on the graph.

* **Theorem I(a)** (`MazyaRefinedCauchy.refined_cauchy_superexp`). For
  `L u = div(a∇u) + b·∇u + c u` with smooth, symmetric, uniformly elliptic `a` and continuous
  `b`, `c`: if `L u = 0` and `r log(1/h(r)) → ∞` as `r → 0⁺`, then `u = 0` near `0`.
* **Theorem I(b)** (`MazyaRefinedCauchy.refined_cauchy_laplace`). For harmonic `u`, in any
  dimension: if `∫₀ log h(r) dr = -∞` and `h` is regular (positive, nondecreasing, and
  `Λ(σ) = log(1/h(e^{-σ}))` superlinear, eventually convex, with `Λ' ≤ CΛ`), then `u = 0` near `0`.

Part (b) is the sufficiency half of the first question of Maz'ya's Problem 5.3 (smooth domains in
place of a half-space) for regular `h`.

### Differences from the informal theorem

The informal Theorem I allows `C^{3,1}` boundaries, `C^{2,1}` leading coefficients, bounded `b`, `c`,
weak solutions, and in part (b) any constant-coefficient operator `a^{ij}∂_{ij}`. The formal
statements assume smooth `Γ` and `a`, continuous `b` and `c`, classical (`C²`) solutions, and in
part (b) the Laplacian. These match the smooth setting of Maz'ya's problem.

## Building

```bash
lake exe cache get
lake build
```

Comparator (`lake comparator`) needs Linux and `bwrap`; CI runs it on every push via
[`scripts/verify-comparator.sh`](scripts/verify-comparator.sh). `scripts/check-defs-sync.py`
checks that `MazyaRefinedCauchy/Defs.lean` repeats the definitions of `Challenge.lean` verbatim.

## Registry

When the development is complete and Comparator passes, the project will be submitted to the
[Palomar registry](https://palomar-registry.org/) through https://submit.palomar-registry.org/.

## Licence

Apache-2.0, see [LICENSE](LICENSE).
