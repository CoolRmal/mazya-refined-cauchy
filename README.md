# Maz'ya's refined Cauchy problem at a boundary point, in Lean

A Lean 4 / Mathlib formalization of two uniqueness theorems for elliptic equations whose
Cauchy data are small at a single boundary point. They concern Problem 5.3 in
V. Maz'ya, [*Seventy five (thousand) unsolved problems in analysis and partial differential
equations*](https://users.mai.liu.se/vlama82/pdf/Problems2018l_0312.pdf) (2018).

**Status: complete.** Both theorems are proved. The development has no `sorry`, and both
theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. On every push,
CI runs Comparator, which checks that [`Solution.lean`](Solution.lean) proves exactly the
statements of [`Challenge.lean`](Challenge.lean) and replays the proofs through Lean's kernel and
the independent kernels NanoDa and con-ron. [`BLUEPRINT.md`](BLUEPRINT.md) describes how the proof
is organized.

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

For `h` in this regularity class, which has not been compared with the unspecified regularity
conditions of Maz'ya and Havin, part (b) is, in local form, the sufficiency half of the first
question of Maz'ya's Problem 5.3: smooth domains in place of the half-space, for the Laplacian.
Part (a) bounds the conormal derivative and needs `r log(1/h(r)) → ∞`, so it does not answer
Maz'ya's second question.

### Differences from the informal theorem

The informal Theorem I allows `C^{3,1}` boundaries, `C^{2,1}` leading coefficients, bounded `b`, `c`,
weak solutions, and in part (b) any constant-coefficient operator `a^{ij}∂_{ij}`. The formal
statements assume smooth `Γ` and `a`, continuous `b` and `c`, classical (`C²`) solutions, and in
part (b) the Laplacian. For smooth coefficients, which is Maz'ya's setting, weak solutions are
classical, so nothing is lost there. The log-integral in (b) is stated on `(0, ρ/2)`.

## Provenance

Theorem I and its informal proof were first written in 2026 in an unpublished note by the
maintainer, with AI assistance. This formalization was produced by Claude Code agents
(`claude-opus-5-5`) working from that proof; the statements in `Challenge.lean` were audited by
independent AI reviewers, and the maintainer's review is pending. The formal proof follows the
route of the note, with classical `C²` solutions throughout and no Sobolev spaces;
[`BLUEPRINT.md`](BLUEPRINT.md) describes its organization and its departures from the note. Whether Theorem I is new
has not been established by a systematic literature search, and no novelty is claimed here.

The formalization does not build on an earlier formalization of these theorems. A few general
lemmas were adapted from three Apache-2.0 Lean libraries, PDEAtlas, Tau Ceti and
quasianalytic-lean; [`NOTICE`](NOTICE) lists them.

## Building

```bash
lake exe cache get
lake build
```

Comparator (`lake comparator`) needs Linux and `bwrap`; CI runs it on every push via
[`scripts/verify-comparator.sh`](scripts/verify-comparator.sh). `scripts/check-defs-sync.py`
checks that `MazyaRefinedCauchy/Defs.lean` repeats the definitions of `Challenge.lean` verbatim.

## Registry

The project is to be submitted to the [Palomar registry](https://palomar-registry.org/) through
https://submit.palomar-registry.org/.

## Licence

Apache-2.0, see [LICENSE](LICENSE).
