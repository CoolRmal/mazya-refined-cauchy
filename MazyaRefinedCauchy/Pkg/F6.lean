module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F6

The theorems stated in this file are the frozen contract of package F6 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F6: Carleman's quasianalyticity theorem -/

/-- **Denjoy–Carleman (Carleman's criterion).** A smooth function on `ℝ` whose derivatives are
bounded by `M k`, with `∑ M k ^ (-1/k) = ∞`, and which vanishes to infinite order at `0`, is
identically zero. -/
theorem denjoy_carleman (f : ℝ → ℂ) (M : ℕ → ℝ) (hf : ContDiff ℝ ∞ f) (hM : ∀ k, 0 < M k)
    (hbound : ∀ k x, ‖iteratedDeriv k f x‖ ≤ M k) (hzero : ∀ k, iteratedDeriv k f 0 = 0)
    (hdiv : ¬ Summable (fun k : ℕ => M k ^ (-(1 : ℝ) / k))) :
    ∀ x, f x = 0 := by
  sorry

end MazyaRefinedCauchy
