module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F3

The theorems stated in this file are the frozen contract of package F3 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

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

end MazyaRefinedCauchy
