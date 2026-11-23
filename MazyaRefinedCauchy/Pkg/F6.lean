module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F6

The theorems stated in this file are the frozen contract of package F6 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## Proof outline (Carleman's theorem)

The proof is a real-variable one: Bang's argument in a discrete-chain form, applied to the
*log-convex minorant* of the bound sequence `M`, followed by Carleman's inequality.

* The Bang step (`bang_step`) and the chain (`chain`) are adapted from quasianalytic-lean,
  `QuasianalyticLean/DenjoyCarleman/DC12.lean` and `DC3.lean` (Apache-2.0), generalised so that
  the a priori bound `|f^{(q)}| ≤ M q` is only used at the vertices `q` of the log-convex
  minorant of `M`, and to vector-valued functions.
* If `M k ^ (1/k)` does not tend to infinity, Taylor's formula gives `f = 0` directly
  (`forward_caseB`).
* Otherwise the lower convex hull of the points `(k, log M k)` is constructed greedily
  (`nx`, `vtx`, `hullW`), the chain runs along it, and Carleman's inequality
  `∑ (a₁ ⋯ aₖ)^{1/k} ≤ e ∑ aₖ` (`carleman_ineq`) shows that `∑ hullW k / hullW (k+1) = ∞`.
* Negative `x` are handled by reflection.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F6: Carleman's quasianalyticity theorem -/

namespace DenjoyCarlemanF6

open Set Real
open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Iterated derivatives and Taylor's formula -/

/-- Adapted from quasianalytic-lean, `QuasianalyticLean/DenjoyCarleman/DC12.lean`. -/
lemma iter_iter (f : ℝ → E) (m k : ℕ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

lemma contDiff_iter {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  rw [iteratedDeriv_eq_iterate]; exact hf.iterate_deriv k

/-- Taylor's formula with a Lagrange-type remainder bound, for a globally smooth function. -/
lemma taylor_bound {g : ℝ → E} (hg : ContDiff ℝ ∞ g) {x h : ℝ} (hh : 0 ≤ h) (n : ℕ) {C : ℝ}
    (hC : ∀ y ∈ Icc x (x + h), ‖iteratedDeriv (n + 1) g y‖ ≤ C) :
    ‖g (x + h) - ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) • iteratedDeriv k g x‖
      ≤ C * h ^ (n + 1) / n ! := by
  rcases hh.eq_or_lt with h0 | hpos
  · subst h0
    simp [Finset.sum_range_succ']
  have hderivs : ∀ y ∈ Icc x (x + h), ∀ k : ℕ,
      iteratedDerivWithin k g (Icc x (x + h)) y = iteratedDeriv k g y := fun y hy k =>
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
      (hg.contDiffAt.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))) hy
  have hrem := taylor_mean_remainder_bound (f := g) (n := n) (C := C) (x := x + h) (a := x)
    (b := x + h) (hg.contDiffOn.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤)))
    (right_mem_Icc.2 (by linarith)) (fun y hy => by rw [hderivs y hy]; exact hC y hy)
  rw [taylor_within_apply, show x + h - x = h by ring] at hrem
  have hsum : ∑ k ∈ Finset.range (n + 1),
      ((k ! : ℝ)⁻¹ * h ^ k) • iteratedDerivWithin k g (Icc x (x + h)) x
      = ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) • iteratedDeriv k g x := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hderivs x (left_mem_Icc.2 (by linarith)) k]
  rw [hsum] at hrem
  exact hrem

/-! ### Bang's step (generalised) -/

/-- **Bang's step.** Adapted from quasianalytic-lean, `DenjoyCarleman/DC12.lean` (`DC2_bang_step`):
here the weight `W` is only assumed to satisfy `W (i+k) ≤ W i * A ^ k` below the level `q`, and the
a priori bound on `f` is used only at the level `q`. -/
theorem bang_step {f : ℝ → E} (hf : ContDiff ℝ ∞ f) {W : ℕ → ℝ} (hW : ∀ k, 0 < W k)
    {A : ℝ} (hA : 0 < A) {q : ℕ}
    (h1 : ∀ i k, i + k ≤ q → W (i + k) ≤ W i * A ^ k)
    (h2 : ∀ y, ‖iteratedDeriv q f y‖ ≤ W q)
    {x h β : ℝ} (hh : 0 ≤ h) (hβ : Real.exp (-(q : ℝ)) ≤ β)
    (hbx : ∀ i < q, ‖iteratedDeriv i f x‖ ≤ β * Real.exp i * W i) :
    ∀ i < q, ‖iteratedDeriv i f (x + h)‖ ≤
      β * Real.exp (2 * Real.exp 1 * h * A) * Real.exp i * W i := by
  intro i hiq
  set t := Real.exp 1 * A * h with ht
  have ht0 : 0 ≤ t := by positivity
  have hβpos : 0 < β := lt_of_lt_of_le (Real.exp_pos _) hβ
  have hWi := hW i
  set P := β * Real.exp i * W i with hP
  have hPpos : 0 < P := by positivity
  have hgoal : β * Real.exp (2 * Real.exp 1 * h * A) * Real.exp i * W i
      = P * Real.exp t * Real.exp t := by
    rw [show 2 * Real.exp 1 * h * A = t + t by rw [ht]; ring, Real.exp_add, hP]
    ring
  rw [hgoal]
  obtain ⟨n, rfl⟩ : ∃ n, q = i + n + 1 := ⟨q - i - 1, by omega⟩
  set g := iteratedDeriv i f with hg
  have hgs : ContDiff ℝ ∞ g := contDiff_iter hf i
  have hrem := taylor_bound hgs (x := x) hh n (C := W (i + n + 1)) (fun y _ => by
    rw [hg, iter_iter, show n + 1 + i = i + n + 1 by omega]; exact h2 y)
  -- bound the Taylor polynomial
  have hT : ‖∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) • iteratedDeriv k g x‖
      ≤ P * Real.exp t := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range (n + 1), ‖((k ! : ℝ)⁻¹ * h ^ k) • iteratedDeriv k g x‖
        ≤ ∑ k ∈ Finset.range (n + 1), P * (t ^ k / k !) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_range] at hk
          rw [norm_smul, Real.norm_of_nonneg (by positivity), hg, iter_iter, add_comm k i]
          have hD := hbx (k + i) (by omega)
          have hDC := h1 i k (by omega)
          have hexp : Real.exp ((k + i : ℕ) : ℝ) = Real.exp i * Real.exp 1 ^ k := by
            rw [Real.exp_one_pow, ← Real.exp_add]; push_cast; ring_nf
          rw [hexp, add_comm k i] at hD
          calc (k ! : ℝ)⁻¹ * h ^ k * ‖iteratedDeriv (i + k) f x‖
              ≤ (k ! : ℝ)⁻¹ * h ^ k * (β * (Real.exp i * Real.exp 1 ^ k) * W (i + k)) := by
                gcongr
            _ ≤ (k ! : ℝ)⁻¹ * h ^ k * (β * (Real.exp i * Real.exp 1 ^ k) * (W i * A ^ k)) := by
                gcongr
            _ = P * (t ^ k / k !) := by
                rw [hP, ht]; field_simp; ring
      _ = P * ∑ k ∈ Finset.range (n + 1), t ^ k / k ! := by rw [Finset.mul_sum]
      _ ≤ P * Real.exp t := by gcongr; exact Real.sum_le_exp_of_nonneg ht0 _
  -- bound the remainder
  have hR : W (i + n + 1) * h ^ (n + 1) / n ! ≤ P * (t * Real.exp t) := by
    have hDC := h1 i (n + 1) (by omega)
    rw [show i + (n + 1) = i + n + 1 by omega] at hDC
    have hβq : 1 ≤ β * Real.exp ((i + n + 1 : ℕ) : ℝ) := by
      calc (1 : ℝ) = Real.exp (-((i + n + 1 : ℕ) : ℝ)) * Real.exp ((i + n + 1 : ℕ) : ℝ) := by
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        _ ≤ β * Real.exp ((i + n + 1 : ℕ) : ℝ) := by gcongr
    have hexp : Real.exp ((i + n + 1 : ℕ) : ℝ) = Real.exp i * Real.exp 1 ^ (n + 1) := by
      rw [Real.exp_one_pow, ← Real.exp_add]; push_cast; ring_nf
    rw [hexp] at hβq
    have hpow := Real.pow_div_factorial_le_exp _ ht0 n
    calc W (i + n + 1) * h ^ (n + 1) / n ! ≤ W i * A ^ (n + 1) * h ^ (n + 1) / n ! := by
          gcongr
      _ ≤ (β * (Real.exp i * Real.exp 1 ^ (n + 1))) *
            (W i * A ^ (n + 1) * h ^ (n + 1) / n !) := by
          have : 0 ≤ W i * A ^ (n + 1) * h ^ (n + 1) / n ! := by positivity
          nlinarith
      _ = P * (t * (t ^ n / n !)) := by rw [hP, ht]; field_simp; ring
      _ ≤ P * (t * Real.exp t) := by gcongr
  have htri : ‖g (x + h)‖ ≤
      ‖∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) • iteratedDeriv k g x‖
      + ‖g (x + h) - ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) • iteratedDeriv k g x‖ := by
    have := norm_add_le (∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) • iteratedDeriv k g x)
      (g (x + h) - ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) • iteratedDeriv k g x)
    simpa using this
  have h1t : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  calc ‖g (x + h)‖ ≤ P * Real.exp t + P * (t * Real.exp t) := by linarith
    _ = P * Real.exp t * (1 + t) := by ring
    _ ≤ P * Real.exp t * Real.exp t := by gcongr

/-! ### The chain -/

/-- **The chain.** Adapted from quasianalytic-lean, `DenjoyCarleman/DC3.lean` (`DC3_chain`). The
step from level `j + 1` to level `j` uses Bang's step at the level `Q j ≥ j + 1` (a vertex of the
log-convex minorant), where the a priori bound `‖f^{(Q j)}‖ ≤ W (Q j)` is available. -/
theorem chain {f : ℝ → E} (hf : ContDiff ℝ ∞ f) {W ρ : ℕ → ℝ} (hW : ∀ k, 0 < W k)
    (hρ : ∀ k, 0 < ρ k) (hWρ : ∀ k, W (k + 1) = W k * ρ k)
    {Q : ℕ → ℕ} (hQ1 : ∀ j, j + 1 ≤ Q j) (hQmono : ∀ j, Q j ≤ Q (j + 1))
    (hρle : ∀ j k, k < Q j → ρ k ≤ ρ j)
    (hQb : ∀ j y, ‖iteratedDeriv (Q j) f y‖ ≤ W (Q j))
    {x₀ : ℝ} (hflat : ∀ k, iteratedDeriv k f x₀ = 0) {L N : ℕ} (hLN : L ≤ N) :
    ∀ x, x₀ ≤ x → x ≤ x₀ + ∑ j ∈ Finset.Ico L N, (2 * Real.exp 1 * ρ j)⁻¹ →
      ∀ i < Q L, ‖iteratedDeriv i f x‖ ≤ Real.exp (-(L : ℝ)) * Real.exp i * W i := by
  set g : ℕ → ℝ := fun j => (2 * Real.exp 1 * ρ j)⁻¹ with hg
  -- the log-convexity bound below the level `Q j`
  have hpow : ∀ j i k, i + k ≤ Q j → W (i + k) ≤ W i * ρ j ^ k := by
    intro j i k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hik
      have ih := ih (by omega)
      have hr := hρle j (i + k) (by omega)
      have hWi := hW i
      have hρj := hρ j
      calc W (i + (k + 1)) = W (i + k) * ρ (i + k) := by rw [← add_assoc, hWρ]
        _ ≤ (W i * ρ j ^ k) * ρ j := mul_le_mul ih hr (hρ _).le (by positivity)
        _ = W i * ρ j ^ (k + 1) := by ring
  have key : ∀ k j : ℕ, j + k = N → ∀ x : ℝ, x₀ ≤ x →
      x ≤ x₀ + ∑ m ∈ Finset.Ico j N, g m →
      ∀ i < Q j, ‖iteratedDeriv i f x‖ ≤ Real.exp (-(j : ℝ)) * Real.exp i * W i := by
    intro k
    induction k with
    | zero =>
      intro j hj x hx1 hx3 i _
      simp only [add_zero] at hj
      subst hj
      simp only [Finset.Ico_self, Finset.sum_empty, add_zero] at hx3
      have : x = x₀ := le_antisymm hx3 hx1
      subst this
      rw [hflat, norm_zero]
      have := hW i
      positivity
    | succ k ih =>
      intro j hj x hx1 hx3 i hi
      have hjN : j < N := by omega
      have ih' := ih (j + 1) (by omega)
      rw [Finset.sum_eq_sum_Ico_succ_bot hjN] at hx3
      set S := ∑ m ∈ Finset.Ico (j + 1) N, g m
      have hexp : Real.exp (-((j + 1 : ℕ) : ℝ)) ≤ Real.exp (-(j : ℝ)) := by
        apply Real.exp_le_exp.mpr; push_cast; linarith
      have hWi := hW i
      have hiQ : i < Q (j + 1) := lt_of_lt_of_le hi (hQmono j)
      by_cases hc : x ≤ x₀ + S
      · calc ‖iteratedDeriv i f x‖ ≤ Real.exp (-((j + 1 : ℕ) : ℝ)) * Real.exp i * W i :=
              ih' x hx1 hc i hiQ
          _ ≤ Real.exp (-(j : ℝ)) * Real.exp i * W i := by gcongr
      · push Not at hc
        have hS0 : 0 ≤ S := Finset.sum_nonneg (fun m _ => by
          have := hρ m; simp only [hg]; positivity)
        set x' := x₀ + S with hx'
        have hbx' := ih' x' (by linarith) le_rfl
        have hρj := hρ j
        have hβ : Real.exp (-((Q j : ℕ) : ℝ)) ≤ Real.exp (-((j + 1 : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have h' : ((j + 1 : ℕ) : ℝ) ≤ (Q j : ℝ) := by exact_mod_cast hQ1 j
          linarith
        have h2 := bang_step hf hW hρj (q := Q j) (hpow j) (hQb j) (x := x') (h := x - x')
          (β := Real.exp (-((j + 1 : ℕ) : ℝ))) (by linarith) hβ
          (fun i' hi' => hbx' i' (lt_of_lt_of_le hi' (hQmono j))) i hi
        rw [show x' + (x - x') = x by ring] at h2
        have hle : 2 * Real.exp 1 * (x - x') * ρ j ≤ 1 := by
          have hpos : 0 < 2 * Real.exp 1 * ρ j := by positivity
          have : x - x' ≤ g j := by linarith
          simp only [hg] at this
          calc 2 * Real.exp 1 * (x - x') * ρ j
              = (x - x') * (2 * Real.exp 1 * ρ j) := by ring
            _ ≤ (2 * Real.exp 1 * ρ j)⁻¹ * (2 * Real.exp 1 * ρ j) := by gcongr
            _ = 1 := inv_mul_cancel₀ hpos.ne'
        calc ‖iteratedDeriv i f x‖
            ≤ Real.exp (-((j + 1 : ℕ) : ℝ)) *
                Real.exp (2 * Real.exp 1 * (x - x') * ρ j) * Real.exp i * W i := h2
          _ ≤ Real.exp (-((j + 1 : ℕ) : ℝ)) * Real.exp 1 * Real.exp i * W i := by
              gcongr
          _ = Real.exp (-(j : ℝ)) * Real.exp i * W i := by
              rw [← Real.exp_add]; congr 3; push_cast; ring
  intro x hx1 hx3 i hi
  exact key (N - L) L (by omega) x hx1 hx3 i hi

/-- Forward uniqueness, given the data of a log-convex weight along which the chain runs.
Adapted from quasianalytic-lean, `QuasianalyticLean/DenjoyCarleman/DC45.lean` (`DC4_forward`,
`exists_chain_long`). -/
theorem forward_of_data {f : ℝ → E} (hf : ContDiff ℝ ∞ f) {W ρ : ℕ → ℝ} (hW : ∀ k, 0 < W k)
    (hρ : ∀ k, 0 < ρ k) (hWρ : ∀ k, W (k + 1) = W k * ρ k)
    {Q : ℕ → ℕ} (hQ1 : ∀ j, j + 1 ≤ Q j) (hQmono : ∀ j, Q j ≤ Q (j + 1))
    (hρle : ∀ j k, k < Q j → ρ k ≤ ρ j)
    (hQb : ∀ j y, ‖iteratedDeriv (Q j) f y‖ ≤ W (Q j))
    (hdiv : ¬ Summable (fun k => (ρ k)⁻¹))
    {x₀ : ℝ} (hflat : ∀ k, iteratedDeriv k f x₀ = 0) :
    ∀ x, x₀ ≤ x → f x = 0 := by
  intro x hx
  have hnn : ∀ k, 0 ≤ (ρ k)⁻¹ := fun k => (inv_pos.2 (hρ k)).le
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).1 hdiv
  have hL : ∀ L : ℕ, ‖f x‖ ≤ Real.exp (-(L : ℝ)) * W 0 := by
    intro L
    have ht2 : Tendsto (fun N : ℕ => (2 * Real.exp 1)⁻¹ * (∑ k ∈ Finset.range N, (ρ k)⁻¹ -
        ∑ k ∈ Finset.range L, (ρ k)⁻¹)) atTop atTop :=
      (tendsto_atTop_add_const_right _ _ ht).const_mul_atTop (by positivity)
    obtain ⟨N, hN⟩ := ((ht2.eventually_ge_atTop (x - x₀)).and (eventually_ge_atTop L)).exists
    have hsum : ∑ j ∈ Finset.Ico L N, (2 * Real.exp 1 * ρ j)⁻¹ =
        (2 * Real.exp 1)⁻¹ * (∑ k ∈ Finset.range N, (ρ k)⁻¹ -
          ∑ k ∈ Finset.range L, (ρ k)⁻¹) := by
      rw [← Finset.sum_Ico_eq_sub _ hN.2, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_inv]
    have := chain hf hW hρ hWρ hQ1 hQmono hρle hQb hflat hN.2 x hx
      (by rw [hsum]; linarith [hN.1]) 0 (by have := hQ1 L; omega)
    simpa [iteratedDeriv_zero] using this
  have hlim : Tendsto (fun L : ℕ => Real.exp (-(L : ℝ)) * W 0) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).mul_const (W 0)
    simpa [Function.comp_def] using this
  have h0 : ‖f x‖ ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hL)
  exact norm_le_zero_iff.1 h0

/-! ### Carleman's inequality -/

/-- The weights `c l = (l+2)^(l+1) / (l+1)^l` used in the proof of Carleman's inequality. -/
noncomputable def carC (l : ℕ) : ℝ := ((l : ℝ) + 2) ^ (l + 1) / ((l : ℝ) + 1) ^ l

lemma carC_pos (l : ℕ) : 0 < carC l := by unfold carC; positivity

lemma carC_prod (n : ℕ) : ∏ l ∈ Finset.range n, carC l = ((n : ℝ) + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, carC]
    push_cast
    field_simp
    ring

lemma carC_div_le (l : ℕ) : carC l / ((l : ℝ) + 1) ≤ Real.exp 1 := by
  have h : carC l / ((l : ℝ) + 1) = (1 + 1 / ((l : ℝ) + 1)) ^ (l + 1) := by
    have hl : (0 : ℝ) < (l : ℝ) + 1 := by positivity
    rw [show (1 + 1 / ((l : ℝ) + 1)) = ((l : ℝ) + 2) / ((l : ℝ) + 1) by field_simp; ring, div_pow]
    unfold carC
    rw [div_div, ← pow_succ]
  rw [h]
  calc (1 + 1 / ((l : ℝ) + 1)) ^ (l + 1) ≤ (Real.exp (1 / ((l : ℝ) + 1))) ^ (l + 1) := by
        gcongr
        linarith [Real.add_one_le_exp (1 / ((l : ℝ) + 1))]
    _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp

/-- **Carleman's inequality** `∑_{k ≤ N} (a₀ ⋯ aₖ)^{1/(k+1)} ≤ e ∑_{k ≤ N} aₖ`. -/
theorem carleman_ineq (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (N : ℕ) :
    ∑ k ∈ Finset.range N, (∏ l ∈ Finset.range (k + 1), a l) ^ ((1 : ℝ) / (k + 1))
      ≤ Real.exp 1 * ∑ k ∈ Finset.range N, a k := by
  have hbnn : ∀ l, 0 ≤ a l * carC l := fun l => mul_nonneg (ha l) (carC_pos l).le
  -- termwise bound, from AM-GM
  have hterm : ∀ k, (∏ l ∈ Finset.range (k + 1), a l) ^ ((1 : ℝ) / (k + 1))
      ≤ (∑ l ∈ Finset.range (k + 1), a l * carC l) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    intro k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hamgm := Real.geom_mean_le_arith_mean_weighted (Finset.range (k + 1))
      (fun _ => (1 : ℝ) / ((k : ℝ) + 1)) (fun l => a l * carC l) (fun _ _ => by positivity)
      (by simp [Finset.sum_const, Finset.card_range]; field_simp) (fun l _ => hbnn l)
    rw [Real.finsetProd_rpow _ _ (fun l _ => hbnn l), ← Finset.mul_sum,
      Finset.prod_mul_distrib, carC_prod,
      Real.mul_rpow (Finset.prod_nonneg (fun l _ => ha l)) (by positivity)] at hamgm
    have hroot : (((((k + 1 : ℕ) : ℝ) + 1) ^ (k + 1)) ^ ((1 : ℝ) / ((k : ℝ) + 1)))
        = (k : ℝ) + 2 := by
      rw [show ((1 : ℝ) / ((k : ℝ) + 1)) = ((k + 1 : ℕ) : ℝ)⁻¹ by push_cast; ring,
        Real.pow_rpow_inv_natCast (by positivity) (by omega)]
      push_cast; ring
    rw [hroot] at hamgm
    rw [le_div_iff₀ (by positivity)]
    calc (∏ l ∈ Finset.range (k + 1), a l) ^ ((1 : ℝ) / (k + 1)) * (((k : ℝ) + 1) * ((k : ℝ) + 2))
        = ((∏ l ∈ Finset.range (k + 1), a l) ^ ((1 : ℝ) / (k + 1)) * ((k : ℝ) + 2))
            * ((k : ℝ) + 1) := by ring
      _ ≤ (1 / ((k : ℝ) + 1) * ∑ l ∈ Finset.range (k + 1), a l * carC l) * ((k : ℝ) + 1) := by
          gcongr
      _ = ∑ l ∈ Finset.range (k + 1), a l * carC l := by field_simp
  -- telescoping identity
  have htel : ∀ N, ∑ k ∈ Finset.range N,
      (∑ l ∈ Finset.range (k + 1), a l * carC l) / (((k : ℝ) + 1) * ((k : ℝ) + 2))
      = ∑ l ∈ Finset.range N, a l * carC l / ((l : ℝ) + 1)
        - (∑ l ∈ Finset.range N, a l * carC l) / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Finset.sum_range_succ]
      push_cast
      field_simp
      ring
  calc ∑ k ∈ Finset.range N, (∏ l ∈ Finset.range (k + 1), a l) ^ ((1 : ℝ) / (k + 1))
      ≤ ∑ k ∈ Finset.range N,
          (∑ l ∈ Finset.range (k + 1), a l * carC l) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = ∑ l ∈ Finset.range N, a l * carC l / ((l : ℝ) + 1)
          - (∑ l ∈ Finset.range N, a l * carC l) / ((N : ℝ) + 1) := htel N
    _ ≤ ∑ l ∈ Finset.range N, a l * carC l / ((l : ℝ) + 1) := by
        have : 0 ≤ (∑ l ∈ Finset.range N, a l * carC l) / ((N : ℝ) + 1) :=
          div_nonneg (Finset.sum_nonneg (fun l _ => hbnn l)) (by positivity)
        linarith
    _ ≤ ∑ l ∈ Finset.range N, Real.exp 1 * a l := by
        apply Finset.sum_le_sum
        intro l _
        calc a l * carC l / ((l : ℝ) + 1) = a l * (carC l / ((l : ℝ) + 1)) := by ring
          _ ≤ a l * Real.exp 1 := mul_le_mul_of_nonneg_left (carC_div_le l) (ha l)
          _ = Real.exp 1 * a l := by ring
    _ = Real.exp 1 * ∑ k ∈ Finset.range N, a k := by rw [Finset.mul_sum]

/-! ### The log-convex minorant (greedy lower convex hull of `k ↦ log M k`) -/

/-- Slope of `log M` between the indices `p` and `j`. -/
noncomputable def slp (M : ℕ → ℝ) (p j : ℕ) : ℝ :=
  (Real.log (M j) - Real.log (M p)) / ((j : ℝ) - p)

open Classical in
/-- The next vertex of the lower convex hull after `p` (a minimiser of the slope from `p`). -/
noncomputable def nx (M : ℕ → ℝ) (p : ℕ) : ℕ :=
  if h : ∃ j, p < j ∧ ∀ j', p < j' → slp M p j ≤ slp M p j' then Classical.choose h else p + 1

/-- The slope of the hull edge starting at `p`. -/
noncomputable def sg (M : ℕ → ℝ) (p : ℕ) : ℝ := slp M p (nx M p)

/-- `vtx M k` is the hull vertex at or before `k` whose edge contains `(k, k+1)`. -/
noncomputable def vtx (M : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if k + 1 < nx M (vtx M k) then vtx M k else nx M (vtx M k)

/-- The log-convex minorant. -/
noncomputable def hullW (M : ℕ → ℝ) (k : ℕ) : ℝ :=
  M (vtx M k) * Real.exp (sg M (vtx M k) * ((k : ℝ) - vtx M k))

/-- The ratio `hullW (k+1) / hullW k`. -/
noncomputable def hullρ (M : ℕ → ℝ) (k : ℕ) : ℝ := Real.exp (sg M (vtx M k))

/-- The hull vertex `nx M (vtx M j) ≥ j + 1`: the right end of the hull edge containing
`(j, j + 1)`. -/
noncomputable def hullQ (M : ℕ → ℝ) (j : ℕ) : ℕ := nx M (vtx M j)

/-- Superlinear growth of `log M`, i.e. `M k ^ (1/k) → ∞`. -/
def Superlin (M : ℕ → ℝ) : Prop := ∀ R : ℝ, ∀ᶠ k : ℕ in atTop, R * k ≤ Real.log (M k)

variable {M : ℕ → ℝ}

lemma lt_nx (p : ℕ) : p < nx M p := by
  unfold nx; split_ifs with h
  · exact (Classical.choose_spec h).1
  · omega

lemma vtx_zero : vtx M 0 = 0 := rfl

lemma vtx_succ (k : ℕ) :
    vtx M (k + 1) = if k + 1 < nx M (vtx M k) then vtx M k else nx M (vtx M k) := rfl

lemma exists_min_slp (hA : Superlin M) (p : ℕ) :
    ∃ j, p < j ∧ ∀ j', p < j' → slp M p j ≤ slp M p j' := by
  have hev : ∀ᶠ j : ℕ in atTop, slp M p (p + 1) < slp M p j := by
    filter_upwards [hA (|slp M p (p + 1)| * ((p : ℝ) + 1) + |Real.log (M p)| + 1
      + |slp M p (p + 1)|), eventually_gt_atTop p] with j hj hjp
    have hjp' : (p : ℝ) < j := by exact_mod_cast hjp
    have h1 : (1 : ℝ) ≤ j := by
      have : 1 ≤ j := by omega
      exact_mod_cast this
    set c := slp M p (p + 1) with hc
    set ℓ := Real.log (M p) with hℓ
    conv_rhs => unfold slp
    rw [lt_div_iff₀ (by linarith)]
    have f1 : |c| * ((p : ℝ) + 1) * 1 ≤ |c| * ((p : ℝ) + 1) * j :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have f2 : |ℓ| * 1 ≤ |ℓ| * j := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have f3 : c * j ≤ |c| * j := mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    have f4 : -|c| * p ≤ c * p := mul_le_mul_of_nonneg_right (neg_abs_le c) (by positivity)
    have f5 : ℓ ≤ |ℓ| := le_abs_self ℓ
    have f6 : 0 ≤ |c| := abs_nonneg c
    nlinarith
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  obtain ⟨j, hjmem, hjmin⟩ := (Finset.Icc (p + 1) (max J (p + 1))).exists_min_image (slp M p)
    ⟨p + 1, by simp⟩
  rw [Finset.mem_Icc] at hjmem
  refine ⟨j, by omega, fun j' hj' => ?_⟩
  by_cases hj'J : j' ≤ max J (p + 1)
  · exact hjmin j' (Finset.mem_Icc.2 ⟨by omega, hj'J⟩)
  · have h1 := hJ j' (by omega)
    have h2 := hjmin (p + 1) (Finset.mem_Icc.2 ⟨le_rfl, le_max_right _ _⟩)
    linarith

lemma nx_min (hA : Superlin M) (p : ℕ) : ∀ j, p < j → sg M p ≤ slp M p j := by
  intro j hj
  have h := exists_min_slp hA p
  unfold sg nx
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).2 j hj

lemma log_nx (p : ℕ) :
    Real.log (M (nx M p)) = Real.log (M p) + sg M p * ((nx M p : ℝ) - p) := by
  have hlt : (p : ℝ) < nx M p := by exact_mod_cast lt_nx p
  have hne : (nx M p : ℝ) - p ≠ 0 := by linarith
  unfold sg slp
  field_simp
  ring

lemma sg_mono (hA : Superlin M) (p : ℕ) : sg M p ≤ sg M (nx M p) := by
  have hq : p < nx M p := lt_nx p
  have hj := lt_nx (M := M) (nx M p)
  have h1 := nx_min hA p (nx M (nx M p)) (by omega)
  have hlog := log_nx (M := M) p
  show sg M p ≤ slp M (nx M p) (nx M (nx M p))
  unfold slp at h1 ⊢
  have hpq : (p : ℝ) < nx M p := by exact_mod_cast hq
  have hqr : (nx M p : ℝ) < nx M (nx M p) := by exact_mod_cast hj
  rw [le_div_iff₀ (by linarith)] at h1 ⊢
  rw [hlog]
  nlinarith

lemma vtx_spec (k : ℕ) : vtx M k ≤ k ∧ k < nx M (vtx M k) := by
  induction k with
  | zero => exact ⟨le_refl 0, lt_nx 0⟩
  | succ k ih =>
    by_cases h : k + 1 < nx M (vtx M k)
    · rw [vtx_succ, ite_eq_left h]
      exact ⟨by omega, h⟩
    · rw [vtx_succ, ite_eq_right h]
      have e : nx M (vtx M k) = k + 1 := by omega
      rw [e]
      exact ⟨le_refl _, lt_nx _⟩

lemma vtx_const {j k : ℕ} (hjk : j ≤ k) (hk : k < nx M (vtx M j)) : vtx M k = vtx M j := by
  revert hk
  induction k, hjk using Nat.le_induction with
  | base => intro _; rfl
  | succ k hjk ih =>
    intro hk
    have ih := ih (by omega)
    rw [vtx_succ, ih, ite_eq_left hk]

lemma vtx_hullQ (j : ℕ) : vtx M (hullQ M j) = hullQ M j := by
  unfold hullQ
  obtain ⟨h1, h2⟩ := vtx_spec (M := M) j
  obtain ⟨m, hm⟩ : ∃ m, nx M (vtx M j) = m + 1 := ⟨nx M (vtx M j) - 1, by omega⟩
  have hjm : j ≤ m := by omega
  have hc := vtx_const (M := M) hjm (by omega)
  rw [hm, vtx_succ, hc, hm]
  simp

lemma hullW_pos (hM : ∀ k, 0 < M k) (k : ℕ) : 0 < hullW M k := by
  unfold hullW; have := hM (vtx M k); positivity

lemma hullρ_pos (k : ℕ) : 0 < hullρ M k := Real.exp_pos _

lemma hullW_succ (hM : ∀ k, 0 < M k) (k : ℕ) : hullW M (k + 1) = hullW M k * hullρ M k := by
  unfold hullW hullρ
  by_cases h : k + 1 < nx M (vtx M k)
  · rw [vtx_succ, ite_eq_left h, mul_assoc, ← Real.exp_add]
    congr 2
    push_cast; ring
  · rw [vtx_succ, ite_eq_right h]
    have hk := vtx_spec (M := M) k
    have e' : nx M (vtx M k) = k + 1 := by omega
    have e : (nx M (vtx M k) : ℝ) = (k : ℝ) + 1 := by exact_mod_cast e'
    have hl := log_nx (M := M) (vtx M k)
    have hMnx : M (nx M (vtx M k)) =
        M (vtx M k) * Real.exp (sg M (vtx M k) * ((nx M (vtx M k) : ℝ) - vtx M k)) := by
      rw [← Real.exp_log (hM (nx M (vtx M k))), hl, Real.exp_add, Real.exp_log (hM _)]
    rw [hMnx, e]
    push_cast
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring

lemma hullW_le (hA : Superlin M) (hM : ∀ k, 0 < M k) (k : ℕ) : hullW M k ≤ M k := by
  unfold hullW
  have hk := (vtx_spec (M := M) k).1
  rcases hk.eq_or_lt with h | h
  · rw [h]; simp
  · have hmin := nx_min hA (vtx M k) k h
    unfold slp at hmin
    have hlt : ((vtx M k : ℕ) : ℝ) < k := by exact_mod_cast h
    rw [le_div_iff₀ (by linarith)] at hmin
    calc M (vtx M k) * Real.exp (sg M (vtx M k) * ((k : ℝ) - vtx M k))
        ≤ M (vtx M k) * Real.exp (Real.log (M k) - Real.log (M (vtx M k))) := by
          gcongr
          exact (hM _).le
      _ = M k := by
          rw [Real.exp_sub, Real.exp_log (hM _), Real.exp_log (hM _)]
          field_simp [(hM (vtx M k)).ne']

lemma hullρ_mono (hA : Superlin M) : Monotone (hullρ M) := by
  apply monotone_nat_of_le_succ
  intro k
  unfold hullρ
  apply Real.exp_le_exp.2
  by_cases h : k + 1 < nx M (vtx M k)
  · rw [vtx_succ, ite_eq_left h]
  · rw [vtx_succ, ite_eq_right h]; exact sg_mono hA _

lemma hullQ_ge (j : ℕ) : j + 1 ≤ hullQ M j := (vtx_spec (M := M) j).2

lemma hullQ_mono (j : ℕ) : hullQ M j ≤ hullQ M (j + 1) := by
  unfold hullQ
  by_cases h : j + 1 < nx M (vtx M j)
  · rw [vtx_succ, ite_eq_left h]
  · rw [vtx_succ, ite_eq_right h]; exact (lt_nx _).le

lemma hullρ_le_of_lt_hullQ (hA : Superlin M) (j k : ℕ) (hk : k < hullQ M j) :
    hullρ M k ≤ hullρ M j := by
  rcases le_or_gt k j with h | h
  · exact hullρ_mono hA h
  · unfold hullρ; rw [vtx_const h.le hk]

lemma hullW_hullQ (j : ℕ) : hullW M (hullQ M j) = M (hullQ M j) := by
  unfold hullW; rw [vtx_hullQ]; simp

lemma rpow_le_one_add {x r : ℝ} (hx : 0 ≤ x) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : x ^ r ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx h hr0
    linarith
  · calc x ^ r ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hr1
      _ = x := Real.rpow_one x
      _ ≤ 1 + x := by linarith

lemma hullW_prod (hM : ∀ k, 0 < M k) (k : ℕ) :
    hullW M k = hullW M 0 * ∏ l ∈ Finset.range k, hullρ M l := by
  induction k with
  | zero => simp
  | succ k ih => rw [hullW_succ hM, ih, Finset.prod_range_succ]; ring

lemma term_bound (hA : Superlin M) (hM : ∀ k, 0 < M k) (k : ℕ) :
    M (k + 1) ^ (-(1 : ℝ) / ((k + 1 : ℕ) : ℝ)) ≤
      (1 + (hullW M 0)⁻¹) * (∏ l ∈ Finset.range (k + 1), (hullρ M l)⁻¹) ^ ((1 : ℝ) / (k + 1)) := by
  set r : ℝ := (1 : ℝ) / (k + 1) with hr
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]; linarith
  have hexp : (-(1 : ℝ) / ((k + 1 : ℕ) : ℝ)) = -r := by rw [hr]; push_cast; ring
  rw [hexp]
  have hP : 0 < ∏ l ∈ Finset.range (k + 1), hullρ M l :=
    Finset.prod_pos (fun l _ => hullρ_pos l)
  have hW0 := hullW_pos hM 0
  calc M (k + 1) ^ (-r) ≤ hullW M (k + 1) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos (hullW_pos hM _) (hullW_le hA hM _) (by linarith)
    _ = (hullW M 0) ^ (-r) * (∏ l ∈ Finset.range (k + 1), hullρ M l) ^ (-r) := by
        rw [hullW_prod hM, Real.mul_rpow hW0.le hP.le]
    _ = ((hullW M 0)⁻¹) ^ r * (∏ l ∈ Finset.range (k + 1), (hullρ M l)⁻¹) ^ r := by
        rw [Finset.prod_inv_distrib, Real.inv_rpow hW0.le, Real.inv_rpow hP.le,
          Real.rpow_neg hW0.le, Real.rpow_neg hP.le]
    _ ≤ (1 + (hullW M 0)⁻¹) * (∏ l ∈ Finset.range (k + 1), (hullρ M l)⁻¹) ^ r := by
        apply mul_le_mul_of_nonneg_right _
          (Real.rpow_nonneg (Finset.prod_nonneg (fun l _ => (inv_pos.2 (hullρ_pos l)).le)) r)
        exact rpow_le_one_add (inv_nonneg.2 hW0.le) hr0 hr1

lemma hullρ_not_summable (hA : Superlin M) (hM : ∀ k, 0 < M k)
    (hdiv : ¬ Summable (fun k : ℕ => M k ^ (-(1 : ℝ) / k))) :
    ¬ Summable (fun k => (hullρ M k)⁻¹) := by
  intro hs
  have hnn : ∀ k, 0 ≤ (hullρ M k)⁻¹ := fun k => (inv_pos.2 (hullρ_pos k)).le
  have hW0 := hullW_pos hM 0
  have hC : 0 ≤ 1 + (hullW M 0)⁻¹ := by positivity
  have hsum : Summable (fun k : ℕ => M (k + 1) ^ (-(1 : ℝ) / ((k + 1 : ℕ) : ℝ))) := by
    refine summable_of_sum_range_le
      (c := (1 + (hullW M 0)⁻¹) * (Real.exp 1 * ∑' k, (hullρ M k)⁻¹))
      (fun k => Real.rpow_nonneg (hM _).le _) (fun N => ?_)
    have hcar := carleman_ineq (fun k => (hullρ M k)⁻¹) hnn N
    have hpart : ∑ k ∈ Finset.range N, (hullρ M k)⁻¹ ≤ ∑' k, (hullρ M k)⁻¹ :=
      hs.sum_le_tsum _ (fun k _ => hnn k)
    calc ∑ k ∈ Finset.range N, M (k + 1) ^ (-(1 : ℝ) / ((k + 1 : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.range N, (1 + (hullW M 0)⁻¹) *
            (∏ l ∈ Finset.range (k + 1), (hullρ M l)⁻¹) ^ ((1 : ℝ) / (k + 1)) :=
          Finset.sum_le_sum (fun k _ => term_bound hA hM k)
      _ = (1 + (hullW M 0)⁻¹) * ∑ k ∈ Finset.range N,
            (∏ l ∈ Finset.range (k + 1), (hullρ M l)⁻¹) ^ ((1 : ℝ) / (k + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (1 + (hullW M 0)⁻¹) * (Real.exp 1 * ∑ k ∈ Finset.range N, (hullρ M k)⁻¹) := by
          gcongr
      _ ≤ (1 + (hullW M 0)⁻¹) * (Real.exp 1 * ∑' k, (hullρ M k)⁻¹) := by
          gcongr
  exact hdiv ((summable_nat_add_iff 1).1 hsum)

/-! ### The analytic case -/

lemma flat_taylor {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ k x, ‖iteratedDeriv k f x‖ ≤ M k) (hzero : ∀ k, iteratedDeriv k f 0 = 0)
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : ‖f x‖ ≤ M (n + 1) * x ^ (n + 1) / n ! := by
  have := taylor_bound hf (x := 0) (h := x) hx n (C := M (n + 1)) (fun y _ => hbound (n + 1) y)
  simpa [hzero] using this

lemma forward_caseB {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (hM : ∀ k, 0 < M k)
    (hbound : ∀ k x, ‖iteratedDeriv k f x‖ ≤ M k) (hzero : ∀ k, iteratedDeriv k f 0 = 0)
    (hB : ¬ Superlin M) : ∀ x, 0 ≤ x → f x = 0 := by
  intro x hx
  unfold Superlin at hB
  push Not at hB
  obtain ⟨R, hR⟩ := hB
  set y := Real.exp R * x with hy
  have hy0 : 0 ≤ y := by positivity
  have hlim : Tendsto (fun n : ℕ => y * (y ^ n / n !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop y).const_mul y
  by_contra hne
  have hε : 0 < ‖f x‖ := norm_pos_iff.2 hne
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
  obtain ⟨b, hb, hbR⟩ := Filter.frequently_atTop.1 hR (N + 1)
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  have h1 := flat_taylor hf hbound hzero hx n
  have h2 : M (n + 1) ≤ Real.exp (R * ((n + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_log (hM (n + 1))]; exact Real.exp_le_exp.2 hbR.le
  have h3 := hN n (by omega)
  have h4 : M (n + 1) * x ^ (n + 1) / n ! ≤ y * (y ^ n / n !) := by
    calc M (n + 1) * x ^ (n + 1) / n ! ≤ Real.exp (R * ((n + 1 : ℕ) : ℝ)) * x ^ (n + 1) / n ! := by
          gcongr
      _ = y * (y ^ n / n !) := by
          rw [show R * ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) * R by ring, Real.exp_nat_mul, hy]
          ring
  linarith

/-! ### Forward uniqueness and the theorem -/

theorem forward {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (hM : ∀ k, 0 < M k)
    (hbound : ∀ k x, ‖iteratedDeriv k f x‖ ≤ M k) (hzero : ∀ k, iteratedDeriv k f 0 = 0)
    (hdiv : ¬ Summable (fun k : ℕ => M k ^ (-(1 : ℝ) / k))) :
    ∀ x, 0 ≤ x → f x = 0 := by
  by_cases hA : Superlin M
  · exact forward_of_data hf (hullW_pos hM) hullρ_pos (hullW_succ hM) hullQ_ge hullQ_mono
      (hullρ_le_of_lt_hullQ hA) (fun j y => by rw [hullW_hullQ]; exact hbound _ y)
      (hullρ_not_summable hA hM hdiv) hzero
  · exact forward_caseB hf hM hbound hzero hA

end DenjoyCarlemanF6

/-- **Denjoy–Carleman (Carleman's criterion).** A smooth function on `ℝ` whose derivatives are
bounded by `M k`, with `∑ M k ^ (-1/k) = ∞`, and which vanishes to infinite order at `0`, is
identically zero. -/
theorem denjoy_carleman (f : ℝ → ℂ) (M : ℕ → ℝ) (hf : ContDiff ℝ ∞ f) (hM : ∀ k, 0 < M k)
    (hbound : ∀ k x, ‖iteratedDeriv k f x‖ ≤ M k) (hzero : ∀ k, iteratedDeriv k f 0 = 0)
    (hdiv : ¬ Summable (fun k : ℕ => M k ^ (-(1 : ℝ) / k))) :
    ∀ x, f x = 0 := by
  intro x
  rcases le_or_gt 0 x with hx | hx
  · exact DenjoyCarlemanF6.forward hf hM hbound hzero hdiv x hx
  · -- reflection; adapted from quasianalytic-lean, `DenjoyCarleman/DC45.lean` (`DC5_backward`)
    have hg : ContDiff ℝ ∞ (fun y => f (-y)) := hf.comp contDiff_neg
    have hgb : ∀ k y, ‖iteratedDeriv k (fun y => f (-y)) y‖ ≤ M k := by
      intro k y
      rw [iteratedDeriv_comp_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hbound k (-y)
    have hgz : ∀ k, iteratedDeriv k (fun y => f (-y)) 0 = 0 := by
      intro k; rw [iteratedDeriv_comp_neg, neg_zero, hzero, smul_zero]
    have := DenjoyCarlemanF6.forward hg hM hgb hgz hdiv (-x) (by linarith)
    simpa using this

end MazyaRefinedCauchy
