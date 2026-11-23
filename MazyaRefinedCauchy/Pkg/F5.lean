module

public import MazyaRefinedCauchy.Setup
public import Mathlib


@[expose] public section

/-!
# Work package F5

The theorems stated in this file are the frozen contract of package F5 (see `BLUEPRINT.md`).
Helper lemmas may be added; the statements of the contract theorems must not change.

## The construction of the majorant

We simplify the construction of the informal note (a smoothed concave minorant). Write
`Λ_g(σ) = log (1 / g (e^{-σ}))`. We build `Λ_g` directly as a supremum of convex functions
```
  L(σ) = sup_k φ_k(σ),   φ_k(σ) = (5/4)^k (e^σ - e^{a_k}),
```
where the thresholds `a_k` satisfy `a_{k+1} ≥ a_k + 1`, `a_k ≥ k`, and
`h(e^{-σ}) ≤ exp (-(5/4)^k e^σ)` for `σ ≥ a_k` (possible by the hypothesis on `h`).
Then `g(r) = exp (-L(log (1/r)))`, and:

* `L` is convex and nondecreasing (a supremum of convex nondecreasing functions);
* `e^{-σ} L(σ) ≥ (5/4)^k / 2` for `σ ≥ a_k + 1`, so `e^{-σ} L(σ) → ∞`;
* `φ_k(σ + t) ≤ e^{2t} φ_k(σ)` for `σ ≥ a_k + 1`, and `φ_{k+1} ≤ max 0 φ_k` on
  `(-∞, a_{k+1} + 1]` (this uses `e ≤ 4`); by induction on `k`,
  `L(σ + t) ≤ e^{2t} L(σ)` for `σ ≥ a_0 + 1`, `t ≥ 0`;
* `L(σ) ≤ log (1 / h(e^{-σ}))` for `σ ≥ a_0`, i.e. `h ≤ g` near `0`.
-/

open scoped ContDiff RealInnerProductSpace
open Filter Topology InnerProductSpace MeasureTheory

namespace MazyaRefinedCauchy

variable {n : ℕ}

/-! ## Package F5: regular profiles and the majorant -/

/-- Regularity of a decay profile `h`: `Λ(σ) = log(1/h(e^{-σ}))` is eventually convex,
superlinear, and satisfies `Λ(σ + t) ≤ e^{Ct} Λ(σ)` for large `σ` and `t ≥ 0`. -/
structure RegularProfile (h : ℝ → ℝ) : Prop where
  convex : ∃ σ₀ : ℝ, ConvexOn ℝ (Set.Ici σ₀) (fun σ => Real.log (1 / h (Real.exp (-σ))))
  super : Tendsto (fun σ => Real.log (1 / h (Real.exp (-σ))) / σ) atTop atTop
  growth : ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ t ≥ 0,
    Real.log (1 / h (Real.exp (-(σ + t)))) ≤ Real.exp (C * t) * Real.log (1 / h (Real.exp (-σ)))

namespace F5

/-! ### Thresholds -/

/-- A sequence of thresholds with gaps at least `1`:
`seq T 0 = max (T 0) 0` and `seq T (k + 1) = max (T (k + 1)) (seq T k + 1)`. -/
noncomputable def seq (T : ℕ → ℝ) : ℕ → ℝ
  | 0 => max (T 0) 0
  | k + 1 => max (T (k + 1)) (seq T k + 1)

theorem le_seq (T : ℕ → ℝ) (k : ℕ) : T k ≤ seq T k := by
  cases k with
  | zero => exact le_max_left _ _
  | succ k => exact le_max_left _ _

theorem seq_add_one_le (T : ℕ → ℝ) (k : ℕ) : seq T k + 1 ≤ seq T (k + 1) :=
  le_max_right _ _

theorem natCast_le_seq (T : ℕ → ℝ) (k : ℕ) : (k : ℝ) ≤ seq T k := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero]
    exact le_max_right _ _
  | succ k ih =>
    push_cast
    linarith [seq_add_one_le T k]

/-! ### The building blocks `φ_k` and their supremum `L` -/

/-- The building blocks `φ_k(σ) = (5/4)^k (e^σ - e^{a_k})`. -/
noncomputable def phi (a : ℕ → ℝ) (k : ℕ) (σ : ℝ) : ℝ :=
  (5 / 4 : ℝ) ^ k * (Real.exp σ - Real.exp (a k))

/-- The convex function `L = sup_k φ_k`. -/
noncomputable def Lfun (a : ℕ → ℝ) (σ : ℝ) : ℝ := ⨆ k, phi a k σ

/-- The majorant `g(r) = exp (-L(log (1/r)))`. -/
noncomputable def gfun (a : ℕ → ℝ) (r : ℝ) : ℝ := Real.exp (-Lfun a (-Real.log r))

theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.add_one_le_exp 1]

theorem phi_le (a : ℕ → ℝ) (k : ℕ) (σ : ℝ) : phi a k σ ≤ (5 / 4 : ℝ) ^ k * Real.exp σ := by
  unfold phi
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [Real.exp_pos (a k)]

theorem phi_nonpos (a : ℕ → ℝ) {k : ℕ} {σ : ℝ} (h : σ ≤ a k) : phi a k σ ≤ 0 := by
  unfold phi
  have : Real.exp σ ≤ Real.exp (a k) := Real.exp_le_exp.2 h
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem bddAbove_phi (a : ℕ → ℝ) (ha : ∀ k : ℕ, (k : ℝ) ≤ a k) (σ : ℝ) :
    BddAbove (Set.range fun k => phi a k σ) := by
  refine ⟨Real.exp σ * Real.exp σ, ?_⟩
  rintro _ ⟨k, rfl⟩
  by_cases hk : (k : ℝ) ≤ σ
  · calc phi a k σ ≤ (5 / 4 : ℝ) ^ k * Real.exp σ := phi_le a k σ
      _ ≤ Real.exp σ * Real.exp σ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos σ).le
        calc (5 / 4 : ℝ) ^ k ≤ (Real.exp 1) ^ k := by
              apply pow_le_pow_left₀ (by norm_num)
              linarith [two_le_exp_one]
          _ = Real.exp k := by rw [← Real.exp_nat_mul, mul_one]
          _ ≤ Real.exp σ := Real.exp_le_exp.2 hk
  · simp only [not_le] at hk
    have h1 := phi_nonpos a (k := k) (σ := σ) (by linarith [ha k])
    have h2 := Real.exp_pos σ
    have h3 : 0 ≤ Real.exp σ * Real.exp σ := by positivity
    linarith

theorem phi_le_Lfun (a : ℕ → ℝ) (ha : ∀ k : ℕ, (k : ℝ) ≤ a k) (k : ℕ) (σ : ℝ) :
    phi a k σ ≤ Lfun a σ :=
  le_ciSup (bddAbove_phi a ha σ) k

theorem convexOn_Lfun (a : ℕ → ℝ) (ha : ∀ k : ℕ, (k : ℝ) ≤ a k) :
    ConvexOn ℝ Set.univ (Lfun a) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ p q hp hq hpq
  apply ciSup_le
  intro k
  have hexp := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) hp hq hpq
  simp only [smul_eq_mul] at hexp ⊢
  have hx := phi_le_Lfun a ha k x
  have hy := phi_le_Lfun a ha k y
  have hc : (0 : ℝ) < (5 / 4 : ℝ) ^ k := by positivity
  calc phi a k (p * x + q * y)
        = (5 / 4 : ℝ) ^ k * (Real.exp (p * x + q * y) - Real.exp (a k)) := rfl
    _ ≤ (5 / 4 : ℝ) ^ k * (p * Real.exp x + q * Real.exp y - Real.exp (a k)) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        linarith
    _ = p * phi a k x + q * phi a k y := by
        unfold phi
        linear_combination (5 / 4 : ℝ) ^ k * Real.exp (a k) * hpq
    _ ≤ p * Lfun a x + q * Lfun a y :=
        add_le_add (mul_le_mul_of_nonneg_left hx hp) (mul_le_mul_of_nonneg_left hy hq)

theorem phi_mono (a : ℕ → ℝ) (k : ℕ) : Monotone (phi a k) := by
  intro x y hxy
  unfold phi
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [Real.exp_le_exp.2 hxy]

theorem Lfun_mono (a : ℕ → ℝ) (ha : ∀ k : ℕ, (k : ℝ) ≤ a k) : Monotone (Lfun a) := fun _ y hxy =>
  ciSup_mono (bddAbove_phi a ha y) (fun k => phi_mono a k hxy)

/-- `e^{a_k} ≤ e^σ / 2` once `σ ≥ a_k + 1`. -/
theorem two_mul_exp_le {b σ : ℝ} (h : b + 1 ≤ σ) : 2 * Real.exp b ≤ Real.exp σ := by
  have hb := Real.exp_pos b
  calc 2 * Real.exp b ≤ Real.exp 1 * Real.exp b :=
        mul_le_mul_of_nonneg_right two_le_exp_one hb.le
    _ = Real.exp (b + 1) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp σ := Real.exp_le_exp.2 h

/-- Growth of a single block: `φ_k(σ + t) ≤ e^{2t} φ_k(σ)` for `σ ≥ a_k + 1`, `t ≥ 0`. -/
theorem phi_add_le (a : ℕ → ℝ) {k : ℕ} {σ t : ℝ} (hσ : a k + 1 ≤ σ) (ht : 0 ≤ t) :
    phi a k (σ + t) ≤ Real.exp (2 * t) * phi a k σ := by
  unfold phi
  have hA := Real.exp_pos (a k)
  have hS : 2 * Real.exp (a k) ≤ Real.exp σ := two_mul_exp_le hσ
  have hu : 1 ≤ Real.exp t := Real.one_le_exp ht
  have h2t : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.exp_add, h2t]
  have hc : (0 : ℝ) < (5 / 4 : ℝ) ^ k := by positivity
  have key : Real.exp σ * Real.exp t - Real.exp (a k)
      ≤ Real.exp t * Real.exp t * (Real.exp σ - Real.exp (a k)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu)
        (mul_nonneg (sub_nonneg.2 hS) (by linarith : (0 : ℝ) ≤ Real.exp t)),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hu) hA.le) (sub_nonneg.2 hu)]
  calc (5 / 4 : ℝ) ^ k * (Real.exp σ * Real.exp t - Real.exp (a k))
      ≤ (5 / 4 : ℝ) ^ k * (Real.exp t * Real.exp t * (Real.exp σ - Real.exp (a k))) :=
        mul_le_mul_of_nonneg_left key hc.le
    _ = Real.exp t * Real.exp t * ((5 / 4 : ℝ) ^ k * (Real.exp σ - Real.exp (a k))) := by ring

/-- The block `φ_{k+1}` does not exceed `max 0 φ_k` up to `a_{k+1} + 1`. -/
theorem phi_succ_le (a : ℕ → ℝ) (ha : ∀ k, a k + 1 ≤ a (k + 1)) {k : ℕ} {s : ℝ}
    (hs : s ≤ a (k + 1) + 1) : phi a (k + 1) s ≤ max 0 (phi a k s) := by
  by_cases h1 : s ≤ a (k + 1)
  · exact (phi_nonpos a h1).trans (le_max_left _ _)
  · simp only [not_le] at h1
    apply le_max_of_le_right
    unfold phi
    have hE1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hE0 : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
    have hA := Real.exp_pos (a (k + 1))
    have hB := Real.exp_pos (a k)
    have hSA : Real.exp s ≤ Real.exp 1 * Real.exp (a (k + 1)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have hBA : Real.exp 1 * Real.exp (a k) ≤ Real.exp (a (k + 1)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith [ha k])
    have hc : (0 : ℝ) < (5 / 4 : ℝ) ^ k := by positivity
    have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have key : (5 / 4 : ℝ) * (Real.exp s - Real.exp (a (k + 1))) ≤ Real.exp s - Real.exp (a k) := by
      have hq : Real.exp (a (k + 1)) * ((Real.exp 1 - 1) * (Real.exp 1 - 4)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hA.le
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      have h1' : Real.exp 1 * Real.exp s ≤ Real.exp 1 * (Real.exp 1 * Real.exp (a (k + 1))) :=
        mul_le_mul_of_nonneg_left hSA hEpos.le
      have h2' : Real.exp 1 * ((5 / 4 : ℝ) * (Real.exp s - Real.exp (a (k + 1)))
          - (Real.exp s - Real.exp (a k))) ≤ Real.exp 1 * 0 := by
        nlinarith
      have := le_of_mul_le_mul_left h2' hEpos
      linarith
    rw [pow_succ]
    calc (5 / 4 : ℝ) ^ k * (5 / 4) * (Real.exp s - Real.exp (a (k + 1)))
        = (5 / 4 : ℝ) ^ k * ((5 / 4) * (Real.exp s - Real.exp (a (k + 1)))) := by ring
      _ ≤ (5 / 4 : ℝ) ^ k * (Real.exp s - Real.exp (a k)) :=
        mul_le_mul_of_nonneg_left key hc.le

theorem Lfun_nonneg (a : ℕ → ℝ) (ha : ∀ k : ℕ, (k : ℝ) ≤ a k) {σ : ℝ} (hσ : a 0 ≤ σ) :
    0 ≤ Lfun a σ := by
  have h0 : 0 ≤ phi a 0 σ := by
    unfold phi
    simp only [pow_zero, one_mul]
    linarith [Real.exp_le_exp.2 hσ]
  exact h0.trans (phi_le_Lfun a ha 0 σ)

/-- The growth estimate for every block against `L`, by induction on `k`. -/
theorem phi_growth (a : ℕ → ℝ) (ha1 : ∀ k, a k + 1 ≤ a (k + 1)) (ha2 : ∀ k : ℕ, (k : ℝ) ≤ a k) :
    ∀ k : ℕ, ∀ σ, a 0 + 1 ≤ σ → ∀ t, 0 ≤ t →
      phi a k (σ + t) ≤ Real.exp (2 * t) * Lfun a σ := by
  intro k
  induction k with
  | zero =>
    intro σ hσ t ht
    calc phi a 0 (σ + t) ≤ Real.exp (2 * t) * phi a 0 σ := phi_add_le a hσ ht
      _ ≤ Real.exp (2 * t) * Lfun a σ :=
        mul_le_mul_of_nonneg_left (phi_le_Lfun a ha2 0 σ) (Real.exp_pos _).le
  | succ k ih =>
    intro σ hσ t ht
    have hL : 0 ≤ Lfun a σ := Lfun_nonneg a ha2 (by linarith)
    by_cases h1 : a (k + 1) + 1 ≤ σ
    · calc phi a (k + 1) (σ + t) ≤ Real.exp (2 * t) * phi a (k + 1) σ := phi_add_le a h1 ht
        _ ≤ Real.exp (2 * t) * Lfun a σ :=
          mul_le_mul_of_nonneg_left (phi_le_Lfun a ha2 _ σ) (Real.exp_pos _).le
    · simp only [not_le] at h1
      by_cases h2 : σ + t ≤ a (k + 1) + 1
      · calc phi a (k + 1) (σ + t) ≤ max 0 (phi a k (σ + t)) := phi_succ_le a ha1 h2
          _ ≤ Real.exp (2 * t) * Lfun a σ :=
            max_le (mul_nonneg (Real.exp_pos _).le hL) (ih σ hσ t ht)
      · simp only [not_le] at h2
        have e1 : σ + (a (k + 1) + 1 - σ) = a (k + 1) + 1 := by ring
        have e2 : a (k + 1) + 1 + (σ + t - (a (k + 1) + 1)) = σ + t := by ring
        have h3 := phi_add_le a (k := k + 1) (σ := a (k + 1) + 1)
          (t := σ + t - (a (k + 1) + 1)) le_rfl (by linarith)
        rw [e2] at h3
        have h4 : phi a (k + 1) (a (k + 1) + 1) ≤ max 0 (phi a k (a (k + 1) + 1)) :=
          phi_succ_le a ha1 le_rfl
        have h5 := ih σ hσ (a (k + 1) + 1 - σ) (by linarith)
        rw [e1] at h5
        have e3 : 2 * (σ + t - (a (k + 1) + 1)) + 2 * (a (k + 1) + 1 - σ) = 2 * t := by ring
        calc phi a (k + 1) (σ + t)
            ≤ Real.exp (2 * (σ + t - (a (k + 1) + 1))) * phi a (k + 1) (a (k + 1) + 1) := h3
          _ ≤ Real.exp (2 * (σ + t - (a (k + 1) + 1))) * max 0 (phi a k (a (k + 1) + 1)) :=
            mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
          _ ≤ Real.exp (2 * (σ + t - (a (k + 1) + 1)))
                * (Real.exp (2 * (a (k + 1) + 1 - σ)) * Lfun a σ) :=
            mul_le_mul_of_nonneg_left
              (max_le (mul_nonneg (Real.exp_pos _).le hL) h5) (Real.exp_pos _).le
          _ = Real.exp (2 * t) * Lfun a σ := by
            rw [← mul_assoc, ← Real.exp_add, e3]

theorem Lfun_growth (a : ℕ → ℝ) (ha1 : ∀ k, a k + 1 ≤ a (k + 1)) (ha2 : ∀ k : ℕ, (k : ℝ) ≤ a k)
    {σ t : ℝ} (hσ : a 0 + 1 ≤ σ) (ht : 0 ≤ t) :
    Lfun a (σ + t) ≤ Real.exp (2 * t) * Lfun a σ :=
  ciSup_le fun k => phi_growth a ha1 ha2 k σ hσ t ht

/-- `e^{-σ} L(σ) → ∞`. -/
theorem tendsto_exp_neg_mul_Lfun (a : ℕ → ℝ) (ha2 : ∀ k : ℕ, (k : ℝ) ≤ a k) :
    Tendsto (fun σ => Real.exp (-σ) * Lfun a σ) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * B) (by norm_num : (1 : ℝ) < 5 / 4)
  rw [eventually_atTop]
  refine ⟨a k + 1, fun σ hσ => ?_⟩
  have hS : 2 * Real.exp (a k) ≤ Real.exp σ := two_mul_exp_le hσ
  have hc : (0 : ℝ) < (5 / 4 : ℝ) ^ k := by positivity
  have h1 : (5 / 4 : ℝ) ^ k * Real.exp σ / 2 ≤ phi a k σ := by
    unfold phi
    nlinarith [mul_nonneg hc.le (sub_nonneg.2 hS)]
  have h2 := phi_le_Lfun a ha2 k σ
  have hpos := Real.exp_pos σ
  calc B ≤ (5 / 4 : ℝ) ^ k / 2 := by linarith
    _ = Real.exp (-σ) * ((5 / 4 : ℝ) ^ k * Real.exp σ / 2) := by
        rw [Real.exp_neg]; field_simp
    _ ≤ Real.exp (-σ) * Lfun a σ :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le

/-- `L(σ) / σ → ∞`. -/
theorem tendsto_Lfun_div (a : ℕ → ℝ) (ha2 : ∀ k : ℕ, (k : ℝ) ≤ a k) :
    Tendsto (fun σ => Lfun a σ / σ) atTop atTop := by
  have h := (tendsto_exp_neg_mul_Lfun a ha2).atTop_mul_atTop₀ (Real.tendsto_exp_div_pow_atTop 1)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with σ hσ
  rw [pow_one, Real.exp_neg]
  field_simp

/-- The majorant property: `h(e^{-σ}) ≤ e^{-L(σ)}` for `σ ≥ a_0`. -/
theorem le_exp_neg_Lfun (a : ℕ → ℝ) (h : ℝ → ℝ)
    (hh : ∀ k σ, a k ≤ σ → h (Real.exp (-σ)) ≤ Real.exp (-((5 / 4 : ℝ) ^ k * Real.exp σ)))
    {σ : ℝ} (hσ : a 0 ≤ σ) : h (Real.exp (-σ)) ≤ Real.exp (-Lfun a σ) := by
  rcases le_or_gt (h (Real.exp (-σ))) 0 with hneg | hpos
  · exact hneg.trans (Real.exp_pos _).le
  · have hk : ∀ k, phi a k σ ≤ -Real.log (h (Real.exp (-σ))) := by
      intro k
      have hle : h (Real.exp (-σ)) ≤ Real.exp (-phi a k σ) := by
        by_cases hk : a k ≤ σ
        · refine (hh k σ hk).trans (Real.exp_le_exp.2 ?_)
          linarith [phi_le a k σ]
        · simp only [not_le] at hk
          refine (hh 0 σ hσ).trans (Real.exp_le_exp.2 ?_)
          have h1 := phi_nonpos a hk.le
          have h2 : 0 ≤ (5 / 4 : ℝ) ^ 0 * Real.exp σ := by positivity
          linarith
      have := Real.log_le_log hpos hle
      rw [Real.log_exp] at this
      linarith
    have hL : Lfun a σ ≤ -Real.log (h (Real.exp (-σ))) := ciSup_le hk
    calc h (Real.exp (-σ)) = Real.exp (Real.log (h (Real.exp (-σ)))) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (-Lfun a σ) := Real.exp_le_exp.2 (by linarith)

theorem log_one_div_gfun (a : ℕ → ℝ) (r : ℝ) :
    Real.log (1 / gfun a r) = Lfun a (-Real.log r) := by
  unfold gfun
  rw [one_div, Real.log_inv, Real.log_exp, neg_neg]

theorem log_one_div_gfun_exp (a : ℕ → ℝ) (σ : ℝ) :
    Real.log (1 / gfun a (Real.exp (-σ))) = Lfun a σ := by
  rw [log_one_div_gfun, Real.log_exp, neg_neg]

theorem regularProfile_gfun (a : ℕ → ℝ) (ha1 : ∀ k, a k + 1 ≤ a (k + 1))
    (ha2 : ∀ k : ℕ, (k : ℝ) ≤ a k) : RegularProfile (gfun a) where
  convex := ⟨0, by
    simp only [log_one_div_gfun_exp]
    exact (convexOn_Lfun a ha2).subset (Set.subset_univ _) (convex_Ici 0)⟩
  super := by
    simp only [log_one_div_gfun_exp]
    exact tendsto_Lfun_div a ha2
  growth := ⟨2, a 0 + 1, fun σ hσ t ht => by
    simp only [log_one_div_gfun_exp]
    exact Lfun_growth a ha1 ha2 hσ ht⟩

end F5

open F5 in
/-- A profile with `h(r) ≤ e^{-M/r}` eventually, for every `M`, has a positive, nondecreasing,
regular majorant `g` with `r log(1/g(r)) → ∞`. -/
theorem exists_regular_majorant (h : ℝ → ℝ)
    (hh : ∀ M : ℝ, ∀ᶠ r in 𝓝[>] 0, h r ≤ Real.exp (-M / r)) :
    ∃ g : ℝ → ℝ, ∃ r₀ > 0, (∀ r ∈ Set.Ioo 0 r₀, h r ≤ g r) ∧ (∀ r, 0 < r → 0 < g r) ∧
      MonotoneOn g (Set.Ioi 0) ∧ RegularProfile g ∧
      Tendsto (fun r => r * Real.log (1 / g r)) (𝓝[>] 0) atTop := by
  -- thresholds in the variable `σ = log (1/r)`
  have hT : ∀ M : ℝ, ∃ S : ℝ, ∀ σ, S ≤ σ →
      h (Real.exp (-σ)) ≤ Real.exp (-(M * Real.exp σ)) := by
    intro M
    have hlim : Tendsto (fun σ : ℝ => Real.exp (-σ)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
        Eventually.of_forall fun σ => Real.exp_pos _⟩
    obtain ⟨S, hS⟩ := eventually_atTop.1 (hlim.eventually (hh M))
    refine ⟨S, fun σ hσ => ?_⟩
    have h1 := hS σ hσ
    have e : -M / Real.exp (-σ) = -(M * Real.exp σ) := by
      rw [Real.exp_neg, div_inv_eq_mul]; ring
    rwa [e] at h1
  choose S hS using hT
  have ha1 : ∀ k, seq (fun k => S ((5 / 4 : ℝ) ^ k)) k + 1
      ≤ seq (fun k => S ((5 / 4 : ℝ) ^ k)) (k + 1) := fun k => seq_add_one_le _ k
  have ha2 : ∀ k : ℕ, (k : ℝ) ≤ seq (fun k => S ((5 / 4 : ℝ) ^ k)) k :=
    fun k => natCast_le_seq _ k
  have ha3 : ∀ k σ, seq (fun k => S ((5 / 4 : ℝ) ^ k)) k ≤ σ →
      h (Real.exp (-σ)) ≤ Real.exp (-((5 / 4 : ℝ) ^ k * Real.exp σ)) :=
    fun k σ hσ => hS _ σ ((le_seq (fun k => S ((5 / 4 : ℝ) ^ k)) k).trans hσ)
  set a := seq (fun k => S ((5 / 4 : ℝ) ^ k)) with ha_def
  refine ⟨gfun a, Real.exp (-a 0), Real.exp_pos _, ?_, ?_, ?_, regularProfile_gfun a ha1 ha2, ?_⟩
  · -- `h ≤ g` near `0`
    rintro r ⟨hr0, hr⟩
    have hσ : a 0 ≤ -Real.log r := by
      have := Real.log_lt_log hr0 hr
      rw [Real.log_exp] at this
      linarith
    have := le_exp_neg_Lfun a h ha3 hσ
    rwa [neg_neg, Real.exp_log hr0] at this
  · -- positivity
    intro r _
    exact Real.exp_pos _
  · -- monotonicity
    intro x hx y hy hxy
    unfold gfun
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply Lfun_mono a ha2
    exact neg_le_neg (Real.log_le_log hx hxy)
  · -- `r log (1/g(r)) → ∞`
    have h1 : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    have h2 := (tendsto_exp_neg_mul_Lfun a ha2).comp h1
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    show Real.exp (-(-Real.log r)) * Lfun a (-Real.log r) = r * Real.log (1 / gfun a r)
    rw [neg_neg, Real.exp_log hr, log_one_div_gfun]

end MazyaRefinedCauchy
