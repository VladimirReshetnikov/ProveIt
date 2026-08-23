import IntegerPoints.SP5Core
import IntegerPoints.GKLemma33

/-!
# Graham–Kolesnik, Lemma 3.4 (stationary phase)

`∫_a^b e(g(x)) dx = e(1/8 + g(x₀)) / g''(x₀)^{1/2} + O(R₁ + R₂)` for `g ∈ C⁴` with
`g'' ≥ λ₂ > 0`, `g'(x₀) = 0`, `|g'''| ≤ λ₃`, `|g''''| ≤ λ₄` on `[a, b]`, where
`R₁ = min(1/(λ₂(x₀ − a)), λ₂^{-1/2}) + min(1/(λ₂(b − x₀)), λ₂^{-1/2})` and
`R₂ = (b − a)λ₄λ₂⁻² + (b − a)λ₃²λ₂⁻³`.

* If `x₀ − a ≥ λ₂^{-1/2}` and `b − x₀ ≥ λ₂^{-1/2}`, translate to `x₀ = 0`, `g(0) = 0`
  (`SP.Data`) and apply the core estimate `SP.Data.core_bound`; then `R₁` is
  `1/(λ₂(x₀ − a)) + 1/(λ₂(b − x₀))`.
* Otherwise `R₁ ≥ λ₂^{-1/2}`, and Lemma 3.2 bounds the integral by `≪ λ₂^{-1/2}` while the
  main term has modulus `≤ λ₂^{-1/2}`.

The case `g'' ≤ −λ₂` follows by conjugation (`g ↦ −g`).
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace GK34

theorem iteratedDeriv_two (g : ℝ → ℝ) : iteratedDeriv 2 g = deriv (deriv g) := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]

theorem iteratedDeriv_three (g : ℝ → ℝ) : iteratedDeriv 3 g = deriv (deriv (deriv g)) := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_two]

theorem iteratedDeriv_four (g : ℝ → ℝ) :
    iteratedDeriv 4 g = deriv (deriv (deriv (deriv g))) := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_three]

/-- The translate `G(y) = g(y + x₀) − g(x₀)`. -/
noncomputable def shift (g : ℝ → ℝ) (x₀ : ℝ) (y : ℝ) : ℝ := g (y + x₀) - g x₀

theorem deriv_shift (g : ℝ → ℝ) (x₀ : ℝ) : deriv (shift g x₀) = fun y => deriv g (y + x₀) := by
  funext y
  unfold shift
  rw [deriv_sub_const, deriv_comp_add_const]

theorem deriv2_shift (g : ℝ → ℝ) (x₀ : ℝ) :
    deriv (deriv (shift g x₀)) = fun y => deriv (deriv g) (y + x₀) := by
  rw [deriv_shift]
  funext y
  rw [deriv_comp_add_const]

theorem deriv3_shift (g : ℝ → ℝ) (x₀ : ℝ) :
    deriv (deriv (deriv (shift g x₀))) = fun y => deriv (deriv (deriv g)) (y + x₀) := by
  rw [deriv2_shift]
  funext y
  rw [deriv_comp_add_const]

theorem deriv4_shift (g : ℝ → ℝ) (x₀ : ℝ) :
    deriv (deriv (deriv (deriv (shift g x₀)))) =
      fun y => deriv (deriv (deriv (deriv g))) (y + x₀) := by
  rw [deriv3_shift]
  funext y
  rw [deriv_comp_add_const]

theorem contDiff_shift {g : ℝ → ℝ} (hg : ContDiff ℝ 4 g) (x₀ : ℝ) : ContDiff ℝ 4 (shift g x₀) := by
  unfold shift
  exact (hg.comp (contDiff_id.add contDiff_const)).sub contDiff_const

/-- `∫_a^b e(g) = e(g(x₀)) ∫_{a−x₀}^{b−x₀} e(G)`. -/
theorem integral_shift (g : ℝ → ℝ) (a b x₀ : ℝ) :
    ∫ x in a..b, e (g x) = e (g x₀) * ∫ y in (a - x₀)..(b - x₀), e (shift g x₀ y) := by
  rw [← intervalIntegral.integral_const_mul]
  have : ∫ y in (a - x₀)..(b - x₀), e (g x₀) * e (shift g x₀ y) =
      ∫ y in (a - x₀)..(b - x₀), e (g (y + x₀)) := by
    apply integral_congr
    intro y _
    unfold shift
    change e (g x₀) * e (g (y + x₀) - g x₀) = e (g (y + x₀))
    rw [← KL.e_add]
    congr 1
    ring
  rw [this, intervalIntegral.integral_comp_add_right (fun x => e (g x)) x₀]
  simp

/-- `λ₂^{-1/2}`, with `s · s = 1/λ₂`. -/
theorem rpow_half_facts {lam₂ : ℝ} (h : 0 < lam₂) :
    0 < lam₂ ^ (-(1 : ℝ) / 2) ∧ lam₂ ^ (-(1 : ℝ) / 2) * lam₂ ^ (-(1 : ℝ) / 2) = 1 / lam₂ ∧
      lam₂ ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt lam₂ := by
  refine ⟨by positivity, ?_, ?_⟩
  · rw [← Real.rpow_add h]
    norm_num
    rw [Real.rpow_neg_one]
  · rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg h.le]
    simp only [one_div]

theorem minInv_nonneg {D t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t) : 0 ≤ minInv D t := by
  unfold minInv
  split_ifs
  · exact hD
  · exact le_min hD (by positivity)

/-- When `t ≥ 1/D`, `minInv D t = 1/t`. -/
theorem minInv_eq_inv {D t : ℝ} (hD : 0 < D) (ht : 1 / D ≤ t) : minInv D t = 1 / t := by
  unfold minInv
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  rw [if_neg ht0.ne']
  apply min_eq_right
  rw [div_le_iff₀ ht0]
  rw [div_le_iff₀ hD] at ht
  linarith

/-- When `0 ≤ t < 1/D`, `minInv D t = D`. -/
theorem minInv_eq_D {D t : ℝ} (hD : 0 < D) (ht0 : 0 ≤ t) (ht : t < 1 / D) : minInv D t = D := by
  unfold minInv
  split_ifs with h
  · rfl
  · apply min_eq_left
    have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h)
    rw [le_div_iff₀ ht0']
    rw [lt_div_iff₀ hD] at ht
    linarith

end GK34

open GK34 in
/-- **Graham–Kolesnik, Lemma 3.4** (the case `g'' ≥ λ₂ > 0`). -/
theorem gk_lemma34_holds : gk_lemma34 := by
  obtain ⟨C₁, h31⟩ := gk_lemma31_holds
  obtain ⟨C₂, h32⟩ := gk_lemma32_holds
  obtain ⟨C₃, h33⟩ := gk_lemma33_holds
  refine ⟨|SP.Data.C₀ C₁ C₃| + |C₂| + 1, ?_⟩
  intro a b x₀ lam₂ lam₃ lam₄ g hab hl2 hl3 hl4 hg h2 hx₀ hg'0 h3 h4
  rw [iteratedDeriv_two] at h2 ⊢
  rw [iteratedDeriv_three] at h3
  rw [iteratedDeriv_four] at h4
  obtain ⟨hs0, hss, hs⟩ := rpow_half_facts hl2
  set s : ℝ := lam₂ ^ (-(1 : ℝ) / 2) with hsdef
  have hinv : 1 / s = lam₂ * s := by
    rw [div_eq_iff hs0.ne', show lam₂ * s * s = lam₂ * (s * s) by ring, hss]
    field_simp
  have hR2nn : 0 ≤ gkR₂ lam₂ lam₃ lam₄ a b := by
    unfold gkR₂
    have : 0 ≤ b - a := by linarith
    positivity
  have hR1nn : 0 ≤ gkR₁ lam₂ a b x₀ := by
    unfold gkR₁
    have h1 : 0 ≤ lam₂ * (x₀ - a) := by nlinarith [hx₀.1]
    have h2' : 0 ≤ lam₂ * (b - x₀) := by nlinarith [hx₀.2]
    exact add_nonneg (minInv_nonneg hs0.le h1) (minInv_nonneg hs0.le h2')
  have hg2x₀ : lam₂ ≤ deriv (deriv g) x₀ := h2 x₀ hx₀
  -- the modulus of the main term is at most `s`
  have hmain : ‖e (1 / 8 + g x₀) / ((Real.sqrt (deriv (deriv g) x₀) : ℝ) : ℂ)‖ ≤ s := by
    rw [norm_div, PS.norm_e_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by linarith)), hs]
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 hl2)
    exact Real.sqrt_le_sqrt hg2x₀
  by_cases hcase : s ≤ x₀ - a ∧ s ≤ b - x₀
  · -- the generic case: translate and apply the core estimate
    obtain ⟨hca, hcb⟩ := hcase
    have ha' : a - x₀ < 0 := by linarith
    have hb' : 0 < b - x₀ := by linarith
    let D : SP.Data :=
      { g := shift g x₀, a := a - x₀, b := b - x₀, lam₂ := lam₂, lam₃ := lam₃, lam₄ := lam₄,
        ha := ha', hb := hb', hlam₂ := hl2, hlam₃ := hl3, hlam₄ := hl4,
        hg := contDiff_shift hg x₀,
        hg0 := by simp [shift],
        hg'0 := by rw [deriv_shift]; simpa using hg'0,
        h2 := fun y hy => by
          rw [deriv2_shift]
          exact h2 (y + x₀) ⟨by linarith [hy.1], by linarith [hy.2]⟩,
        h3 := fun y hy => by
          rw [deriv3_shift]
          exact h3 (y + x₀) ⟨by linarith [hy.1], by linarith [hy.2]⟩,
        h4 := fun y hy => by
          rw [deriv4_shift]
          exact h4 (y + x₀) ⟨by linarith [hy.1], by linarith [hy.2]⟩ }
    have hcore := D.core_bound h31 h33
    have hDg2 : D.g2 0 = deriv (deriv g) x₀ := by
      show deriv (deriv (shift g x₀)) 0 = _
      rw [deriv2_shift]
      simp
    have hDR1 : D.R₁ = gkR₁ lam₂ a b x₀ := by
      unfold SP.Data.R₁ gkR₁
      show 1 / (lam₂ * |a - x₀|) + 1 / (lam₂ * (b - x₀)) = _
      rw [minInv_eq_inv hs0 (by
          rw [hinv]
          exact mul_le_mul_of_nonneg_left hca hl2.le),
        minInv_eq_inv hs0 (by
          rw [hinv]
          exact mul_le_mul_of_nonneg_left hcb hl2.le),
        abs_of_neg ha']
      ring_nf
    have hDR2 : D.R₂ = gkR₂ lam₂ lam₃ lam₄ a b := by
      unfold SP.Data.R₂ gkR₂
      show (b - x₀ - (a - x₀)) * lam₄ * lam₂ ^ (-(2 : ℝ)) +
        (b - x₀ - (a - x₀)) * lam₃ ^ 2 * lam₂ ^ (-(3 : ℝ)) = _
      ring_nf
    -- relate the integrals
    have hint : (∫ x in a..b, e (g x)) - e (1 / 8 + g x₀) / ((Real.sqrt (deriv (deriv g) x₀) : ℝ) : ℂ) =
        e (g x₀) * ((∫ y in D.a..D.b, e (D.g y)) - e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)) := by
      rw [hDg2, integral_shift g a b x₀, KL.e_add]
      show e (g x₀) * (∫ y in (a - x₀)..(b - x₀), e (shift g x₀ y)) -
        e (1 / 8) * e (g x₀) / ((Real.sqrt (deriv (deriv g) x₀) : ℝ) : ℂ) =
        e (g x₀) * ((∫ y in (a - x₀)..(b - x₀), e (shift g x₀ y)) -
          e (1 / 8) / ((Real.sqrt (deriv (deriv g) x₀) : ℝ) : ℂ))
      ring
    rw [hint, norm_mul, PS.norm_e_one, one_mul]
    calc _ ≤ SP.Data.C₀ C₁ C₃ * (D.R₁ + D.R₂) := hcore
      _ ≤ |SP.Data.C₀ C₁ C₃| * (gkR₁ lam₂ a b x₀ + gkR₂ lam₂ lam₃ lam₄ a b) := by
          rw [hDR1, hDR2]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ (|SP.Data.C₀ C₁ C₃| + |C₂| + 1) * (gkR₁ lam₂ a b x₀ + gkR₂ lam₂ lam₃ lam₄ a b) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          linarith [abs_nonneg C₂]
  · -- the degenerate case: Lemma 3.2
    have hI := h32 a b lam₂ g hab hl2 (hg.of_le (by norm_num)) (fun x hx => by
      rw [iteratedDeriv_two]
      exact (h2 x hx).trans (le_abs_self _))
    have hR1 : s ≤ gkR₁ lam₂ a b x₀ := by
      unfold gkR₁
      change s ≤ minInv s (lam₂ * (x₀ - a)) + minInv s (lam₂ * (b - x₀))
      have h1 : 0 ≤ lam₂ * (x₀ - a) := by nlinarith [hx₀.1]
      have h2' : 0 ≤ lam₂ * (b - x₀) := by nlinarith [hx₀.2]
      push Not at hcase
      rcases le_or_gt s (x₀ - a) with hca | hca
      · have hcb := hcase hca
        have : minInv s (lam₂ * (b - x₀)) = s := by
          apply minInv_eq_D hs0 h2'
          rw [hinv]
          exact mul_lt_mul_of_pos_left hcb hl2
        rw [this]
        exact le_add_of_nonneg_left (minInv_nonneg hs0.le h1)
      · have : minInv s (lam₂ * (x₀ - a)) = s := by
          apply minInv_eq_D hs0 h1
          rw [hinv]
          exact mul_lt_mul_of_pos_left hca hl2
        rw [this]
        exact le_add_of_nonneg_right (minInv_nonneg hs0.le h2')
    calc ‖(∫ x in a..b, e (g x)) - e (1 / 8 + g x₀) / ((Real.sqrt (deriv (deriv g) x₀) : ℝ) : ℂ)‖
        ≤ ‖∫ x in a..b, e (g x)‖ + ‖e (1 / 8 + g x₀) / ((Real.sqrt (deriv (deriv g) x₀) : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ C₂ * s + s := add_le_add hI hmain
      _ ≤ (|C₂| + 1) * s := by
          have := le_abs_self C₂
          nlinarith
      _ ≤ (|C₂| + 1) * gkR₁ lam₂ a b x₀ := mul_le_mul_of_nonneg_left hR1 (by positivity)
      _ ≤ (|SP.Data.C₀ C₁ C₃| + |C₂| + 1) * (gkR₁ lam₂ a b x₀ + gkR₂ lam₂ lam₃ lam₄ a b) := by
          calc
            (|C₂| + 1) * gkR₁ lam₂ a b x₀ ≤
                (|SP.Data.C₀ C₁ C₃| + |C₂| + 1) * gkR₁ lam₂ a b x₀ :=
              mul_le_mul_of_nonneg_right
                (by linarith [abs_nonneg (SP.Data.C₀ C₁ C₃)]) hR1nn
            _ ≤ (|SP.Data.C₀ C₁ C₃| + |C₂| + 1) *
                (gkR₁ lam₂ a b x₀ + gkR₂ lam₂ lam₃ lam₄ a b) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hR2nn) (by positivity)

open GK34 in
/-- **Graham–Kolesnik, Lemma 3.4**, the case `g'' ≤ −λ₂ < 0`, by conjugation. -/
theorem gk_lemma34_neg_holds : gk_lemma34_neg := by
  obtain ⟨C, hC⟩ := gk_lemma34_holds
  refine ⟨C, ?_⟩
  intro a b x₀ lam₂ lam₃ lam₄ g hab hl2 hl3 hl4 hg h2 hx₀ hg'0 h3 h4
  have hneg := hC a b x₀ lam₂ lam₃ lam₄ (-g) hab hl2 hl3 hl4 hg.neg
    (fun x hx => by rw [iteratedDeriv_neg]; linarith [h2 x hx])
    hx₀ (by rw [deriv.neg, hg'0, neg_zero])
    (fun x hx => by rw [iteratedDeriv_neg, abs_neg]; exact h3 x hx)
    (fun x hx => by rw [iteratedDeriv_neg, abs_neg]; exact h4 x hx)
  rw [iteratedDeriv_neg, Pi.neg_apply] at hneg
  have hg2 : iteratedDeriv 2 g x₀ ≤ -lam₂ := h2 x₀ hx₀
  have habs : |iteratedDeriv 2 g x₀| = -iteratedDeriv 2 g x₀ := abs_of_neg (by linarith)
  rw [habs]
  -- the conjugation identity
  have hconj : (∫ x in a..b, e (-g x)) - e (1 / 8 + -g x₀) / ((Real.sqrt (-iteratedDeriv 2 g x₀) : ℝ) : ℂ) =
      starRingEnd ℂ ((∫ x in a..b, e (g x)) -
        e (-1 / 8 + g x₀) / ((Real.sqrt (-iteratedDeriv 2 g x₀) : ℝ) : ℂ)) := by
    rw [map_sub, map_div₀, Complex.conj_ofReal, ← GK32.integral_e_neg, ← KL.e_neg]
    congr 3
    ring
  have hneg' : ‖(∫ x in a..b, e (-g x)) -
      e (1 / 8 + -g x₀) / ((Real.sqrt (-iteratedDeriv 2 g x₀) : ℝ) : ℂ)‖ ≤
      C * (gkR₁ lam₂ a b x₀ + gkR₂ lam₂ lam₃ lam₄ a b) := by
    simpa using hneg
  rw [hconj, Complex.norm_conj] at hneg'
  exact hneg'

end LeanProofs.IntegerPoints
