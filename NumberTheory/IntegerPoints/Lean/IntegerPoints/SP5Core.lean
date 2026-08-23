import IntegerPoints.SP4Assembly
import IntegerPoints.GKStatements

/-!
# Stationary phase, part 5: the core estimate in the normalised setting

For `D : SP.Data` with `a ≤ −λ₂^{-1/2}` and `λ₂^{-1/2} ≤ b` (the regime (3.2.2) of
Graham–Kolesnik), we prove

`‖∫_a^b e(g) − e(1/8)/√(g''(0))‖ ≤ C₀ (R₁ + R₂)`

with `R₁ = 1/(λ₂|a|) + 1/(λ₂ b)`, `R₂ = (b − a) λ₄ λ₂⁻² + (b − a) λ₃² λ₂⁻³`, and an absolute
constant `C₀` built from the constants of Lemmas 3.1 and 3.3.  The pieces:

* `∫_a^b e(g) = ∫_a^b e(q) + ∫_a^b F` with `F = e(q)(e(r) − 1)` (`SP4Assembly.main_bound`);
* `∫_a^b e(q) = ∫_{−X}^{X} e(q) + (rest)` with `X = min(|a|, b)`; the symmetric integral is the
  Fresnel integral of Lemma 3.3 with `A = g''(0)/2`, the rest is bounded by Lemma 3.1;
* `δ = λ₃^{-1/3}` in `K₂(δ)` gives `K₂ ≪ λ₃/λ₂ + (b − a)λ₄/λ₂`;
* the term `λ₃/λ₂²` is absorbed by `R₁ + (b − a)λ₃²/λ₂³` (AM–GM, using `(b − a) ≥ |a|`).
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace SP

namespace Data

variable (D : Data)

/-- `R₁` in the normalised setting. -/
noncomputable def R₁ : ℝ := 1 / (D.lam₂ * |D.a|) + 1 / (D.lam₂ * D.b)

/-- `R₂`. -/
noncomputable def R₂ : ℝ :=
  (D.b - D.a) * D.lam₄ * D.lam₂ ^ (-(2 : ℝ)) + (D.b - D.a) * D.lam₃ ^ 2 * D.lam₂ ^ (-(3 : ℝ))

theorem R₁_nonneg : 0 ≤ D.R₁ := by
  unfold R₁
  have := D.hlam₂
  have := D.hb
  positivity

theorem R₂_eq : D.R₂ = (D.b - D.a) * D.lam₄ / D.lam₂ ^ 2 + (D.b - D.a) * D.lam₃ ^ 2 / D.lam₂ ^ 3 := by
  unfold R₂
  rw [Real.rpow_neg D.hlam₂.le, Real.rpow_neg D.hlam₂.le]
  norm_num
  ring

theorem R₂_nonneg : 0 ≤ D.R₂ := by
  rw [R₂_eq]
  have := D.hlam₂
  have := D.hlam₃
  have := D.hlam₄
  have : 0 ≤ D.b - D.a := by linarith [D.ha, D.hb]
  positivity

/-- `δ = λ₃^{-1/3}` makes `λ₃² δ³ = λ₃` and `δ⁻³ = λ₃`. -/
theorem delta_facts :
    let δ := D.lam₃ ^ (-(1 : ℝ) / 3)
    0 < δ ∧ D.lam₃ ^ 2 * δ ^ 3 = D.lam₃ ∧ 1 / δ ^ 3 = D.lam₃ := by
  intro δ
  have h3 := D.hlam₃
  have hδ : δ = D.lam₃ ^ (-(1 : ℝ) / 3) := rfl
  have hδ3 : δ ^ 3 = D.lam₃ ^ (-(1 : ℝ)) := by
    rw [hδ, ← Real.rpow_natCast, ← Real.rpow_mul h3.le]
    norm_num
  have hpos : 0 < δ := by rw [hδ]; positivity
  refine ⟨hpos, ?_, ?_⟩
  · rw [hδ3, Real.rpow_neg_one]
    field_simp
  · rw [hδ3, Real.rpow_neg_one, one_div, inv_inv]

/-- `K₂(λ₃^{-1/3}) = (2/3 + π/2 + 6/π) λ₃/λ₂ + (b − a) λ₄/(12 λ₂)`. -/
theorem K₂_delta :
    D.K₂ (D.lam₃ ^ (-(1 : ℝ) / 3)) =
      (2 / 3 + π / 2 + 6 / π) * (D.lam₃ / D.lam₂) + (D.b - D.a) * D.lam₄ / (12 * D.lam₂) := by
  obtain ⟨hδ, h1, h2⟩ := D.delta_facts
  unfold K₂
  have hl2 := D.hlam₂
  have hpi := Real.pi_pos
  have hδ3 : 0 < (D.lam₃ ^ (-(1 : ℝ) / 3)) ^ 3 := by positivity
  rw [show π * D.lam₃ ^ 2 * (D.lam₃ ^ (-(1 : ℝ) / 3)) ^ 3 / (2 * D.lam₂) =
      π * (D.lam₃ ^ 2 * (D.lam₃ ^ (-(1 : ℝ) / 3)) ^ 3) / (2 * D.lam₂) by ring, h1,
    show 6 / (π * D.lam₂ * (D.lam₃ ^ (-(1 : ℝ) / 3)) ^ 3) =
      6 / (π * D.lam₂) * (1 / (D.lam₃ ^ (-(1 : ℝ) / 3)) ^ 3) by field_simp, h2]
  field_simp
  ring

/-- The AM–GM absorption: `λ₃/λ₂² ≤ R₁ + (b − a) λ₃²/λ₂³`. -/
theorem lam3_div_le : D.lam₃ / D.lam₂ ^ 2 ≤ D.R₁ + (D.b - D.a) * D.lam₃ ^ 2 / D.lam₂ ^ 3 := by
  have hl2 := D.hlam₂
  have hl3 := D.hlam₃
  have ha := D.ha
  have hb := D.hb
  set U : ℝ := 1 / (D.lam₂ * (D.b - D.a)) with hU
  set V : ℝ := (D.b - D.a) * D.lam₃ ^ 2 / D.lam₂ ^ 3 with hV
  have hba : 0 < D.b - D.a := by linarith
  have hU0 : 0 < U := by positivity
  have hV0 : 0 ≤ V := by positivity
  have hUV : U * V = (D.lam₃ / D.lam₂ ^ 2) ^ 2 := by
    rw [hU, hV]
    field_simp
    ring
  have hUR : U ≤ D.R₁ := by
    unfold R₁
    rw [hU, abs_of_neg ha]
    have h1 : 1 / (D.lam₂ * (D.b - D.a)) ≤ 1 / (D.lam₂ * -D.a) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have h2 : 0 ≤ 1 / (D.lam₂ * D.b) := by positivity
    linarith
  -- `x² = UV ≤ ((U+V)/2)²` so `x ≤ (U+V)/2 ≤ U + V`
  have hx0 : 0 ≤ D.lam₃ / D.lam₂ ^ 2 := by positivity
  have hsq : (D.lam₃ / D.lam₂ ^ 2) ^ 2 ≤ ((U + V) / 2) ^ 2 := by
    rw [← hUV]
    nlinarith [sq_nonneg (U - V)]
  have hle : D.lam₃ / D.lam₂ ^ 2 ≤ (U + V) / 2 :=
    (pow_le_pow_iff_left₀ hx0 (by positivity) two_ne_zero).1 hsq
  linarith

/-! ### The Fresnel part `∫_a^b e(q)` -/

/-- `∫_a^b e(q) = e(1/8)/√(g''(0)) + O(1/(λ₂ X))`, `X = min(|a|, b)`, from Lemmas 3.1 and 3.3. -/
theorem fresnel_part {C₁ C₃ : ℝ}
    (h31 : ∀ (a b lam : ℝ) (f g : ℝ → ℝ), a ≤ b → 0 < lam → ContDiff ℝ 2 f → ContDiff ℝ 2 g →
      (MonotoneOn (fun x => g x / deriv f x) (Set.Icc a b) ∨
        AntitoneOn (fun x => g x / deriv f x) (Set.Icc a b)) →
      (∀ x ∈ Set.Icc a b, deriv f x ≠ 0 ∧ lam * |g x| ≤ |deriv f x|) →
      ‖∫ x in a..b, (g x : ℂ) * e (f x)‖ ≤ C₁ / lam)
    (h33 : ∀ A X : ℝ, 0 < A → 0 < X →
      ‖(∫ x in (-X)..X, e (A * x ^ 2)) - e (1 / 8) / ((Real.sqrt (2 * A) : ℝ) : ℂ)‖ ≤ C₃ / (A * X)) :
    ‖(∫ x in D.a..D.b, e (D.q x)) - e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)‖ ≤
      (2 * C₃ + 2 * C₁) * D.R₁ := by
  have hg20 := D.g2_zero_pos
  have hl2 := D.hlam₂
  have ha := D.ha
  have hb := D.hb
  set A : ℝ := D.g2 0 / 2 with hA
  have hA0 : 0 < A := by positivity
  have hqA : ∀ x, D.q x = A * x ^ 2 := fun x => by unfold q; rw [hA]; ring
  have h2A : Real.sqrt (2 * A) = Real.sqrt (D.g2 0) := by rw [hA]; ring_nf
  set X : ℝ := min (-D.a) D.b with hX
  have hX0 : 0 < X := lt_min (by linarith) hb
  have hXa : X ≤ -D.a := min_le_left _ _
  have hXb : X ≤ D.b := min_le_right _ _
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun x => e (D.q x)) volume p q :=
    fun p q => (PS.continuous_e_comp D.continuous_q).intervalIntegrable p q
  -- the symmetric part
  have hsym := h33 A X hA0 hX0
  have hsym' : ‖(∫ x in (-X)..X, e (D.q x)) - e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)‖ ≤
      C₃ / (A * X) := by
    rw [← h2A]
    convert hsym using 3
    exact integral_congr fun x _ => by rw [hqA]
  -- the two rests, by Lemma 3.1 with weight `1`
  have hq2 : ContDiff ℝ 2 D.q := by unfold q; fun_prop
  have hderiv_q : ∀ x, deriv D.q x = D.g2 0 * x := fun x => (D.hasDerivAt_q x).deriv
  have hrest_right : ‖∫ x in X..D.b, e (D.q x)‖ ≤ C₁ / (D.g2 0 * X) := by
    have := h31 X D.b (D.g2 0 * X) D.q (fun _ => 1) hXb (by positivity) hq2 contDiff_const
      (Or.inr (by
        intro x hx y hy hxy
        simp only [hderiv_q]
        apply one_div_le_one_div_of_le (by nlinarith [hx.1])
        exact mul_le_mul_of_nonneg_left hxy hg20.le))
      (fun x hx => by
        rw [hderiv_q]
        refine ⟨by nlinarith [hx.1], ?_⟩
        rw [abs_one, mul_one, abs_of_pos (by nlinarith [hx.1])]
        exact mul_le_mul_of_nonneg_left hx.1 hg20.le)
    simpa using this
  have hrest_left : ‖∫ x in D.a..(-X), e (D.q x)‖ ≤ C₁ / (D.g2 0 * X) := by
    have := h31 D.a (-X) (D.g2 0 * X) D.q (fun _ => 1) (by linarith) (by positivity) hq2 contDiff_const
      (Or.inr (by
        intro x hx y hy hxy
        simp only [hderiv_q]
        have hx0 : x < 0 := by linarith [hx.2]
        have hy0 : y < 0 := by linarith [hy.2]
        rw [div_le_div_iff_of_neg (by nlinarith) (by nlinarith)]
        nlinarith))
      (fun x hx => by
        rw [hderiv_q]
        have hx0 : x ≤ -X := hx.2
        refine ⟨by nlinarith, ?_⟩
        rw [abs_one, mul_one, abs_of_neg (by nlinarith)]
        nlinarith)
    simpa using this
  -- assemble
  have hsplit : ∫ x in D.a..D.b, e (D.q x) =
      (∫ x in D.a..(-X), e (D.q x)) + (∫ x in (-X)..X, e (D.q x)) + ∫ x in X..D.b, e (D.q x) := by
    rw [integral_add_adjacent_intervals (hint _ _) (hint _ _),
      integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hC1 : 0 ≤ C₁ := by
    have := hrest_right
    have : 0 ≤ C₁ / (D.g2 0 * X) := (norm_nonneg _).trans this
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by
      have : 0 < D.g2 0 * X := by positivity
      linarith [h.2])
  have hC3 : 0 ≤ C₃ := by
    have : 0 ≤ C₃ / (A * X) := (norm_nonneg _).trans hsym
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by
      have : 0 < A * X := by positivity
      linarith [h.2])
  have hXR : 1 / (D.lam₂ * X) ≤ D.R₁ := by
    unfold R₁
    rw [abs_of_neg ha]
    rcases le_or_gt (-D.a) D.b with h | h
    · have hXeq : X = -D.a := min_eq_left h
      rw [hXeq]
      have : 0 ≤ 1 / (D.lam₂ * D.b) := by positivity
      linarith
    · have hXeq : X = D.b := min_eq_right h.le
      rw [hXeq]
      have : 0 ≤ 1 / (D.lam₂ * -D.a) := by positivity
      linarith
  have e1 : C₃ / (A * X) ≤ 2 * C₃ * (1 / (D.lam₂ * X)) := by
    rw [hA]
    have h2 := D.g2_pos_at_zero
    calc C₃ / (D.g2 0 / 2 * X) = 2 * C₃ * (1 / (D.g2 0 * X)) := by field_simp
      _ ≤ 2 * C₃ * (1 / (D.lam₂ * X)) := by
          gcongr
  have e2 : C₁ / (D.g2 0 * X) ≤ C₁ * (1 / (D.lam₂ * X)) := by
    have h2 := D.g2_pos_at_zero
    calc C₁ / (D.g2 0 * X) = C₁ * (1 / (D.g2 0 * X)) := by ring
      _ ≤ C₁ * (1 / (D.lam₂ * X)) := by gcongr
  rw [hsplit]
  calc ‖(∫ x in D.a..(-X), e (D.q x)) + (∫ x in (-X)..X, e (D.q x)) + (∫ x in X..D.b, e (D.q x)) -
        e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)‖
      = ‖(∫ x in D.a..(-X), e (D.q x)) +
          ((∫ x in (-X)..X, e (D.q x)) - e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)) +
          (∫ x in X..D.b, e (D.q x))‖ := by ring_nf
    _ ≤ ‖∫ x in D.a..(-X), e (D.q x)‖ +
        ‖(∫ x in (-X)..X, e (D.q x)) - e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)‖ +
        ‖∫ x in X..D.b, e (D.q x)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ C₁ / (D.g2 0 * X) + C₃ / (A * X) + C₁ / (D.g2 0 * X) :=
        add_le_add (add_le_add hrest_left hsym') hrest_right
    _ ≤ C₁ * (1 / (D.lam₂ * X)) + 2 * C₃ * (1 / (D.lam₂ * X)) + C₁ * (1 / (D.lam₂ * X)) :=
        add_le_add (add_le_add e2 e1) e2
    _ = (2 * C₃ + 2 * C₁) * (1 / (D.lam₂ * X)) := by ring
    _ ≤ (2 * C₃ + 2 * C₁) * D.R₁ := by gcongr

/-! ### The core estimate -/

/-- The absolute constant of the core estimate, from the constants `C₁` (Lemma 3.1) and
`C₃` (Lemma 3.3). -/
noncomputable def C₀ (C₁ C₃ : ℝ) : ℝ :=
  2 * C₃ + 2 * C₁ + 1 / π + (1 / (2 * π)) * (3 + 2 / 3 + π / 2 + 6 / π + 1)

/-- **The core estimate** in the normalised setting:
`‖∫_a^b e(g) − e(1/8)/√(g''(0))‖ ≤ C₀ (R₁ + R₂)`. -/
theorem core_bound {C₁ C₃ : ℝ}
    (h31 : ∀ (a b lam : ℝ) (f g : ℝ → ℝ), a ≤ b → 0 < lam → ContDiff ℝ 2 f → ContDiff ℝ 2 g →
      (MonotoneOn (fun x => g x / deriv f x) (Set.Icc a b) ∨
        AntitoneOn (fun x => g x / deriv f x) (Set.Icc a b)) →
      (∀ x ∈ Set.Icc a b, deriv f x ≠ 0 ∧ lam * |g x| ≤ |deriv f x|) →
      ‖∫ x in a..b, (g x : ℂ) * e (f x)‖ ≤ C₁ / lam)
    (h33 : ∀ A X : ℝ, 0 < A → 0 < X →
      ‖(∫ x in (-X)..X, e (A * x ^ 2)) - e (1 / 8) / ((Real.sqrt (2 * A) : ℝ) : ℂ)‖ ≤ C₃ / (A * X)) :
    ‖(∫ x in D.a..D.b, e (D.g x)) - e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)‖ ≤
      C₀ C₁ C₃ * (D.R₁ + D.R₂) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hl2 := D.hlam₂
  have hl3 := D.hlam₃
  have hl4 := D.hlam₄
  have ha := D.ha
  have hb := D.hb
  have hba : 0 ≤ D.b - D.a := by linarith
  -- split `e(g) = e(q) + F`
  have hsplit : ∫ x in D.a..D.b, e (D.g x) = (∫ x in D.a..D.b, e (D.q x)) + ∫ x in D.a..D.b, D.F x := by
    rw [← intervalIntegral.integral_add ((PS.continuous_e_comp D.continuous_q).intervalIntegrable _ _)
      (D.continuous_F.intervalIntegrable _ _)]
    apply integral_congr
    intro x _
    unfold F
    rw [D.g_eq_q_add_r, KL.e_add]
    ring
  have hF := D.fresnel_part h31 h33
  obtain ⟨hδ, -, -⟩ := D.delta_facts
  have hM := D.main_bound hδ
  rw [D.K₂_delta] at hM
  have hAM := D.lam3_div_le
  have hR2 := D.R₂_eq
  have hR1 := D.R₁_nonneg
  -- the constant bookkeeping
  have hC1 : 0 ≤ C₁ := by
    have := h31 0 1 1 (fun x => x) (fun _ => 1) zero_le_one one_pos contDiff_id contDiff_const
      (Or.inl (by
        intro x _ y _ _
        simp))
      (fun x _ => by simp)
    have h0 : 0 ≤ C₁ / 1 := (norm_nonneg _).trans this
    simpa using h0
  have hC3 : 0 ≤ C₃ := by
    have := h33 1 1 one_pos one_pos
    have h0 : 0 ≤ C₃ / (1 * 1) := (norm_nonneg _).trans this
    simpa using h0
  -- `1/(πλ₂|a|) + 1/(πλ₂ b) = R₁/π`
  have hend : 1 / (π * D.lam₂ * |D.a|) + 1 / (π * D.lam₂ * D.b) = (1 / π) * D.R₁ := by
    unfold R₁
    rw [abs_of_neg ha]
    field_simp
    ring
  -- the `B₂` and `K₂` terms
  have hmid : 1 / (2 * π * D.lam₂) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) * D.B₂ +
      ((2 / 3 + π / 2 + 6 / π) * (D.lam₃ / D.lam₂) + (D.b - D.a) * D.lam₄ / (12 * D.lam₂))) ≤
      (1 / (2 * π)) * ((3 + 2 / 3 + π / 2 + 6 / π) * (D.R₁ + D.R₂) + D.R₂) := by
    unfold B₂
    have e1 : 1 / (2 * π * D.lam₂) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) *
        (D.lam₄ / (6 * D.lam₂) + 3 * D.lam₃ ^ 2 / (4 * D.lam₂ ^ 2)) +
        ((2 / 3 + π / 2 + 6 / π) * (D.lam₃ / D.lam₂) + (D.b - D.a) * D.lam₄ / (12 * D.lam₂))) =
        (1 / (2 * π)) * ((2 + (2 / 3 + π / 2 + 6 / π)) * (D.lam₃ / D.lam₂ ^ 2) +
          (D.b - D.a) * D.lam₄ / D.lam₂ ^ 2 * (1 / 6 + 1 / 12) +
          (3 / 4) * ((D.b - D.a) * D.lam₃ ^ 2 / D.lam₂ ^ 3)) := by
      field_simp
      ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hc : 0 ≤ 2 + (2 / 3 + π / 2 + 6 / π) := by positivity
    have t1 : (2 + (2 / 3 + π / 2 + 6 / π)) * (D.lam₃ / D.lam₂ ^ 2) ≤
        (2 + (2 / 3 + π / 2 + 6 / π)) * (D.R₁ + (D.b - D.a) * D.lam₃ ^ 2 / D.lam₂ ^ 3) :=
      mul_le_mul_of_nonneg_left hAM hc
    have t2 : (D.b - D.a) * D.lam₃ ^ 2 / D.lam₂ ^ 3 ≤ D.R₂ := by
      rw [hR2]
      have : 0 ≤ (D.b - D.a) * D.lam₄ / D.lam₂ ^ 2 := by positivity
      linarith
    have t3 : (D.b - D.a) * D.lam₄ / D.lam₂ ^ 2 * (1 / 6 + 1 / 12) +
        (3 / 4) * ((D.b - D.a) * D.lam₃ ^ 2 / D.lam₂ ^ 3) ≤ D.R₂ := by
      rw [hR2]
      have h1 : 0 ≤ (D.b - D.a) * D.lam₄ / D.lam₂ ^ 2 := by positivity
      have h2 : 0 ≤ (D.b - D.a) * D.lam₃ ^ 2 / D.lam₂ ^ 3 := by positivity
      nlinarith
    have hR2' := D.R₂_nonneg
    nlinarith
  rw [hsplit]
  calc ‖(∫ x in D.a..D.b, e (D.q x)) + (∫ x in D.a..D.b, D.F x) -
        e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)‖
      = ‖((∫ x in D.a..D.b, e (D.q x)) - e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)) +
          ∫ x in D.a..D.b, D.F x‖ := by ring_nf
    _ ≤ ‖(∫ x in D.a..D.b, e (D.q x)) - e (1 / 8) / ((Real.sqrt (D.g2 0) : ℝ) : ℂ)‖ +
        ‖∫ x in D.a..D.b, D.F x‖ := norm_add_le _ _
    _ ≤ (2 * C₃ + 2 * C₁) * D.R₁ +
        (1 / (π * D.lam₂ * |D.a|) + 1 / (π * D.lam₂ * D.b) +
          1 / (2 * π * D.lam₂) * (2 * D.lam₃ / D.lam₂ + (D.b - D.a) * D.B₂ +
            ((2 / 3 + π / 2 + 6 / π) * (D.lam₃ / D.lam₂) + (D.b - D.a) * D.lam₄ / (12 * D.lam₂)))) :=
        add_le_add hF hM
    _ ≤ (2 * C₃ + 2 * C₁) * D.R₁ + ((1 / π) * D.R₁ +
        (1 / (2 * π)) * ((3 + 2 / 3 + π / 2 + 6 / π) * (D.R₁ + D.R₂) + D.R₂)) := by
        rw [hend]
        gcongr
    _ ≤ C₀ C₁ C₃ * (D.R₁ + D.R₂) := by
        unfold C₀
        have hR2' := D.R₂_nonneg
        have h1 : 0 ≤ 1 / π := by positivity
        have h2 : 0 ≤ 1 / (2 * π) := by positivity
        have h3 : 0 ≤ 3 + 2 / 3 + π / 2 + 6 / π := by positivity
        nlinarith [mul_nonneg (add_nonneg hC1 hC3) hR2', mul_nonneg h1 hR2', mul_nonneg h2 hR2']

end Data

end SP

end LeanProofs.IntegerPoints
