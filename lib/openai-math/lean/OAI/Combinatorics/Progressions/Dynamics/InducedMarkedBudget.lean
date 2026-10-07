import OAI.Combinatorics.Progressions.Estimates.CommonInducedCorrelation

namespace OAI

section

namespace Erdos3

open scoped NNReal

def inducedMarkedLogBudget (C A B : ℕ) (p : ℝ) : ℝ :=
  let q := 6 * p + (p + C) ^ C + 2
  let a := (q + A) ^ A
  let t := a + q + 8 * p + 3
  let b := (t + B) ^ B
  2 * (b + 2 * a + 8 * p + (p + 3) ^ 2 + q + 10) + 132

theorem exists_inducedMarkedLogBudget_bound (C A B : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p → inducedMarkedLogBudget C A B p ≤ (p + N) ^ N := by
  let q : Polynomial ℕ := 6 * Polynomial.X + (Polynomial.X + Polynomial.C C) ^ C + 2
  let a := (q + Polynomial.C A) ^ A
  let t := a + q + 8 * Polynomial.X + 3
  let b := (t + Polynomial.C B) ^ B
  let P : Polynomial ℕ := 2 * (b + 2 * a + 8 * Polynomial.X + (Polynomial.X + 3) ^ 2 + q + 10) + 132
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = inducedMarkedLogBudget C A B p := by
    simp [P, q, a, t, b, inducedMarkedLogBudget, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  rw [← heq]
  exact hbound p hp

theorem exists_inducedMarkedLipschitzBound_exp_bound (s u C : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (d e : ℕ) (p : ℝ) (R : ℝ≥0),
      0 ≤ p → (d : ℝ) ≤ p → (e : ℝ) ≤ p → (R : ℝ) ≤ Real.exp ((p + C) ^ C) →
      (inducedMarkedLipschitzBound s d u e p R : ℝ) ≤ Real.exp ((p + N) ^ N) := by
  obtain ⟨A, _, hsource⟩ := exists_bchBoxMetricConstant_exp_bound (s + 1) 1
  obtain ⟨B, _, htarget⟩ := exists_bchBoxMetricConstant_exp_bound u 1
  obtain ⟨N, hN, hbudget⟩ := exists_inducedMarkedLogBudget_bound C A B
  refine ⟨N, hN, ?_⟩
  intro d e p R hp hd he hR
  apply le_trans ?_ (Real.exp_le_exp.mpr (hbudget p hp))
  let r := (p + C) ^ C
  let q := 6 * p + r + 2
  let a := (q + A) ^ A
  let t := a + q + 8 * p + 3
  let b := (t + B) ^ B
  let W := b + 2 * a + 8 * p + (p + 3) ^ 2 + q + 10
  let H := ⌈Real.exp p⌉₊
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hpq : p + 1 ≤ q := by dsimp [q]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hH : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)
  have hplus (x : ℝ) (hx : 0 ≤ x) : Real.exp x + 1 ≤ Real.exp (x + 1) := by
    calc
      _ ≤ Real.exp x * 2 := by linarith [Real.one_le_exp hx]
      _ ≤ Real.exp x * Real.exp 1 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hRplus : ((R + 1 : ℝ≥0) : ℝ) ≤ Real.exp (r + 1) := by
    change (R : ℝ) + 1 ≤ Real.exp (r + 1)
    exact (add_le_add hR (le_refl (1 : ℝ))).trans (hplus r hr)
  have hRq : (R : ℝ) ≤ Real.exp q := hR.trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  have hbox (D : ℝ≥0) (hD : (D : ℝ) ≤ Real.exp q) :
      bchBoxCoordinateBound (s + 1) d H D ≤ Real.exp a := by
    apply (bchBoxCoordinateBound_le_bchBoxMetricConstant (s + 1) d H D).trans
    apply hsource d H D q hq (hd.trans (by linarith)) hH
    simpa only [pow_one] using hD.trans (Real.exp_le_exp.mpr (by linarith : q ≤ q + 2))
  have hlog (D : ℝ≥0) (hD : (D : ℝ) ≤ Real.exp q) :
      (bchLogMetricConstant (s + 1) d H D : ℝ) ≤ Real.exp (a + 1) := by
    change bchBoxCoordinateBound (s + 1) d H D + 1 ≤ _
    exact (add_le_add (hbox D hD) (le_refl (1 : ℝ))).trans (hplus a ha)
  have hC0 : (bchLogMetricConstant (s + 1) d H 1 : ℝ) ≤ Real.exp (a + 1) :=
    hlog 1 (Real.one_le_exp hq)
  have hcoord : (phaseBandCoordinateConstant (s + 1) d H R : ℝ) ≤ Real.exp (2 * (a + 1)) := by
    change (bchLogMetricConstant (s + 1) d H R : ℝ) * (bchLogMetricConstant (s + 1) d H 1 : ℝ) ≤ _
    calc
      _ ≤ Real.exp (a + 1) * Real.exp (a + 1) :=
        mul_le_mul (hlog R hRq) hC0 (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hinput : Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ) ≤ Real.exp q := by
    calc
      _ ≤ Real.exp (5 * p) * Real.exp (r + 1) := mul_le_mul_of_nonneg_left hRplus (Real.exp_nonneg _)
      _ = Real.exp (5 * p + (r + 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [q]; linarith)
  have hret : (markedRetractionBoxConstant s d H p (R + 1) : ℝ) ≤ Real.exp (a + 5 * p) := by
    change bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ)) * Real.exp (5 * p) ≤ _
    calc
      _ ≤ Real.exp a * Real.exp (5 * p) := mul_le_mul_of_nonneg_right
        (hbox ⟨Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ),
          mul_nonneg (Real.exp_nonneg _) (R + 1).coe_nonneg⟩ hinput) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hT : (markedEvaluationBoxRadius s d H p (R + 1) : ℝ) ≤ Real.exp t := by
    change Real.exp (2 * p) * (markedRetractionBoxConstant s d H p (R + 1) : ℝ) *
      ((R + 1 : ℝ≥0) : ℝ) + 1 ≤ _
    calc
      _ ≤ Real.exp (2 * p) * Real.exp (a + 5 * p) * Real.exp (r + 1) + 1 := by gcongr
      _ = Real.exp (a + 7 * p + r + 1) + 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (a + 7 * p + r + 1 + 1) := hplus _ (by positivity)
      _ ≤ Real.exp t := Real.exp_le_exp.mpr (by dsimp [t, q]; linarith)
  have htargetMetric : (bchBoxMetricConstant u e H (markedEvaluationBoxRadius s d H p (R + 1)) : ℝ) ≤
      Real.exp b := by
    apply htarget e H _ t ht (he.trans (by linarith)) (hH.trans (Real.exp_le_exp.mpr hqt))
    simpa only [pow_one] using hT.trans (Real.exp_le_exp.mpr (by linarith : t ≤ t + 2))
  have hlocal : (markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ) ≤
      Real.exp (b + a + 8 * p) := by
    change Real.exp p * (bchBoxMetricConstant u e H (markedEvaluationBoxRadius s d H p (R + 1)) : ℝ) *
      Real.exp (2 * p) * (markedRetractionBoxConstant s d H p (R + 1) : ℝ) ≤ _
    calc
      _ ≤ Real.exp p * Real.exp b * Real.exp (2 * p) * Real.exp (a + 5 * p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hcoordW := hcoord.trans (Real.exp_le_exp.mpr (show 2 * (a + 1) ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hlocalW := hlocal.trans (Real.exp_le_exp.mpr (show b + a + 8 * p ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hC0W := hC0.trans (Real.exp_le_exp.mpr (show a + 1 ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hphaseW : Real.exp ((p + 3) ^ 2) ≤ Real.exp W := Real.exp_le_exp.mpr (by dsimp [W]; linarith)
  have honeW : 1 ≤ Real.exp W := Real.one_le_exp hW
  change 2 * (2 * (phaseBandCoordinateConstant (s + 1) d H R : ℝ) *
      (markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ) +
      16 * (Real.exp ((p + 3) ^ 2) + (bchLogMetricConstant (s + 1) d H 1 : ℝ) +
        (phaseBandCoordinateConstant (s + 1) d H R : ℝ) + 1)) ≤ Real.exp (2 * W + 132)
  calc
    _ ≤ 2 * (2 * Real.exp W * Real.exp W +
        16 * (Real.exp W + Real.exp W + Real.exp W + Real.exp W)) := by gcongr
    _ = 4 * Real.exp (2 * W) + 128 * Real.exp W := by
      rw [show 2 * W = W + W by ring, Real.exp_add W W]
      ring
    _ ≤ 132 * Real.exp (2 * W) := by
      have hexp : Real.exp W ≤ Real.exp (2 * W) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ ≤ Real.exp 132 * Real.exp (2 * W) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (132 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
