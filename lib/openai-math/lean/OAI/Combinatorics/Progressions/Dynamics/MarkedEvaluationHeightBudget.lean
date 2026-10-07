import OAI.Combinatorics.Progressions.Estimates.MarkedEvaluationJointBounds

namespace OAI

section

namespace Erdos3

theorem markedQuotient_source_height_bound (s n a d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    let T := lieTreeHeight n H s
    let U := max T (s + 1)
    (((a + 1) * (rationalSolveHeight d T * T) ^ a : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ ((6 * s + 4) * 11)) ∧
      (rationalLieStructureHeight a (max U (rationalSolveHeight d U)) : ℝ) ≤
        Real.exp ((p + 2) ^ ((6 * s + 4) * 11)) := by
  let k := 6 * s + 2
  let K := (p + 2) ^ k
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  have hpK : p ≤ K := le_power_budget hp (by dsimp [k]; omega)
  have hT : (T : ℝ) ≤ Real.exp K := lieTreeHeight_le_exp n H s hp hn hH
  have hU : (U : ℝ) ≤ Real.exp K := by
    change ((max T (s + 1) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max]
    refine max_le hT ?_
    calc
      (s + 1 : ℕ) ≤ p := hs
      _ ≤ p + 1 := by linarith
      _ ≤ Real.exp p := Real.add_one_le_exp p
      _ ≤ Real.exp K := Real.exp_le_exp.mpr hpK
  have hB₀ := embedding_coordinate_height_budget a d T T
    (show 0 ≤ K by dsimp [K]; positivity) (ha.trans hpK) (hd.trans hpK) hT hT
  have hB := exponential_budget_comp hp (show 0 ≤ K by dsimp [K]; positivity) k 8 le_rfl hB₀
  have hC₀ := rationalLieStructureHeight_inverse_budget a d U
    (show 0 ≤ K by dsimp [K]; positivity) (ha.trans hpK) (hd.trans hpK) hU
  have hC := exponential_budget_comp hp (show 0 ≤ K by dsimp [K]; positivity) k 11 le_rfl hC₀
  refine ⟨hB.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) ?_)), ?_⟩
  · dsimp [k]
    omega
  · simpa only [k, show 6 * s + 2 + 2 = 6 * s + 4 by omega] using hC

theorem markedQuotient_projection_height_bound (m B C v : ℕ) (hv : 1 ≤ v)
    {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ v))
    (hC : (C : ℝ) ≤ Real.exp ((p + 2) ^ v)) :
    (rationalKernelHeight m B : ℝ) ≤ Real.exp ((p + 2) ^ ((v + 2) * 7)) ∧
      ((max 1 (max C (rationalKernelHeight m B)) : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ ((v + 2) * 7)) := by
  have hQ₀ := rationalKernelHeight_le_budget m B
    (show 0 ≤ (p + 2) ^ v by positivity) (hm.trans (le_power_budget hp hv)) hB
  have hQ := exponential_budget_comp hp (show 0 ≤ (p + 2) ^ v by positivity) v 7 le_rfl hQ₀
  refine ⟨hQ, ?_⟩
  rw [Nat.cast_max, Nat.cast_max, Nat.cast_one]
  refine max_le (Real.one_le_exp (by positivity)) (max_le ?_ hQ)
  exact hC.trans (Real.exp_le_exp.mpr
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by omega : v ≤ (v + 2) * 7)))

theorem markedQuotient_final_height_bound (d q B Q J w : ℕ) (hw : 1 ≤ w)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hJ : (J : ℝ) ≤ Real.exp ((p + 2) ^ w)) :
    ((max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
      ((d + 1) * (B * Q) ^ d) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ ((w + 2) * 11)) := by
  let W := (p + 2) ^ w
  have hpW : p ≤ W := le_power_budget hp hw
  have hCQ₀ := rationalLieStructureHeight_inverse_budget d q J
    (show 0 ≤ W by dsimp [W]; positivity) (hd.trans hpW) (hq.trans hpW) hJ
  have hCQ := exponential_budget_comp hp (show 0 ≤ W by dsimp [W]; positivity) w 11 le_rfl hCQ₀
  have hproduct : ((B * Q : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 1)) := by
    rw [Nat.cast_mul]
    calc
      (B : ℝ) * Q ≤ Real.exp W * Real.exp W :=
        mul_le_mul hB hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (W + W) := (Real.exp_add W W).symm
      _ ≤ Real.exp ((p + 2) ^ (w + 1)) := by
        apply Real.exp_le_exp.mpr
        calc
          W + W = 2 * W := by ring
          _ ≤ (p + 2) * W := mul_le_mul_of_nonneg_right (by linarith) (by dsimp [W]; positivity)
          _ = (p + 2) ^ (w + 1) := by dsimp [W]; rw [pow_succ]; ring
  have hLQ := rational_sum_cost_le_exp d (B * Q) hp (w + 1) 1 hproduct
    (by simpa only [pow_one] using hd.trans (by linarith : p ≤ p + 2))
  rw [Nat.cast_max]
  refine max_le hCQ (hLQ.trans (Real.exp_le_exp.mpr ?_))
  exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by omega : w + 1 + 1 + 1 ≤ (w + 2) * 11)

theorem markedQuotientHeight_le_exp (s n a d m q H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (markedQuotientHeight s n a d m q H : ℝ) ≤ Real.exp ((p + 2) ^ (5082 * s + 3564)) := by
  let v := (6 * s + 4) * 11
  let w := (v + 2) * 7
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  let J := max 1 (max C Q)
  obtain ⟨hB, hC⟩ := markedQuotient_source_height_bound s n a d H hp hs hn ha hd hH
  obtain ⟨hQ, hJ⟩ := markedQuotient_projection_height_bound m B C v
    (by dsimp [v]; omega) hp hm hB hC
  have hBW : (B : ℝ) ≤ Real.exp ((p + 2) ^ w) := hB.trans (Real.exp_le_exp.mpr
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by dsimp [w]; omega : v ≤ w)))
  have h := markedQuotient_final_height_bound d q B Q J w (by dsimp [w]; omega) hp hd hq hBW hQ hJ
  have he : (w + 2) * 11 = 5082 * s + 3564 := by dsimp [w, v]; omega
  change ((max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
    ((d + 1) * (B * Q) ^ d) : ℕ) : ℝ) ≤ _
  simpa only [he] using h

end Erdos3

end

section

namespace Erdos3

noncomputable def markedShiftInputBudget (s : ℕ) (p : ℝ) : ℝ :=
  p * (s + 1 : ℕ) * (p + 1) ^ s + p + (s + 1 : ℕ)

noncomputable def markedShiftHeightBudget (s : ℕ) (p : ℝ) : ℝ :=
  (markedShiftInputBudget s p + 2) ^ (5082 * s + 3564)

noncomputable def markedShiftModelBudget (s : ℕ) (p : ℝ) : ℝ :=
  markedShiftHeightBudget s p +
    (markedShiftHeightBudget s p + (bchIntegralDenominatorBound (s + 1) + 5 : ℕ)) ^
      (bchIntegralDenominatorBound (s + 1) + 5)

theorem markedShiftInputBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  positivity

theorem le_markedShiftInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  exact (le_add_of_nonneg_left (by positivity)).trans
    (le_add_of_nonneg_right (Nat.cast_nonneg _))

theorem step_le_markedShiftInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (s + 1 : ℕ) ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  exact le_add_of_nonneg_left (by positivity)

theorem markedShift_dimension_budget (s n t : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) :
    ((n * (s + 1) * (t + 1) ^ s + t : ℕ) : ℝ) ≤ markedShiftInputBudget s p := by
  calc
    _ ≤ p * (s + 1 : ℕ) * (p + 1) ^ s + p := by
      push_cast
      gcongr
    _ ≤ _ := le_add_of_nonneg_right (Nat.cast_nonneg (s + 1))

theorem markedShiftInputBudget_le_height (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    markedShiftInputBudget s p ≤ markedShiftHeightBudget s p :=
  le_power_budget (markedShiftInputBudget_nonneg s hp) (by omega)

theorem markedShiftHeightBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ markedShiftHeightBudget s p :=
  (markedShiftInputBudget_nonneg s hp).trans (markedShiftInputBudget_le_height s hp)

theorem markedShiftHeightBudget_le_model (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    markedShiftHeightBudget s p ≤ markedShiftModelBudget s p :=
  le_add_of_nonneg_right (pow_nonneg
    (add_nonneg (markedShiftHeightBudget_nonneg s hp) (Nat.cast_nonneg _)) _)

theorem exists_markedShiftModel_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → markedShiftModelBudget s p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X * Polynomial.C (s + 1) * (Polynomial.X + 1) ^ s +
    Polynomial.X + Polynomial.C (s + 1)
  let U : Polynomial ℕ := (Q + 2) ^ (5082 * s + 3564)
  let K := bchIntegralDenominatorBound (s + 1) + 5
  obtain ⟨C, hC, h⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa only [markedShiftModelBudget, markedShiftHeightBudget, markedShiftInputBudget,
    Q, U, K, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom] using h p hp

end Erdos3

end

section

namespace Erdos3

theorem markedEvaluation_extra_height_bound (n d q T Q K w : ℕ) (hw : 1 ≤ w)
    {p : ℝ} (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hT : (T : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hK' : (K : ℝ) ≤ Real.exp ((p + 2) ^ w)) :
    (((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ ((w + 3 + 2) * 8)) := by
  let W := (p + 2) ^ w
  have hpW : p ≤ W := le_power_budget hp hw
  have hW : 0 ≤ W := hp.trans hpW
  have hproduct : ((T * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 1)) := by
    rw [Nat.cast_mul]
    calc
      (T : ℝ) * K ≤ Real.exp W * Real.exp W :=
        mul_le_mul hT hK' (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (W + W) := (Real.exp_add W W).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          W + W = 2 * W := by ring
          _ ≤ (p + 2) * W := mul_le_mul_of_nonneg_right (by linarith) hW
          _ = (p + 2) ^ (w + 1) := by dsimp [W]; rw [pow_succ]; ring
  have hinner : (((n + 1) * (T * K) ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 3)) := by
    simpa only [show w + 1 + 1 + 1 = w + 3 by omega] using
      rational_sum_cost_le_exp n (T * K) hp (w + 1) 1 hproduct
        (by simpa only [pow_one] using hn.trans (by linarith : p ≤ p + 2))
  have hWW : W ≤ (p + 2) ^ (w + 3) :=
    pow_le_pow_right₀ (by linarith) (by omega : w ≤ w + 3)
  have hA : ((max T ((n + 1) * (T * K) ^ n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 3)) := by
    rw [Nat.cast_max]
    exact max_le (hT.trans (Real.exp_le_exp.mpr hWW)) hinner
  have hpV : p ≤ (p + 2) ^ (w + 3) := hpW.trans hWW
  have hV : 0 ≤ (p + 2) ^ (w + 3) := hp.trans hpV
  have heval := embedding_coordinate_height_budget d q Q (max T ((n + 1) * (T * K) ^ n))
    hV (hd.trans hpV) (hq.trans hpV) (hQ.trans (Real.exp_le_exp.mpr hWW)) hA
  exact exponential_budget_comp hp hV (w + 3) 8 le_rfl heval

theorem markedEvaluationHeight_le_exp (s n a d m q H K : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    (markedEvaluationHeight s n a d m q H K : ℝ) ≤
      Real.exp ((p + 2) ^ (5082 * s + 3564)) := by
  let v := (6 * s + 4) * 11
  let w := (v + 2) * 7
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  have hw : 1 ≤ w := by dsimp [w, v]; omega
  have hpW : p ≤ (p + 2) ^ w := le_power_budget hp hw
  obtain ⟨hB, hC⟩ := markedQuotient_source_height_bound s n a d H hp hs hn ha hd hH
  obtain ⟨hQ, _⟩ := markedQuotient_projection_height_bound m B C v
    (by dsimp [v]; omega) hp hm hB hC
  have hT : (T : ℝ) ≤ Real.exp ((p + 2) ^ w) :=
    (lieTreeHeight_le_exp n H s hp hn hH).trans (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by dsimp [w, v]; omega : 6 * s + 2 ≤ w)))
  have heval := markedEvaluation_extra_height_bound n d q T Q K w hw hp hn hd hq hT hQ
    (hK.trans (Real.exp_le_exp.mpr hpW))
  change ((max (markedQuotientHeight s n a d m q H)
    ((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max]
  refine max_le (markedQuotientHeight_le_exp s n a d m q H hp hs hn ha hd hm hq hH) ?_
  exact heval.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith)
    (by dsimp [w, v]; omega : (w + 3 + 2) * 8 ≤ 5082 * s + 3564)))

end Erdos3

end

end OAI
