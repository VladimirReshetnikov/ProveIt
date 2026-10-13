import GowersSzemeredi.Proofs18SharpInterfaces

/-! **Theorem 18.1 in degrees zero through three with offset four.**

The low-degree corpus bounds prove the strongest offset-four instance once.
The older offset-seven interface is obtained by monotonicity; the Fejér
low-degree module likewise derives offset six. Degree three uses the
polynomial base envelope and a progression phase partition. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem theorem_18_1_d4_degree_zero : Theorem181AtSharp 4 0 := by
  intro alpha hα _hα2
  refine ⟨1, fun N _ _ _ A hnot => ?_⟩
  exfalso
  apply hnot
  have hsum : ∀ a : Point N 0, ∑ s : ZMod N, cubeDifference (balanced A) a s = 0 := by
    intro a
    simp only [cubeDifference, List.ofFn_zero, iteratedDifference]
    exact sum_balanced A
  show ∑ a : Point N 0, ‖∑ s : ZMod N, cubeDifference (balanced A) a s‖ ^ 2 ≤
    alpha * (N : Real) ^ (0 + 2)
  have hα0 : 0 ≤ alpha * (N : Real) ^ (0 + 2) := by positivity
  first
    | (simp only [hsum, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero]; exact hα0)
    | (simp [hsum]; done)
    | (simp [hsum]; positivity)

theorem section18ExponentAt4_two_le_quadraticDiscrepancyParameter {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 4 alpha 2 ≤ quadraticDiscrepancyParameter alpha := by
  refine le_trans ?_ (quadratic_discrepancy_fixed_power_lower hα hα2).1
  unfold section18ExponentAt
  exact pow_le_pow_of_le_one hα.le (by linarith)
    ((by norm_num : 49462 ≤ (2 : Nat) ^ 16).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

theorem section18ExponentAt4_two_le_quadraticDiscrepancyExponent {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 4 alpha 2 ≤ quadraticDiscrepancyExponent alpha := by
  refine le_trans ?_ (quadratic_discrepancy_fixed_power_lower hα hα2).2
  unfold section18ExponentAt
  exact pow_le_pow_of_le_one hα.le (by linarith)
    ((by norm_num : 49462 ≤ (2 : Nat) ^ 16).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

theorem theorem_18_1_d4_degree_two : Theorem181AtSharp 4 2 := by
  apply Theorem181AtSharp.of_function_discrepancy
  intro alpha hα hα2
  exact ⟨quadraticDiscrepancyParameter alpha, quadraticDiscrepancyExponent alpha,
    quadraticExponentialThreshold alpha,
    section18ExponentAt4_two_le_quadraticDiscrepancyParameter hα hα2,
    section18ExponentAt4_two_le_quadraticDiscrepancyExponent hα hα2,
    quadratic_function_discrepancy_bound hα (by linarith)⟩

theorem theorem_18_1_d4_degree_one : Theorem181AtSharp 4 1 := by
  apply Theorem181AtSharp.of_function_discrepancy
  intro alpha ha ha2
  have ha1 : alpha ≤ 1 := by linarith
  have haSq : 0 < alpha ^ 2 := pow_pos ha 2
  have haSqHalf : alpha ^ 2 ≤ 1 / 2 := by nlinarith
  obtain ⟨hb, hs⟩ := quadratic_discrepancy_fixed_power_lower haSq haSqHalf
  have he : section18ExponentAt 4 alpha 1 ≤ (alpha ^ 2) ^ (49462 : Nat) := by
    unfold section18ExponentAt
    rw [← pow_mul]
    exact pow_le_pow_of_le_one ha.le ha1
      ((by norm_num : 2 * 49462 ≤ (2 : Nat) ^ 17).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  refine ⟨quadraticDiscrepancyParameter (alpha ^ 2), quadraticDiscrepancyExponent (alpha ^ 2),
    quadraticExponentialThreshold (alpha ^ 2), he.trans hb, he.trans hs, ?_⟩
  intro N _ _ hN f hf hnot
  apply quadratic_function_discrepancy_bound haSq (by linarith) N hN f hf
  intro hu
  apply hnot
  have h := lemma_3_4_holds N 2 f (alpha ^ 2) (by norm_num) hf hu
  simpa only [Nat.reduceSub, ← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le] using h

/-- **Theorem 18.1 at degree three with exponent `α^(2^(2^7))`**, from a phase
partition. -/
theorem theorem_18_1_d4_three_of_phase_partition
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    Theorem181AtSharp 4 3 :=
  theorem181AtSharp_of_polyEnvBound (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
    (by norm_num)


/-! The older offset-seven interface follows from the offset-four result. -/

theorem theorem_18_1_d7_degree_zero : Theorem181AtSharp 7 0 :=
  theorem_18_1_d4_degree_zero.mono (by norm_num)

theorem section18ExponentAt7_two_le_quadraticDiscrepancyParameter {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 7 alpha 2 ≤ quadraticDiscrepancyParameter alpha := by
  exact (section18ExponentAt_antitone (by norm_num : 4 ≤ 7) hα.le (by linarith)).trans
    (section18ExponentAt4_two_le_quadraticDiscrepancyParameter hα hα2)

theorem section18ExponentAt7_two_le_quadraticDiscrepancyExponent {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 7 alpha 2 ≤ quadraticDiscrepancyExponent alpha := by
  exact (section18ExponentAt_antitone (by norm_num : 4 ≤ 7) hα.le (by linarith)).trans
    (section18ExponentAt4_two_le_quadraticDiscrepancyExponent hα hα2)

theorem theorem_18_1_d7_degree_two : Theorem181AtSharp 7 2 :=
  theorem_18_1_d4_degree_two.mono (by norm_num)

theorem theorem_18_1_d7_degree_one : Theorem181AtSharp 7 1 :=
  theorem_18_1_d4_degree_one.mono (by norm_num)

/-- **Theorem 18.1 at degree three with exponent `α^(2^(2^10))`**, from a phase
partition. -/
theorem theorem_18_1_d7_three_of_phase_partition
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    Theorem181AtSharp 7 3 :=
  (theorem_18_1_d4_three_of_phase_partition hpp hpφ hKφ hpφB).mono (by norm_num)

end LeanProofs.GowersSzemeredi
