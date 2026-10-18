import GowersSzemeredi.Proofs18TheoremOneDegrees

/-! Declarations of `Proofs18TheoremOneDegrees` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- A function discrepancy bound with parameters at least
`section18Exponent alpha k`, for every admissible `alpha`, gives Theorem 18.1
at degree `k`. -/
theorem Theorem181At.of_function_discrepancy {k : Nat}
    (h : ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 → ∃ beta sigma T : Real,
      section18Exponent alpha k ≤ beta ∧ section18Exponent alpha k ≤ sigma ∧
        FunctionDiscrepancyBound k alpha beta sigma T) :
    Theorem181At k := by
  intro alpha hα hα2
  obtain ⟨beta, sigma, T, hb, hs, hT⟩ := h alpha hα hα2
  refine ⟨⌈T⌉₊, fun N _ _ hN A hnot => ?_⟩
  obtain ⟨M, Q, hpart, hproper, hsize, hdisc⟩ :=
    hT N ((Nat.le_ceil T).trans (by exact_mod_cast hN)) (balanced A)
      (balanced_discValued A) hnot
  refine ⟨M, Q, hpart, hproper, ?_, ?_⟩
  · have hN1 : (1 : Real) ≤ N := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact (Real.rpow_le_rpow_of_exponent_le hN1 hs).trans hsize
  · exact (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg N)).trans hdisc

/-- Degree zero is vacuous: balanced functions have total sum zero. -/
theorem theorem_18_1_degree_zero : Theorem181At 0 := by
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
  simp only [hsum, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero]
  exact hα0

/-- The quadratic discrepancy parameter dominates the catalogue exponent. -/
theorem section18Exponent_two_le_quadraticDiscrepancyParameter {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18Exponent alpha 2 ≤ quadraticDiscrepancyParameter alpha := by
  refine le_trans ?_ (quadratic_discrepancy_fixed_power_lower hα hα2).1
  unfold section18Exponent
  exact pow_le_pow_of_le_one hα.le (by linarith)
    ((by norm_num : 49462 ≤ (2 : Nat) ^ 16).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-- The quadratic width exponent dominates the catalogue exponent. -/
theorem section18Exponent_two_le_quadraticDiscrepancyExponent {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18Exponent alpha 2 ≤ quadraticDiscrepancyExponent alpha := by
  refine le_trans ?_ (quadratic_discrepancy_fixed_power_lower hα hα2).2
  unfold section18Exponent
  exact pow_le_pow_of_le_one hα.le (by linarith)
    ((by norm_num : 49462 ≤ (2 : Nat) ^ 16).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-- **Theorem 18.1 at degree two**, from the quadratic inverse theorem. -/
theorem theorem_18_1_degree_two : Theorem181At 2 := by
  apply Theorem181At.of_function_discrepancy
  intro alpha hα hα2
  exact ⟨quadraticDiscrepancyParameter alpha, quadraticDiscrepancyExponent alpha,
    quadraticExponentialThreshold alpha,
    section18Exponent_two_le_quadraticDiscrepancyParameter hα hα2,
    section18Exponent_two_le_quadraticDiscrepancyExponent hα hα2,
    quadratic_function_discrepancy_bound hα (by linarith)⟩

end LeanProofs.GowersSzemeredi
