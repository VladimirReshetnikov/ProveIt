import GowersSzemeredi.Proofs18FunctionDiscrepancyReduction
import GowersSzemeredi.Proofs18QuadraticDensityIncrement
import GowersSzemeredi.Sections17_18

/-! Theorem 18.1 degree by degree.

`theorem_18_1` quantifies over every degree `k`. This module names the
statement at one degree (`Theorem181At k`), records that the catalogue
entry is exactly the conjunction over all degrees, and turns any function
discrepancy bound whose parameters dominate `section18Exponent alpha k`
into the degree-`k` statement.

Proved degrees:

* `k = 0`: vacuous, because a balanced function has total sum zero, so
  every set is uniform of degree zero.
* `k = 2`: from the quadratic inverse theorem
  (`quadratic_function_discrepancy_bound`). Its parameters are fixed powers
  of `alpha` (about `alpha^24740` and `alpha^49462`), far above the
  catalogue's `alpha^(2^(2^12))`.

The proved cubic bound does not give `k = 3`. Its exponent is only known
to satisfy `1/e <= exp((2/alpha)^(2^61))`
(`fejerCubicDiscrepancyExponent_inv_le_exp`), which is exponentially small,
whereas `section18Exponent alpha 3` is a fixed power of `alpha`. This is the
unsupported Corollary 16.11 estimate named in the catalogue's editorial
warning on `theorem_18_1`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Theorem 18.1 at a single degree `k`. -/
def Theorem181At (k : Nat) : Prop :=
  ∀ (alpha : Real), 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ A : Finset (ZMod N), ¬ UniformSetOfDegree A alpha k →
        ∃ M : Nat, ∃ P : Fin M → ModAP N,
          IsPartition (fun i => (P i).carrier) Finset.univ ∧
          (∀ i, (P i).IsProper) ∧
          (N : Real) ^ section18Exponent alpha k ≤
            averageCellSize (fun i => (P i).carrier) ∧
          section18Exponent alpha k * N ≤
            ∑ i, ‖∑ s ∈ (P i).carrier, balanced A s‖

/-- The catalogue entry is exactly Theorem 18.1 at every degree. -/
theorem theorem_18_1_iff_forall_degree : theorem_18_1 ↔ ∀ k, Theorem181At k :=
  Iff.rfl

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
  first
    | (simp only [hsum, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero]; exact hα0)
    | (simp [hsum]; done)
    | (simp [hsum]; positivity)

/-- The quadratic discrepancy parameter dominates the catalogue exponent. -/
theorem section18Exponent_two_le_quadraticDiscrepancyParameter {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18Exponent alpha 2 ≤ quadraticDiscrepancyParameter alpha := by
  have hα1 : alpha ≤ 1 := by linarith
  have hsq : alpha * alpha ≤ alpha / 2 := by nlinarith
  have hA : alpha ^ (24718 : Nat) ≤ (alpha / 2) ^ (12359 : Nat) := by
    calc alpha ^ (24718 : Nat) = (alpha * alpha) ^ (12359 : Nat) := by ring
      _ ≤ (alpha / 2) ^ (12359 : Nat) := pow_le_pow_left₀ (by positivity) hsq _
  have h20 : (2 : Real) ^ (-(20 : Int)) = (1 / 2) ^ (20 : Nat) := by norm_num
  have hB : alpha ^ (20 : Nat) ≤ (2 : Real) ^ (-(20 : Int)) := by
    rw [h20]
    exact pow_le_pow_left₀ hα.le hα2 _
  have hexp : (24740 : Nat) ≤ 2 ^ 2 ^ (2 + 10) :=
    (by norm_num : (24740 : Nat) ≤ 2 ^ 15).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  unfold section18Exponent quadraticDiscrepancyParameter
  calc alpha ^ 2 ^ 2 ^ (2 + 10) ≤ alpha ^ (24740 : Nat) :=
        pow_le_pow_of_le_one hα.le hα1 hexp
    _ = alpha ^ (20 : Nat) * alpha ^ 2 * alpha ^ (24718 : Nat) := by ring
    _ ≤ (2 : Real) ^ (-(20 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hB (by positivity)) hA
          (by positivity) (by positivity)

/-- The quadratic width exponent dominates the catalogue exponent. -/
theorem section18Exponent_two_le_quadraticDiscrepancyExponent {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18Exponent alpha 2 ≤ quadraticDiscrepancyExponent alpha := by
  have hα1 : alpha ≤ 1 := by linarith
  have hsq : alpha * alpha ≤ alpha / 2 := by nlinarith
  have hA : alpha ^ (24718 : Nat) ≤ (alpha / 2) ^ (12359 : Nat) := by
    calc alpha ^ (24718 : Nat) = (alpha * alpha) ^ (12359 : Nat) := by ring
      _ ≤ (alpha / 2) ^ (12359 : Nat) := pow_le_pow_left₀ (by positivity) hsq _
  have h14 : (2 : Real) ^ (-(14 : Real)) = (1 / 2) ^ (14 : Nat) := by
    rw [Real.rpow_neg (by norm_num), show (14 : Real) = ((14 : Nat) : Real) by norm_num,
      Real.rpow_natCast]
    norm_num
  have hexp : (49462 : Nat) ≤ 2 ^ 2 ^ (2 + 10) :=
    (by norm_num : (49462 : Nat) ≤ 2 ^ 16).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hC : alpha ^ (14 : Nat) ≤ (1 / 2) ^ (14 : Nat) := pow_le_pow_left₀ hα.le hα2 _
  have hD : (alpha ^ (24718 : Nat)) ^ 2 ≤ ((alpha / 2) ^ (12359 : Nat)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA 2
  have hE : alpha ^ (12 : Nat) ≤ (1 / 2) ^ (12 : Nat) := pow_le_pow_left₀ hα.le hα2 _
  unfold section18Exponent quadraticDiscrepancyExponent cor711Exponent
  rw [h14]
  calc alpha ^ 2 ^ 2 ^ (2 + 10) ≤ alpha ^ (49462 : Nat) :=
        pow_le_pow_of_le_one hα.le hα1 hexp
    _ = alpha ^ (14 : Nat) * (alpha ^ (24718 : Nat)) ^ 2 * alpha ^ (12 : Nat) := by ring
    _ ≤ (1 / 2) ^ (14 : Nat) * ((alpha / 2) ^ (12359 : Nat)) ^ 2 * (1 / 2) ^ (12 : Nat) :=
        mul_le_mul (mul_le_mul hC hD (by positivity) (by positivity)) hE
          (by positivity) (by positivity)
    _ = (1 / 2) ^ (14 : Nat) * ((alpha / 2) ^ (12359 : Nat)) ^ 2 * ((1 : Nat) : Real)⁻¹ /
          4096 := by
        first | (norm_num; done) | (norm_num; ring) | ring

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
