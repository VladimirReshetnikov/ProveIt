import GowersSzemeredi.Proofs18FunctionDiscrepancyReduction
import GowersSzemeredi.Proofs18QuadraticDensityIncrement
import GowersSzemeredi.Sections17_18

/-! Theorem 18.1 degree by degree.

`theorem_18_1` quantifies over every degree `k`. This module names the
statement at one degree (`Theorem181At k`) and records that the catalogue
entry is exactly the conjunction over all degrees.

`Proofs18TheoremOneDegreesSide`, outside the final route, turns any function
discrepancy bound whose parameters dominate `section18Exponent alpha k` into
the degree-`k` statement (`Theorem181At.of_function_discrepancy`), and proves
these degrees:

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
warning on `theorem_18_1`.

`Theorem181At.of_function_discrepancy`,
`section18Exponent_two_le_quadraticDiscrepancyExponent`,
`section18Exponent_two_le_quadraticDiscrepancyParameter`,
`theorem_18_1_degree_two` and `theorem_18_1_degree_zero` are in
`Proofs18TheoremOneDegreesSide`, outside the final route. -/
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

/-- A fixed power dominates both parameters of the quadratic inverse
throughout the source's density range. This does not fix a tower offset. -/
theorem quadratic_discrepancy_fixed_power_lower {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    alpha ^ (49462 : Nat) ≤ quadraticDiscrepancyParameter alpha ∧
      alpha ^ (49462 : Nat) ≤ quadraticDiscrepancyExponent alpha := by
  have ha1 : alpha ≤ 1 := by linarith
  have hsq : alpha * alpha ≤ alpha / 2 := by nlinarith
  have hA : alpha ^ (24718 : Nat) ≤ (alpha / 2) ^ (12359 : Nat) := by
    calc
      alpha ^ (24718 : Nat) = (alpha * alpha) ^ (12359 : Nat) := by ring
      _ ≤ (alpha / 2) ^ (12359 : Nat) := pow_le_pow_left₀ (by positivity) hsq _
  have hB : alpha ^ (20 : Nat) ≤ (2 : Real) ^ (-(20 : Int)) := by
    have h20 : (2 : Real) ^ (-(20 : Int)) = (1 / 2) ^ (20 : Nat) := by norm_num
    rw [h20]
    exact pow_le_pow_left₀ ha.le ha2 _
  constructor
  · have hp : alpha ^ (24740 : Nat) ≤ quadraticDiscrepancyParameter alpha := by
      unfold quadraticDiscrepancyParameter
      calc
        alpha ^ (24740 : Nat) = alpha ^ (20 : Nat) * alpha ^ 2 * alpha ^ (24718 : Nat) := by ring
        _ ≤ (2 : Real) ^ (-(20 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hB (by positivity)) hA
            (by positivity) (by positivity)
    exact (pow_le_pow_of_le_one ha.le ha1 (by omega : 24740 ≤ 49462)).trans hp
  · have h14 : (2 : Real) ^ (-(14 : Real)) = (1 / 2) ^ (14 : Nat) := by
      rw [Real.rpow_neg (by norm_num), show (14 : Real) = ((14 : Nat) : Real) by norm_num,
        Real.rpow_natCast]
      norm_num
    have hC : alpha ^ (14 : Nat) ≤ (1 / 2) ^ (14 : Nat) := pow_le_pow_left₀ ha.le ha2 _
    have hD : (alpha ^ (24718 : Nat)) ^ 2 ≤ ((alpha / 2) ^ (12359 : Nat)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hA 2
    have hE : alpha ^ (12 : Nat) ≤ (1 / 2) ^ (12 : Nat) := pow_le_pow_left₀ ha.le ha2 _
    unfold quadraticDiscrepancyExponent cor711Exponent
    rw [h14]
    calc
      alpha ^ (49462 : Nat) = alpha ^ (14 : Nat) * (alpha ^ (24718 : Nat)) ^ 2 * alpha ^ (12 : Nat) := by ring
      _ ≤ (1 / 2) ^ (14 : Nat) * ((alpha / 2) ^ (12359 : Nat)) ^ 2 * (1 / 2) ^ (12 : Nat) :=
        mul_le_mul (mul_le_mul hC hD (by positivity) (by positivity)) hE
          (by positivity) (by positivity)
      _ = _ := by norm_num <;> ring

end LeanProofs.GowersSzemeredi
