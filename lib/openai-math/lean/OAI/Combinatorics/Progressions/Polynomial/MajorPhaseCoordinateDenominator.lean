/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {η σ : Type*} [Fintype η]

theorem majorPhaseCoordinateDenominator_pos (q : η → ℕ)
    (hq : ∀ i, 0 < q i) : 0 < ∏ i, q i :=
  Finset.prod_pos (fun i _ => hq i)

theorem majorPhaseCoordinateDenominator_le_exp (q : η → ℕ) (B : ℝ)
    (hq : ∀ i, (q i : ℝ) ≤ Real.exp B) :
    ((∏ i, q i : ℕ) : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * B) := by
  classical
  rw [Nat.cast_prod]
  calc
    (∏ i, (q i : ℝ)) ≤ ∏ _i : η, Real.exp B :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg (q i)) (fun i _ => hq i)
    _ = Real.exp ((Fintype.card η : ℝ) * B) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

theorem majorPhaseCoordinateDenominator_grid (q : η → ℕ)
    (R : η → MvPolynomial σ ℚ)
    (hR : ∀ i, (fun α => (R i).coeff α) ∈ denominatorGrid (q i)) (i : η) :
    (fun α => (R i).coeff α) ∈ denominatorGrid (∏ j, q j) := by
  classical
  exact denominatorGrid_subset_of_dvd (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    (hR i)

theorem majorPhaseCoordinateDenominator_joint_grid (q : η → ℕ)
    (R : η → MvPolynomial σ ℚ)
    (hR : ∀ i, (fun α => (R i).coeff α) ∈ denominatorGrid (q i)) :
    (fun p : η × (σ →₀ ℕ) => (R p.1).coeff p.2) ∈ denominatorGrid (∏ j, q j) := by
  classical
  have h := fun i => majorPhaseCoordinateDenominator_grid q R hR i
  choose z hz using h
  exact ⟨fun p => z p.1 p.2, fun p => hz p.1 p.2⟩

theorem majorPhaseCoordinateDenominator_coeff_den_dvd (q : η → ℕ)
    (hq : ∀ i, 0 < q i) (R : η → MvPolynomial σ ℚ)
    (hR : ∀ i, (fun α => (R i).coeff α) ∈ denominatorGrid (q i))
    (i : η) (α : σ →₀ ℕ) :
    ((R i).coeff α).den ∣ ∏ j, q j :=
  den_dvd_of_mem_denominatorGrid (majorPhaseCoordinateDenominator_pos q hq)
    (majorPhaseCoordinateDenominator_grid q R hR i) α

theorem majorPhaseCoordinateDenominator_bounds (q : η → ℕ)
    (hq : ∀ i, 0 < q i) (B : ℝ) (hqB : ∀ i, (q i : ℝ) ≤ Real.exp B)
    (R : η → MvPolynomial σ ℚ)
    (hR : ∀ i, (fun α => (R i).coeff α) ∈ denominatorGrid (q i)) :
    0 < ∏ i, q i ∧
      ((∏ i, q i : ℕ) : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * B) ∧
      (∀ i, (fun α => (R i).coeff α) ∈ denominatorGrid (∏ j, q j)) ∧
      ∀ i α, ((R i).coeff α).den ∣ ∏ j, q j ∧
        ((R i).coeff α).den ≤ ∏ j, q j := by
  refine ⟨majorPhaseCoordinateDenominator_pos q hq,
    majorPhaseCoordinateDenominator_le_exp q B hqB,
    majorPhaseCoordinateDenominator_grid q R hR, ?_⟩
  intro i α
  have hdvd := majorPhaseCoordinateDenominator_coeff_den_dvd q hq R hR i α
  exact ⟨hdvd, Nat.le_of_dvd (majorPhaseCoordinateDenominator_pos q hq) hdvd⟩

end Erdos3

end

end OAI
