import DiophantineConsistency.ThirteenSharedSquares96

set_option Elab.async false
namespace DiophantineConsistency.ThirteenSharedSquares96Checks
open ThirteenSharedSquares96

theorem full_ring_identity {A : Type*} [CommRing A]
    (p : Fin 4 → A) (v : Fin 13 → A) :
    value p v = ThirteenGroupedSquares96.value p v := value_eq_grouped p v

theorem identical_signed_zero_set (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    value p v = 0 ↔ ThirteenGroupedSquares96.value p v = 0 := by
  rw [value_eq_grouped]

theorem shared_residual_identity {A : Type*} [CommRing A] (f d s : A) :
    (f^2 - 1) - d*s^2 = (f^2 - d*s^2) - 1 := by ring

/-- The subtracted one must be included in the shared strong residual. -/
theorem omission_changes_square :
    (((4 : ℤ)-1)-1)^2 = 4 ∧ ((4 : ℤ)-1)^2 = 9 := by norm_num

theorem current_ports_exact :
    currentPolynomial = polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

theorem same_current_polynomial :
    currentPolynomial = ThirteenGroupedSquares96.currentPolynomial :=
  currentPolynomial_eq_grouped

theorem same_current_positive_zero :
    CurrentCarrierArithmetic2011.PositiveZero currentPolynomial ↔
      CurrentCarrierArithmetic2011.PositiveZero ThirteenGroupedSquares96.currentPolynomial := by
  rw [currentPolynomial_eq_grouped]

#print axioms value_eq_grouped
#print axioms value_map
#print axioms polynomial_eq_grouped
#print axioms eval_polynomial
#print axioms same_assignment
#print axioms positive_zero_iff72
#print axioms currentPolynomial_eq_grouped
#print axioms no_current_positive_zero_iff_conZFC
#print axioms identical_signed_zero_set
#print axioms shared_residual_identity
#print axioms same_current_positive_zero

end DiophantineConsistency.ThirteenSharedSquares96Checks
