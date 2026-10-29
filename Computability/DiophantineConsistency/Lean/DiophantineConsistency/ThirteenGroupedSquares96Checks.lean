import DiophantineConsistency.ThirteenGroupedSquares96

set_option Elab.async false
namespace DiophantineConsistency.ThirteenGroupedSquares96Checks
open ThirteenGroupedSquares96 ThirteenCarrierSoundness

theorem identity_witness_map (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ThirteenLVCarrier.value72 p v = 0 :=
  positive_zero_iff72 p v hb hv

theorem square_direction_needs_no_positivity (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hz : value p v = 0) :
    (data p v).P * (data p v).Q = 1 ∧ ThirteenGroupedSquares96.auxiliary p v = 1 ∧
      Carrier65.strong (data p v) = 1 := (value_zero_iff_residuals p v).mp hz

/-- The converse for arbitrary three factors is false: the actual norm theorem
is essential, even though no individual P or Q conclusion is used here. -/
theorem sign_control_needed :
    (-1 : ℤ)*(-1)*1-1 = 0 ∧ ((-1 : ℤ)-1)^2+((-1 : ℤ)-1)^2+(1-1)^2 = 8 := by
  norm_num

theorem zero_squares : (0 : ℤ)^2+0^2+0^2 = 0 :=
  (three_squares_zero_iff 0 0 0).mpr ⟨rfl, rfl, rfl⟩

theorem current_ports_exact :
    currentPolynomial = polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

theorem same_assignment_current (v : Fin 13 → ℤ) (hv : ∀ j, 0 < v j) :
    MvPolynomial.eval v currentPolynomial = 0 ↔
      MvPolynomial.eval v ThirteenLVCarrier.currentPolynomial72 = 0 := by
  rw [currentPolynomial, ThirteenLVCarrier.currentPolynomial72,
    eval_polynomial, ThirteenLVCarrier.eval_polynomial72]
  apply positive_zero_iff72 _ v _ hv
  change (0 : ℤ) < CurrentMasks2011.beta
  exact CurrentMasks2011.beta_pos_int

#print axioms three_squares_zero_iff
#print axioms value_zero_iff_residuals
#print axioms residuals_of_positive72_zero
#print axioms positive_zero_iff72
#print axioms value_map
#print axioms eval_polynomial
#print axioms exists_positive_zero_iff72
#print axioms no_current_positive_zero_iff_conZFC
#print axioms same_assignment_current

end DiophantineConsistency.ThirteenGroupedSquares96Checks
