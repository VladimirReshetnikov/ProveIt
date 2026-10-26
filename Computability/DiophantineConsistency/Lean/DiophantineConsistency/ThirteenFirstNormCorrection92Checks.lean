import DiophantineConsistency.ThirteenFirstNormCorrection92

set_option Elab.async false
namespace DiophantineConsistency.ThirteenFirstNormCorrection92Checks
open ThirteenFirstNormCorrection92

theorem arbitrary_signed_correction (P Q U Z c : ℤ) (hP : P ≠ -1) (hQ : Q ≠ -1) :
    (P*Q)^2+(U-c*(P-1))^2+Z^2-3=0 ↔ (P*Q)^2+U^2+Z^2-3=0 :=
  correction_zero_iff P Q U Z c hP hQ

theorem negative_first_unit_must_be_excluded :
    ((-1 : ℤ)*1)^2+(1-1*((-1)-1))^2+1^2-3 ≠ 0 ∧
      ((-1 : ℤ)*1)^2+1^2+1^2-3=0 := by norm_num

theorem no_polynomial_identity_claim :
    ((2 : ℤ)*1)^2+(1-1*(2-1))^2+1^2-3 ≠
      ((2 : ℤ)*1)^2+1^2+1^2-3 := by norm_num

theorem identical_positive_assignment (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v=0 ↔ ThirteenLVCarrier.value72 p v=0 :=
  (positive_zero_iff75 p v hb hv).trans
    (ThirteenUnitSphere96.positive_zero_iff72 p v hb hv)

theorem actual_current_ports :
    currentPolynomial = polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

theorem exact_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := no_current_positive_zero_iff_conZFC

#print axioms correction_zero_iff
#print axioms positive_zero_iff75
#print axioms value_map
#print axioms eval_polynomial
#print axioms exists_positive_zero_iff75
#print axioms no_current_positive_zero_iff_conZFC
#print axioms identical_positive_assignment
#print axioms actual_current_ports

end DiophantineConsistency.ThirteenFirstNormCorrection92Checks
