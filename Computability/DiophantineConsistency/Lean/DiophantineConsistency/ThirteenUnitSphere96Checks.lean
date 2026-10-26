import DiophantineConsistency.ThirteenUnitSphere96

set_option Elab.async false
namespace DiophantineConsistency.ThirteenUnitSphere96Checks
open ThirteenUnitSphere96

theorem signed_sphere (a b c : ℤ) :
    a^2+b^2+c^2=3 ↔ a^2=1 ∧ b^2=1 ∧ c^2=1 :=
  three_squares_eq_three_iff a b c

theorem negative_units_are_retained_by_sphere :
    (-1 : ℤ)^2 + (-1)^2 + (-1)^2 = 3 := by norm_num

theorem wrong_constants_admit_nonunits :
    (1 : ℤ)^2+1^2+0^2=2 ∧ (2 : ℤ)^2+0^2+0^2=4 := by norm_num

theorem parent_polynomial_not_an_identity :
    ((2 : ℤ)*1)^2+1^2+1^2-3 ≠ ((2 : ℤ)*1-1)^2+(1-1)^2+(1-1)^2 := by
  norm_num

theorem identical_positive_assignment (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔ ThirteenSharedSquares96.value p v = 0 :=
  (positive_zero_iff72 p v hb hv).trans
    (ThirteenSharedSquares96.positive_zero_iff72 p v hb hv).symm

theorem actual_current_ports :
    currentPolynomial = polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

theorem exact_conZFC :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := no_current_positive_zero_iff_conZFC

#print axioms three_squares_eq_three_iff
#print axioms product_ne_neg_one
#print axioms main_ne_neg_one
#print axioms strong_ne_neg_one
#print axioms auxiliary_ne_neg_one
#print axioms positive_zero_iff_residuals
#print axioms positive_zero_iff72
#print axioms value_map
#print axioms eval_polynomial
#print axioms exists_positive_zero_iff72
#print axioms no_current_positive_zero_iff_conZFC
#print axioms identical_positive_assignment
#print axioms actual_current_ports

end DiophantineConsistency.ThirteenUnitSphere96Checks
