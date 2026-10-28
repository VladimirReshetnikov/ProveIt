import DiophantineConsistency.ThirteenSecondFirstNormCorrections
set_option Elab.async false
namespace DiophantineConsistency.ThirteenSecondFirstNormCorrectionsChecks
open ThirteenSecondFirstNormCorrections

example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    coefficient false p v=coefficient90 p v := rfl
example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    coefficient true p v=coefficient88 p v := rfl

theorem same_positive_assignment (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value false p v=0 ↔ value true p v=0 := both_positive_zero_sets p v hb hv

theorem both_actual_ports (sharp : Bool) :
    currentPolynomial sharp =
      polynomial sharp (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

theorem actual90 :
    (¬ CurrentCarrierArithmetic2011.PositiveZero (currentPolynomial false)) ↔
      DiophantineConsistency.ConZFC := no_current_positive_zero_iff_conZFC false

theorem actual88 :
    (¬ CurrentCarrierArithmetic2011.PositiveZero (currentPolynomial true)) ↔
      DiophantineConsistency.ConZFC := no_current_positive_zero_iff_conZFC true

theorem correction_is_not_polynomial_equality :
    ((2 : ℤ)*1)^2+(1-1*(2-1))^2+1^2-3 ≠
      ((2 : ℤ)*1)^2+1^2+1^2-3 := by norm_num

#print axioms coefficient88_eq_difference
#print axioms positive_zero_iff75
#print axioms both_positive_zero_sets
#print axioms value_map
#print axioms eval_polynomial
#print axioms exists_positive_zero_iff75
#print axioms no_current_positive_zero_iff_conZFC
#print axioms both_actual_ports
#print axioms actual90
#print axioms actual88
end DiophantineConsistency.ThirteenSecondFirstNormCorrectionsChecks
