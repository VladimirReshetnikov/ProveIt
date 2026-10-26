import DiophantineConsistency.ThirteenCorrectedStrong

namespace DiophantineConsistency.ThirteenCorrectedStrongChecks

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K

open ThirteenCorrectedStrong

example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) : (ThirteenCarrier.core p v).P ≠ -1 :=
  first_ne_neg_one p v hb hv

example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : value p v = 0) :
    (ThirteenCarrier.core p v).P = 1 := first_eq_one_of_zero p v hb hv hz

example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) (hz : ThirteenCarrier.value71 p v = 0) :
    (ThirteenCarrier.core p v).P = 1 := first_eq_one_of_old_zero p v hb hv hz

example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (hb : 0 < p 0)
    (hv : ∀ j, 0 < v j) :
    MvPolynomial.eval v (polynomial p) = 0 ↔
      MvPolynomial.eval v (ThirteenCarrier.polynomial71 p) = 0 :=
  positive_polynomial_zero_iff p v hb hv

example : (¬ CurrentCarrierArithmetic2011.PositiveZero
    (polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)))) ↔
    DiophantineConsistency.ConZFC := no_current_positive_zero_iff_conZFC

example (h : ¬ DiophantineConsistency.ConZFC) :
    CurrentCarrierArithmetic2011.PositiveZero currentPolynomial := by
  by_contra hz
  exact h (no_current_positive_zero_iff_conZFC.mp hz)

#print axioms correctedStrong_eq
#print axioms coefficient_cancellation
#print axioms correction_identity
#print axioms first_ne_neg_one
#print axioms first_eq_one_of_zero
#print axioms first_eq_one_of_old_zero
#print axioms positive_zero_iff
#print axioms value_map
#print axioms eval_polynomial
#print axioms exists_positive_zero_iff
#print axioms no_current_positive_zero_iff_conZFC

end DiophantineConsistency.ThirteenCorrectedStrongChecks
