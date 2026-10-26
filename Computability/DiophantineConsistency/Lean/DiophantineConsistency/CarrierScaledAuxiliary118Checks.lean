import DiophantineConsistency.CarrierScaledAuxiliary118

namespace DiophantineConsistency.CarrierScaledAuxiliary118Checks

open CarrierScaledAuxiliary118
set_option Elab.async false

-- The whole positive zero set is preserved at the identity assignment.
example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : 0<p 0) (hv : ∀ j,0<v j) :
    MvPolynomial.eval v (polynomial p)=0 ↔
      MvPolynomial.eval v (Carrier65.polynomial p)=0 :=
  positive_polynomial_zero_sets p v hb hv

-- Even positivity is unnecessary when the actual discriminant is nonzero.
example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hd : (Carrier65.core p v).delta ≠ 0) :
    value p v=0 ↔ Carrier65.value p v=0 := value_zero_iff_original p v hd

-- Closed current-port endpoint, without a supplied source/norm/mask premise.
example : (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
    DiophantineConsistency.ConZFC := no_current_positive_zero_iff_conZFC

#print axioms scaled_identity
#print axioms original_scaled_identity
#print axioms value_zero_iff_original
#print axioms positive_polynomial_zero_sets
#print axioms current_positive_zero_iff
#print axioms no_current_positive_zero_iff_conZFC

end DiophantineConsistency.CarrierScaledAuxiliary118Checks
