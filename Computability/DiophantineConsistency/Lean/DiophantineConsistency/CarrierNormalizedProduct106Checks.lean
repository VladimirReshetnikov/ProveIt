import DiophantineConsistency.CarrierNormalizedProduct106

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.CarrierNormalizedProduct106Checks
open CarrierNormalizedProduct106

example {A : Type*} [CommRing A] (p : Fin 4 → A) (v : Fin 14 → A) :
    CarrierScaledAuxiliary118.value p v=(Carrier65.core p v).delta*value p v := scaled_identity p v

example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hd : (Carrier65.core p v).delta ≠ 0) :
    value p v=0 ↔ CarrierScaledAuxiliary118.value p v=0 := zero_iff_scaled p v hd

/-- Identity witness maps preserve arbitrary positive assignments. -/
example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : 0 < p 0) (hv : ∀ j,0 < v j) :
    MvPolynomial.eval v (polynomial p)=0 ↔ MvPolynomial.eval v (Carrier65.polynomial p)=0 :=
  positive_polynomial_zero_iff_original p v hb hv

example : (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
    DiophantineConsistency.ConZFC := no_current_positive_zero_iff_conZFC

#print axioms scaled_identity
#print axioms zero_iff_scaled
#print axioms positive_zero_iff_original
#print axioms eval_polynomial
#print axioms positive_polynomial_zero_iff_original
#print axioms no_current_positive_zero_iff_conZFC
end DiophantineConsistency.CarrierNormalizedProduct106Checks
