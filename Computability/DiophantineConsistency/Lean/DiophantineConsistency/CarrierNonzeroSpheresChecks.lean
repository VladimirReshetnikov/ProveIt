import DiophantineConsistency.CarrierNonzeroSpheres

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.CarrierNonzeroSpheresChecks
open Carrier65 CarrierNonzeroSpheres

example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    (core p v).P ≠ 0 ∧ (core p v).Q ≠ 0 ∧ strong (core p v) ≠ 0 ∧
      auxiliary (core p v) ≠ 0 :=
  ⟨first_ne_zero p v hb hv,main_ne_zero p v hb hv,
    strong_ne_zero p v hb hv,auxiliary_ne_zero p v hb hv⟩

example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hf : (core p v).f=1) :
    auxiliary (core p v)=(core p v).y^2 := by
  simp only [auxiliary,hf,one_pow,sub_self,mul_zero,zero_mul,zero_add]

example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hs : strong (core p v)=1) :
    auxiliary (core p v) ≠ -1 := auxiliary_ne_neg_one_of_strong_one p v hs

/-- The original assignment itself solves both new equations. -/
example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    (value71 p v=0 ∧ value72 p v=0) ↔ Carrier65.value p v=0 := by
  rw [positive_zero71_iff_original p v hb hv,positive_zero72_iff_original p v hb hv]
  exact and_self_iff

example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    MvPolynomial.eval v (polynomial71 p)=0 ↔
      MvPolynomial.eval v (Carrier65.polynomial p)=0 := by
  rw [eval_polynomial71,Carrier65.eval_polynomial]
  exact positive_zero71_iff_original p v hb hv

example : (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial72) ↔
    DiophantineConsistency.ConZFC := no_current_positive_zero72_iff_conZFC

#print axioms first_ne_zero
#print axioms main_ne_zero
#print axioms strong_ne_zero
#print axioms auxiliary_ne_zero
#print axioms auxiliary_ne_neg_one_of_strong_one
#print axioms positive_zero71_iff_original
#print axioms positive_zero72_iff_original
#print axioms eval_polynomial71
#print axioms eval_polynomial72
#print axioms no_current_positive_zero71_iff_conZFC
#print axioms no_current_positive_zero72_iff_conZFC

end DiophantineConsistency.CarrierNonzeroSpheresChecks
