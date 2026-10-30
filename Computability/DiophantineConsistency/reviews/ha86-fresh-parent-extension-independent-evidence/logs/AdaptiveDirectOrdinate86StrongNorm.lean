import DiophantineConsistency.AdaptiveDirectOrdinate86Comparison
import DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011

/-! Strong Pell norm from the actual direct-ordinate 86 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86StrongNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveStrongNorm2011 AdaptiveDirectOrdinate86Literal
open AdaptiveDirectOrdinate86Factors AdaptiveDirectOrdinate86Units
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem represented_unit {p : Pair V} {a b : V}
    (hu : p.1=p.2+1) (hr : Equivalent p (a,b)) : a=b+1 := by
  change p.1+b=p.2+a at hr
  have h : p.2+(1+b)=p.2+a := calc
    _=(p.2+1)+b := by ring
    _=p.1+b := by rw [hu]
    _=p.2+a := hr
  have h' := add_left_cancel h
  simpa only [add_comm] using h'.symm

theorem expressionAt_strong_norm86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : StrongNorm v := by
  have hu := (expressionAt_factor_units86 (fun j => (p j:ℤ)) v hz).2.2.2
  rw [strong_factor_eq] at hu
  have hr := strong_rep p v
  have h := represented_unit hu hr
  have h' : 1+((v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))*v 4*
      ((v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))*v 4)+
      ((3+4*(v 6*v 7+v 7))+(v 6*v 7+v 7)*(v 6*v 7+v 7))) =
      1+(((3+4*(v 6*v 7+v 7))+(v 6*v 7+v 7)*(v 6*v 7+v 7))*(v 3*v 3)) := by
    calc
      _=(1+((v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))*v 4*
        ((v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))*v 4))+
        ((3+4*(v 6*v 7+v 7))+(v 6*v 7+v 7)*(v 6*v 7+v 7))) := by ring
      _=_ := by rw [h]; ring
  exact add_left_cancel h'

end DiophantineConsistency.AdaptiveDirectOrdinate86StrongNorm
