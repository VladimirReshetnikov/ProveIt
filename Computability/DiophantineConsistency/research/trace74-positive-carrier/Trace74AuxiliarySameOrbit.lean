import Trace74CoupledCarrierShift

/-! The quotient and ordinate from the same auxiliary Pell orbit satisfy its norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74AuxiliarySameOrbit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem quotient_ordinate_norm (I h : V) (hI : 2≤I) :
    let Q := oddQuotient h (I-2)
    let y := ycoord (2*h+1) (I-2)
    I*I*Q*Q+y*y=1+I*I*y*y := by
  let b := I-2
  let Q := oddQuotient h b
  let y := ycoord (2*h+1) b
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hdelta : delta b+1=(b+2)*(b+2) := by unfold delta; ring
  have hx : xcoord (2*h+1) b=I*Q := by rw [odd_exact, hb]
  calc
    I*I*Q*Q+y*y=xcoord (2*h+1) b*xcoord (2*h+1) b+y*y := by rw [hx]; ring
    _=1+delta b*y*y+y*y := by rw [norm]
    _=1+(delta b+1)*y*y := by ring
    _=1+I*I*y*y := by rw [hdelta,hb]

#print axioms Trace74AuxiliarySameOrbit.quotient_ordinate_norm
end Trace74AuxiliarySameOrbit
