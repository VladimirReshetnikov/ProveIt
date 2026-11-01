import DiophantineConsistency.AdaptiveGap85ShiftModelAlgebra
import DiophantineConsistency.ArithmeticSignedPairs

/-! Model-internal signed root invariance for the gap shift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftModelPairs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs AdaptiveGap85ShiftModelAlgebra
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- First-root signed representations before and after the shift agree. -/
theorem first_root (b q3 c U A k F q C r ell Y : V) :
    let M := q3*b
    let d := b*c*U
    let rp := r+d*A*k+c*U*A
    let Cp := C+d
    Equivalent (M*(ell+k+rp)+Y*b+(M*k+q3)*(F*q),(M*k+q3)*(Cp*A))
      (M*(ell+k+r)+Y*b+(M*k+q3)*(F*q),(M*k+q3)*(C*A)) := by
  simpa only [Equivalent, add_comm] using first_root_cross b q3 c U A k F q C r ell Y

/-- Signed `U*gamma+rank` agrees before and after the shift. -/
theorem main_root (b c U H q F C gamma P : V) :
    let d := b*c*U
    let rq := q*q*H+P
    let rn := (F*q+C)*H
    let gp := gamma+b*c*H
    let rnp := (F*q+(C+d))*H
    Equivalent (U*gp+rq,rnp) (U*gamma+rq,rn) := by
  simpa only [Equivalent, add_comm] using main_root_cross b c U H q F C gamma P

/-- Signed auxiliary-root representations agree when T contains the decrement. -/
theorem auxiliary_root (b c U H q F C t P f : V) :
    let d := b*c*U
    let rq := q*q*H+P
    let rn := (F*q+C)*H
    let rnp := (F*q+(C+d))*H
    let T := t+b*U*H
    Equivalent (f*f*(t*c+rnp),f*f*rq+c) (f*f*(T*c+rn),f*f*rq+c) := by
  simpa only [Equivalent, add_comm] using aux_root_cross b c U H q F C t P f
end DiophantineConsistency.AdaptiveGap85ShiftModelPairs
