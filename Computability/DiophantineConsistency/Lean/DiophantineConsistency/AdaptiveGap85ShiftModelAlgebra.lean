import DiophantineConsistency.ArithmeticPellRecurrence

/-! Ring-free identities behind the gap shift, valid in every IΣ₁ model. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftModelAlgebra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first-root positive and negative parts have equal cross-sums after the shift. -/
theorem first_root_cross (b q3 c U A k F q C r ell Y : V) :
    let M := q3*b
    let d := b*c*U
    let rp := r+d*A*k+c*U*A
    let Cp := C+d
    (M*(ell+k+rp)+Y*b+(M*k+q3)*(F*q))+(M*k+q3)*(C*A) =
    (M*(ell+k+r)+Y*b+(M*k+q3)*(F*q))+(M*k+q3)*(Cp*A) := by
  dsimp
  ring

/-- The signed main-root input `U*gamma+rank` is unchanged. -/
theorem main_root_cross (b c U H q F C gamma P : V) :
    let d := b*c*U
    let rq := q*q*H+P
    let rn := (F*q+C)*H
    let gp := gamma+b*c*H
    let rnp := (F*q+(C+d))*H
    (U*gp+rq)+rn=(U*gamma+rq)+rnp := by
  dsimp
  ring

/-- With the original T written as t plus its decrement, the signed
    auxiliary root is unchanged, without invoking subtraction or a quotient. -/
theorem aux_root_cross (b c U H q F C t P f : V) :
    let d := b*c*U
    let rq := q*q*H+P
    let rn := (F*q+C)*H
    let rnp := (F*q+(C+d))*H
    let T := t+b*U*H
    (f*f*(t*c+rnp))+(f*f*rq+c) =
    (f*f*(T*c+rn))+(f*f*rq+c) := by
  dsimp
  ring
end DiophantineConsistency.AdaptiveGap85ShiftModelAlgebra
