import FreeMainGraphShape
import P64QCube77Unit

/-! Unchecked draft: split an actual 72 graph zero into the five residuals. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainGraphResiduals
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_same (p : Fin 4 → ℤ) : (P64QCube72Free.graph p).A0=(P64QCube78.graph p).A0 := by rfl
theorem transport_same (p : Fin 4 → ℤ) : (P64QCube72Free.graph p).Lt=(P64QCube78.graph p).Lt := by rfl

theorem residuals (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v) :
    let g := P64QCube72Free.graph (fun j => (p j:ℤ))
    let z : Fin 14 → DiffRing V := fun i => ι (v i)
    g.A0.evalRing z=1 ∧ g.M.evalRing z=0 ∧ g.W.evalRing z=0 ∧
      g.Na.evalRing z=1 ∧ g.Lt.evalRing z=0 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let g := P64QCube72Free.graph pp
  let a := g.A0.evalRing z
  let m := g.M.evalRing z
  let w := g.W.evalRing z
  let n := g.Na.evalRing z
  let l := g.Lt.evalRing z
  have hs : (a*n-1)*(a*n-1)+m*m+w*w+l*l=0 := by
    rw [internalZero_iff,FreeMainGraphShape.output_shape] at hz
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat,Nat.cast_one] at hz
    exact hz
  have hu := mul_self_nonneg (a*n-1)
  have hm := mul_self_nonneg m
  have hw := mul_self_nonneg w
  have hl := mul_self_nonneg l
  have hunit : a*n=1 := sub_eq_zero.mp (mul_self_eq_zero.mp (by linarith))
  have hm0 : m=0 := mul_self_eq_zero.mp (by linarith)
  have hw0 : w=0 := mul_self_eq_zero.mp (by linarith)
  have hl0 : l=0 := mul_self_eq_zero.mp (by linarith)
  have hlt : InternalZero (P64QCube78.graph pp).Lt v := by
    rw [internalZero_iff,←transport_same pp]
    exact hl0
  have haneg : a≠ -1 := by
    change (P64QCube72Free.graph pp).A0.evalRing z≠ -1
    rw [first_same pp]
    exact P64QCube77Unit.first_ne_neg_of_transport p v hv hlt
  obtain ⟨ha,hn⟩ := P64QCube77Unit.positive_factors hunit haneg
  exact ⟨ha,hm0,hw0,hn,hl0⟩


#print axioms FreeMainGraphResiduals.first_same
#print axioms FreeMainGraphResiduals.transport_same
#print axioms FreeMainGraphResiduals.residuals
end FreeMainGraphResiduals
