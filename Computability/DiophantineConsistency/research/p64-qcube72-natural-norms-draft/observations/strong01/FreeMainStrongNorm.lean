import FreeMainGraphResiduals
import P64QCubeBinding

/-! Unchecked draft: natural strong norm from an actual 72 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainStrongNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem strong_same (p : Fin 4 → ℤ) : (P64QCube72Free.graph p).W=(P64QCube81.graph p).W := by rfl

theorem strong (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v) :
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let X := v 8*q
    let a := X*Y+Y
    let c := (v 10+v 11)*Y+v 10
    (v 5*c*c)*(v 5*c*c)+delta a=delta a*(v 4*v 4) := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let a : V := X*Y+Y
  let c : V := (v 10+v 11)*Y+v 10
  obtain ⟨_,_,hw,_,_⟩ := FreeMainGraphResiduals.residuals p v hv hz
  have hW : InternalZero (P64Graph.graph pp).W w := by
    rw [internalZero_iff]
    change (P64QCube72Free.graph pp).W.evalRing z=0 at hw
    rw [strong_same pp,←P64QCubeBinding.strong pp z,←P64QCubeMap.lift_cast p v] at hw
    exact hw
  have hs := P64Root.strong p w hW
  have hs' : (v 5*(c*c))*(v 5*(c*c))+(a*a+(4*a+3)) =
      (a*a+(4*a+3))*(v 4*v 4) := by
    simpa [w,lift,q,Y,X,a,c] using hs
  have hd : a*a+(4*a+3)=delta a := by unfold delta; ring
  simpa only [←hd,mul_assoc] using hs'

#print axioms FreeMainStrongNorm.strong_same
#print axioms FreeMainStrongNorm.strong
end FreeMainStrongNorm
