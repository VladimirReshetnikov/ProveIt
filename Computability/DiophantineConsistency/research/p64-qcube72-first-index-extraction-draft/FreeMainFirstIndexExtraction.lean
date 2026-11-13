import FreeMainGraphResiduals
import DiophantineConsistency.ArithmeticPellFirstNorm

/-! Unchecked draft: classify the first Pell norm of an actual 72 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainFirstIndexExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPellFirstNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_index (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v) :
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let X := v 8*q
    let P := (X*Y)*Y
    let k := v 10+v 11
    ∃ n : V, n≤k ∧ xcoord n (2*(P-1)+1)=v 9 ∧
      2*ycoord n (2*(P-1)+1)=k := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun j => ι (v j)
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  obtain ⟨ha,_,_,_,_⟩ := FreeMainGraphResiduals.residuals p v hv hz
  change (P64QCube72Free.graph pp).A0.evalRing z=1 at ha
  rw [FreeMainGraphResiduals.first_same pp,P64QCube78GraphSplit.first_eval] at ha
  have hA : (ι (v 9):DiffRing V)*ι (v 9) -
      ((ι P:DiffRing V)*ι k)*((ι P)*ι k+ι k)=1 := by
    simpa [pp,z,q,Y,X,P,k] using ha
  have hnorm : v 9*v 9=1+P*(P+1)*k*k := by
    apply ι_injective
    simp only [map_add,map_mul,map_one]
    nlinarith [hA]
  have hq : 0<q := by dsimp [q]; simp
  have hY : 0<Y := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hX : 0<X := mul_pos (hv 8) hq
  have hP : 0<P := mul_pos (mul_pos hX hY) hY
  exact positive_parameter_solution P (v 9) k hP hnorm

#print axioms first_index
end FreeMainFirstIndexExtraction
