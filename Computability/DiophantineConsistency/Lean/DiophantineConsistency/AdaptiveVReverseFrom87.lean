import DiophantineConsistency.AdaptiveVReversePreserve
import DiophantineConsistency.AdaptiveVReverseSign
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveVReverseFrom87
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Lift
open AdaptiveDirectOrdinate86AuxNorm AdaptiveDirectOrdinate86Reverse.VPreserveProbe AdaptiveVReverseSign
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def inflate (v : Fin 13 → V) : Fin 14 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,1,v 12,v 11]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem inflate_old (v : Fin 13 → V) : (fun i => inflate v (oldIndex i)) = v := by
  funext i
  fin_cases i <;> rfl

theorem from87 (p : Fin 4 → ℕ) (v : Fin 13 → V) (hb : 0<(p 0:V))
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 (fun j => (p j:ℤ))) v)
    (hsign : (pairEval (eV (fun j => (p j:ℤ))) v).2 < (pairEval (eV (fun j => (p j:ℤ))) v).1) :
    ∃ w : Fin 13 → V, (∀ i, 0 < w i) ∧ InternalZero (expressionAt86 (fun j => (p j:ℤ))) w ∧
      (pairEval (eV (fun j => (p j:ℤ))) w).2 < (pairEval (eV (fun j => (p j:ℤ))) w).1 := by
  let v14 := inflate v
  have he : (fun i => v14 (oldIndex i)) = v := inflate_old v
  have hp : ∀ i, 0 < v14 (oldIndex i) := by
    intro i
    rw [congrFun he i]
    exact hv i
  have hz' : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 (fun j => (p j:ℤ))) (fun i => v14 (oldIndex i)) := by rw [he]; exact hz
  obtain ⟨w,hw,hwzero,hcoords⟩ := old_positive_zero_to_new_with_coordinates p v14 hb hp hz'
  have hcoords' : ∀ i, i ≠ 11 → w i = v i := by
    intro i hi
    rw [hcoords i hi]
    exact congrFun he i
  have h := eV_congr (fun j => (p j:ℤ)) v w hcoords'
  refine ⟨w,hw,hwzero,?_⟩
  rw [h]
  exact hsign
#print axioms from87
end DiophantineConsistency.AdaptiveVReverseFrom87
