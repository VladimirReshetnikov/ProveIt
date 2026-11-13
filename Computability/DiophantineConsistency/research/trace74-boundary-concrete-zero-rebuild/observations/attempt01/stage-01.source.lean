import Trace74BoundarySeedModelFacts
import Trace74BoundarySeedSpecialization

/-! UNCHECKED DRAFT. Compose the seed model facts with the conditional
specialization, retaining the same witness and its guard equality. The ports
are (1,1,28,0), not the fixed BFS tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74BoundaryConcreteZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open Trace75Factors Trace74Mask Trace74BoundarySeedParametric
open Trace74BoundarySeedSpecialization Trace74BoundarySeedModelFacts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_with_boundary :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ w 0=1 ∧ w 1=1 ∧ w 2=1 ∧
      value74 (ports ports31) (fun j => ι (w j))=0 ∧
      q ports31 w = w 1+w 2 := by
  obtain ⟨hW,hS,hX,hY,hbase,hphase,hXeq,h72⟩ := model_facts (V:=V)
  obtain ⟨w,hw,hw0,hw1,hw2,hzero⟩ :=
    zero_of_seed_model_facts (W (V:=V)) (S (V:=V)) hW hS hX hY hbase hphase hXeq h72
  refine ⟨w,hw,hw0,hw1,hw2,hzero,?_⟩
  simp [q,b,ports31,hw0,hw1,hw2]

#print axioms Trace74BoundaryConcreteZero.positive_zero_with_boundary
end Trace74BoundaryConcreteZero
