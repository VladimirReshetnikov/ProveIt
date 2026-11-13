import Trace74BoundaryNaturalSeed
import Trace74BoundaryGenericAssembly

/-! UNCHECKED DRAFT. Bind the certified finite natural Pell interval to the
model graph theorem, while retaining all remaining model facts explicitly. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74BoundarySeedSpecialization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open Trace75Factors Trace74Mask Trace74BoundarySeedParametric
open Trace74BoundaryRecurrenceCast Trace74BoundaryGenericAssembly
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def eta : ℕ := Trace74BoundaryNaturalSeed.C-Trace74BoundaryNaturalSeed.K*Trace74BoundaryNaturalSeed.Y
def zeta : ℕ := Trace74BoundaryNaturalSeed.K-eta

theorem finite_seed_data :
    0<eta ∧ 0<zeta ∧
    (xy 31 (Trace74BoundaryNaturalSeed.Y*(Trace74BoundaryNaturalSeed.X+1))).2 =
      2*(xy 16 (2*(Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y-1)+1)).2*
        Trace74BoundaryNaturalSeed.Y+eta ∧
    2*(xy 16 (2*(Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y-1)+1)).2=eta+zeta := by
  have hs := Trace74BoundaryNaturalSeed.slacks
  refine ⟨hs.1,hs.2.1,?_,?_⟩
  · change Trace74BoundaryNaturalSeed.C=Trace74BoundaryNaturalSeed.K*Trace74BoundaryNaturalSeed.Y+eta
    exact hs.2.2.1
  · change Trace74BoundaryNaturalSeed.K=eta+zeta
    exact hs.2.2.2

theorem zero_of_seed_model_facts (W S : V)
    (hW : 0<W) (hS : 0<S)
    (hX : X ports31 (source31 W S) = (Trace74BoundaryNaturalSeed.X:V))
    (hY : Y ports31 (source31 W S) = (Trace74BoundaryNaturalSeed.Y:V))
    (hbase : ((2*(Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y-1)+1 : ℕ):V) =
      2*((Trace74BoundaryNaturalSeed.X:V)*(Trace74BoundaryNaturalSeed.Y:V)*(Trace74BoundaryNaturalSeed.Y:V)-1)+1)
    (hphase : (2*(15:V)+1)%4=3)
    (hXeq : X ports31 (source31 W S)=Exp.exp (2*(15:V)+1))
    (h72 : 72*(15:V)<X ports31 (source31 W S)+1) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ w 0=1 ∧ w 1=1 ∧ w 2=1 ∧
      value74 (ports ports31) (fun j => ι (w j))=0 := by
  obtain ⟨heta,hzeta,hck,hk⟩ := finite_seed_data
  exact zero_of_pell_cast_data W S Trace74BoundaryNaturalSeed.X Trace74BoundaryNaturalSeed.Y eta zeta
    hW hS heta hzeta hX hY hbase hphase hXeq h72 hck hk

#print axioms Trace74BoundarySeedSpecialization.zero_of_seed_model_facts
end Trace74BoundarySeedSpecialization
