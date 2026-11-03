import Trace74BoundaryGenericCastTransfer
import Trace74BoundarySeedParametric

/-! UNCHECKED DRAFT. Compose generic model cast-transfer with the conditional
boundary theorem while keeping all concrete coordinate and numerical facts
explicit. This source does not instantiate the audited finite seed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74BoundaryGenericAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open Trace75Factors Trace74Mask Trace74BoundarySeedParametric
open Trace74BoundaryRecurrenceCast Trace74BoundaryGenericCastTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_of_pell_cast_data (W S : V) (x y eta zeta : ℕ)
    (hW : 0<W) (hS : 0<S) (heta : 0<eta) (hzeta : 0<zeta)
    (hX : X ports31 (source31 W S) = (x:V))
    (hY : Y ports31 (source31 W S) = (y:V))
    (hbase : ((2*(x*y*y-1)+1 : ℕ):V) = 2*((x:V)*(y:V)*(y:V)-1)+1)
    (hphase : (2*(15:V)+1)%4=3)
    (hXeq : X ports31 (source31 W S)=Exp.exp (2*(15:V)+1))
    (h72 : 72*(15:V)<X ports31 (source31 W S)+1)
    (hck : (xy 31 (y*(x+1))).2 =
      2*(xy 16 (2*(x*y*y-1)+1)).2*y+eta)
    (hk : 2*(xy 16 (2*(x*y*y-1)+1)).2=eta+zeta) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ w 0=1 ∧ w 1=1 ∧ w 2=1 ∧
      value74 (ports ports31) (fun j => ι (w j))=0 := by
  obtain ⟨hetaV,hzetaV,hckV,hkV⟩ :=
    transfer x y eta zeta heta hzeta hbase hck hk
  have h31 : 2*(15:V)+1=31 := by ring
  have h16 : (15:V)+1=16 := by ring
  apply positive_boundary_of_source W S (eta:V) (zeta:V) hW hS hetaV hzetaV hphase hXeq h72
  · rw [h31,h16,hX,hY]
    exact hckV
  · rw [h16,hX,hY]
    exact hkV

#print axioms Trace74BoundaryGenericAssembly.zero_of_pell_cast_data
end Trace74BoundaryGenericAssembly
