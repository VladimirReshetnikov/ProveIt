import Trace74BoundaryRecurrenceCast

/-! UNCHECKED DRAFT. Transfer a finite natural Pell interval into an arbitrary
IΣ₁ model using common coordinates. The only subtraction cast needed for
this generic step is kept explicit. No concrete seed or graph zero is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74BoundaryGenericCastTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellRecurrence
open Trace74BoundaryRecurrenceCast
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem transfer (x y eta zeta : ℕ)
    (heta : 0 < eta) (hzeta : 0 < zeta)
    (hbase : ((2*(x*y*y-1)+1 : ℕ) : V) =
      2*((x:V)*(y:V)*(y:V)-1)+1)
    (hck : (xy 31 (y*(x+1))).2 =
      2*(xy 16 (2*(x*y*y-1)+1)).2*y+eta)
    (hk : 2*(xy 16 (2*(x*y*y-1)+1)).2=eta+zeta) :
    0<(eta:V) ∧ 0<(zeta:V) ∧
    ycoord (31:V) ((y:V)*((x:V)+1)) =
      2*ycoord (16:V) (2*((x:V)*(y:V)*(y:V)-1)+1)*(y:V)+(eta:V) ∧
    2*ycoord (16:V) (2*((x:V)*(y:V)*(y:V)-1)+1) = (eta:V)+(zeta:V) := by
  have he : 0<(eta:V) := Nat.cast_pos.mpr heta
  have hz : 0<(zeta:V) := Nat.cast_pos.mpr hzeta
  have hfirst := (xy_cast (V:=V) 16 (2*(x*y*y-1)+1)).2
  rw [hbase] at hfirst
  have hmain := (xy_cast (V:=V) 31 (y*(x+1))).2
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hmain
  simp only [Nat.cast_ofNat] at hfirst hmain
  have hckV := congrArg (fun n : ℕ => (n:V)) hck
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hckV
  have hkV := congrArg (fun n : ℕ => (n:V)) hk
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hkV
  refine ⟨he,hz,?_,?_⟩
  · rw [hmain,hfirst]
    exact hckV
  · rw [hfirst]
    exact hkV

#print axioms Trace74BoundaryGenericCastTransfer.transfer
end Trace74BoundaryGenericCastTransfer
