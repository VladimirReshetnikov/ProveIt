import Trace74BoundaryNaturalSeed
import Trace74BoundarySeedParametric

/-! UNCHECKED DRAFT. Attach the finite natural interval to the two source
Pell equations. Positivity of the selected values, source X/Y identification,
phase, exponential and growth are deliberately explicit assumptions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74BoundaryNaturalAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open Trace75Factors Trace74Mask Trace74BoundarySeedParametric
open Trace74BoundaryRecurrenceCast

def W : ℕ := 2^30

theorem zero_of_explicit_coordinates
    (hW : 0 < W) (hS : 0 < Trace74BoundaryNaturalSeed.S)
    (hX : X ports31 (source31 W Trace74BoundaryNaturalSeed.S) = Trace74BoundaryNaturalSeed.X)
    (hY : Y ports31 (source31 W Trace74BoundaryNaturalSeed.S) = Trace74BoundaryNaturalSeed.Y)
    (hphase : (2*(15:ℕ)+1)%4=3)
    (hXeq : X ports31 (source31 W Trace74BoundaryNaturalSeed.S)=Exp.exp (2*(15:ℕ)+1))
    (h72 : 72*(15:ℕ)<X ports31 (source31 W Trace74BoundaryNaturalSeed.S)+1) :
    ∃ w : Fin 10 → ℕ, (∀ j,0<w j) ∧ w 0=1 ∧ w 1=1 ∧ w 2=1 ∧
      value74 (ports ports31) (fun j => ι (w j))=0 := by
  let eta := Trace74BoundaryNaturalSeed.C-Trace74BoundaryNaturalSeed.K*Trace74BoundaryNaturalSeed.Y
  let zeta := Trace74BoundaryNaturalSeed.K-eta
  have hetap : 0<eta := Trace74BoundaryNaturalSeed.slacks.1
  have hzetap : 0<zeta := Trace74BoundaryNaturalSeed.slacks.2.1
  have hyfirst : ycoord (16:ℕ) Trace74BoundaryNaturalSeed.firstBase = (xy 16 Trace74BoundaryNaturalSeed.firstBase).2 :=
    (xy_cast (V:=ℕ) 16 Trace74BoundaryNaturalSeed.firstBase).2
  have hymain : ycoord (31:ℕ) (Trace74BoundaryNaturalSeed.Y*(Trace74BoundaryNaturalSeed.X+1)) = (xy 31 (Trace74BoundaryNaturalSeed.Y*(Trace74BoundaryNaturalSeed.X+1))).2 :=
    (xy_cast (V:=ℕ) 31 (Trace74BoundaryNaturalSeed.Y*(Trace74BoundaryNaturalSeed.X+1))).2
  have hk : 2*ycoord (16:ℕ) Trace74BoundaryNaturalSeed.firstBase=Trace74BoundaryNaturalSeed.K := by
    rw [hyfirst]
    rfl
  have hc : ycoord (31:ℕ) (Trace74BoundaryNaturalSeed.Y*(Trace74BoundaryNaturalSeed.X+1))=Trace74BoundaryNaturalSeed.C := by
    rw [hymain]
    rfl
  have hck : ycoord (31:ℕ) (Trace74BoundaryNaturalSeed.Y*(Trace74BoundaryNaturalSeed.X+1))=
      2*ycoord (16:ℕ) Trace74BoundaryNaturalSeed.firstBase*Trace74BoundaryNaturalSeed.Y+eta := by
    rw [hc,hk]
    exact Trace74BoundaryNaturalSeed.slacks.2.2.1
  have hks : 2*ycoord (16:ℕ) Trace74BoundaryNaturalSeed.firstBase=eta+zeta := by
    rw [hk]
    exact Trace74BoundaryNaturalSeed.slacks.2.2.2
  apply positive_boundary_of_source W Trace74BoundaryNaturalSeed.S eta zeta hW hS hetap hzetap hphase hXeq h72
  · rw [hX,hY]
    exact hck
  · rw [hX,hY]
    exact hks

#print axioms Trace74BoundaryNaturalAssembly.zero_of_explicit_coordinates
end Trace74BoundaryNaturalAssembly
