import PA194Site27To4
import PA194Site27BranchRows
import PA194Path27Input
import PA194SourceSite25Physical
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroTo5
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PRAModelIOpenPairing PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- For a zero-valued source register 0, the site-27 physical dispatch and
    zero test reach control 5; all source registers and suffix stay symbolic. -/
theorem zeroTo5 (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    let v := physicalArgs e
    let e1 : Fin 10 → M := fun j => v j.succ
    let e2 : Fin 9 → M := fun j => e1 j.succ
    let e3 : Fin 8 → M := fun j => e2 j.succ
    let e4 : Fin 7 → M := fun j => e3 j.succ
    let e5 : Fin 6 → M := fun j => e4 j.succ
    let e6 : Fin 5 → M := fun j => e5 j.succ
    let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
    ∃ clock carried : M, let z := carried+carried+1
      F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 5,F pairCode ![(z+z)+(z+z)+1,t]] := by
  dsimp only
  let v := physicalArgs e
  let e1 : Fin 10 → M := fun j => v j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let e6 : Fin 5 → M := fun j => e5 j.succ
  let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
  have hz' : e6 0 = (0 : M) := hz
  have ht : F (fileCode 3) (fun i => e6 i.succ) = t+t := by
    rw [modelFileSucc,modelBlock]
    rfl
  have hq : F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)] = F ones ![(0 : M),t+t] := by
    rw [hz',ht]
  have hin := PA194Path27Input.site27Input k (F sourceFileCode e)
  dsimp only at hin
  have h := PA194Site27To4.site27To4 k e
  dsimp only at h
  rw [hq,hin] at h
  obtain ⟨clock,carried,hstart⟩ : ∃ clock carried : M, let z := carried+carried+1
      F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 4,F pairCode ![z+z,F ones ![(0 : M),t+t]]] := by
    exact ⟨_,_,h⟩
  let z := carried+carried+1
  have hrow := PA194Site27BranchRows.zeroRow z t
  refine ⟨F addCode ![clock,modelNumeral M 1],carried,?_⟩
  rw [PA194StepperCompose.modelStepperCompose,hstart]
  exact hrow
#print axioms zeroTo5
end models
end PA194Site27ZeroTo5
