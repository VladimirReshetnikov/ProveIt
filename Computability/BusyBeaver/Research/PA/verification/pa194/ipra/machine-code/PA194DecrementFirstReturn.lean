import PA194ReturnCell
import PA194ReturnFileMeaning
import PA194StepperCompose
import PA194ReturnedDecrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194DecrementFirstReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ReturnCell PA194ReturnFileMeaning PA194BinaryDouble
open PA194ReturnedDecrement PA194MarkedFile PA194CarryFile PA194ReturnFile
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- The positive-decrement output returns the consumed first run as an
ordinary block containing its residual value, not its initial value. -/
theorem returnResidual (m a p : M) :
    F PA194Stepper.stepper ![(m+1)+1,F pairCode ![modelNumeral M 7,
      F pairCode ![F ones ![m,(a+a)+(a+a)],p+p+1]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![a,F block ![m,p]+F block ![m,p]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelReturnCell m (a+a) p
  dsimp only at h
  rw [(modelDouble a).1,(modelDouble a).2,zero_add] at h
  have he : (1 : M)+p+p = p+p+1 := by simp only [add_assoc,add_comm]
  rw [he] at h
  have hb := modelReturnBlock m p
  rw [←hb]
  exact h
/-- Compose any proved positive-decrement endpoint with the return of the
first physical block, displaying the rest of the file as ordinary blocks. -/
theorem continuePositive (idx n : Nat) (e : Fin (idx+2) → M)
    (rest : Fin (n+2) → M) (v m a time start : M)
    (hrun :
      let tail := F (fileCode (n+1)) rest
      let ep := replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F markedBlock ![v,tail])
      let p := F (returnCode idx) (Fin.cases (F block ![F predCode (fun _ => v),tail]) ep)
      F PA194Stepper.stepper ![time,start] = F pairCode ![modelNumeral M 7,
        F pairCode ![F ones ![m,(a+a)+(a+a)],p+p+1]]) :
    let tail := F (fileCode (n+1)) rest
    let vals : Fin (idx+1) → M := fun i => e i.succ
    let p := F (fileCode idx) (replaceLast idx vals (F block ![F predCode (fun _ => v),tail]))
    F PA194Stepper.stepper ![time+((m+1)+1),start] =
      F pairCode ![modelNumeral M 7,F pairCode ![a,F block ![m,p]+F block ![m,p]]] := by
  dsimp only at hrun ⊢
  change F PA194Stepper.stepper ![F addCode ![time,(m+1)+1],start] = _
  rw [PA194StepperCompose.modelStepperCompose,hrun,returnResidual]
  rw [returnedUpdatedFile]
#print axioms continuePositive
#print axioms returnResidual
end models
end PA194DecrementFirstReturn
