import PA194HXSourceArgs
import PA194HXRootEncoding
import PA194HXBoxAgreement
import PA194CompressedControllerStep
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194HXControllerStepAt
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion TableDispatch PA194StateOne PA194FiniteControls
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceBoundedStep
open PA194CompressedSourceFrame PA194HXSourceRoot PA194HXSourceArgs
open PA194CompressedBoxOracle PA194CompressedBoxFiles PA194CompressedIncrementOracle
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A certified instruction gives a positive HX physical segment once its
    source-state transition and box endpoints are identified. -/
theorem stepAt (s s' gap count spare nextCount : M) (i j : Fin 3673)
    (hi : F pc ![s] = modelNumeral M i.val) (hj : F pc ![s'] = modelNumeral M j.val)
    (br : Branch) (hb : BranchOK (tapeArgs s count spare) br) (extra : Bool) (eff : Eff)
    (hc : PA194HXContractSound.contract br i.val j.val (if extra then 1 else 0) 512 eff = true)
    (hout : boxValue (tapeArgs s count spare) (incremented (tapeArgs s count spare) count) (.plain eff) =
      file (tapeArgs s' nextCount spare)) :
    Reach1 PA194HXDispatch.table (F PA194HXSourceRoot.sourceRootCode ![s,gap,count,spare])
      (F PA194HXSourceRoot.sourceRootCode ![s',(if extra then gap+1 else gap),nextCount,spare]) := by
  rw [PA194HXSourceRoot.sourceRootCodeCorrect s gap count spare i hi,PA194HXSourceRoot.sourceRootCodeCorrect _ _ _ _ j hj]
  let a := tapeArgs s count spare
  let inc := incremented a count
  have hbox := PA194HXBoxAgreement.concreteBoxAgreement a count br (readTail s count spare) hb
  have hin : boxValue a inc (.plain .none) = F PA194HXAllocation.sourceFileCode (args s count spare) :=
    (frameFile s count spare).symm
  rw [← frameFile] at hout
  have h := PA194HXRootEncoding.contractFrames gap hbox i.val j.val (if extra then 1 else 0)
    512 eff (args s count spare) (args s' nextCount spare) hin hout hc
  cases extra
  · exact h
  · simp only [if_true] at h ⊢
    rw [PA194CompressedControllerStep.shiftOffset] at h
    exact h

#print axioms stepAt
end models
end PA194HXControllerStepAt
