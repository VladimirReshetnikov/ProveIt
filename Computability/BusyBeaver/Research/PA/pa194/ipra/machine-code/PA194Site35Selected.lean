import PA194Site35MarkedFile
import PA194Site35SelectedGeneric
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site35Selected
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194OnesCommute PA194StateOne TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  let e := PA194Site35MarkedFile.selectedArgs args
  let ep := PA194Site35MarkedFile.prefixArgs args
  let front := (((1 : M)+1)+e 0)+F (costCode 4) (fun i => e i.succ)
  let c := F addCode ![F addCode ![F addCode ![PA194Site35To14.clock k args,modelNumeral M 3],PA194Site35SecondTo17.backCost k args],modelNumeral M 25]
  F addCode ![F addCode ![c,modelNumeral M 10],((k+1)+F (costCode 5) ep)+front]

theorem selected (k : M) (args : Fin 11 → M) :
    let e := PA194Site35MarkedFile.selectedArgs args
    let ep := PA194Site35MarkedFile.prefixArgs args
    let pl := F (PA194PrefixFile.leftCode 5) (Fin.cases (F ones ![k+1,modelNumeral M 1608]) ep)
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 35 ((k+1)+1) args] =
      F pairCode ![(1 : M),F pairCode ![F (leftCode 4)
        (Fin.cases (F ones ![e 0,(pl+pl)+(pl+pl)+1]) (fun i => e i.succ)),e 5]] := by
  dsimp only
  let e := PA194Site35MarkedFile.selectedArgs args
  let ep := PA194Site35MarkedFile.prefixArgs args
  let file := F (fileCode 5) ep
  have hw : F ones ![k,file+file+1] = F ones ![k+1,file] := by
    rw [modelOnesCommute]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],file]
    rw [modelAddOne,modelOnesSucc]
  have hp : ep (Fin.last 5) = F (markedFile 4) e := rfl
  have hsel := PA194Site35SelectedGeneric.selectedThrough 5 4 (k+1) (modelNumeral M 1608) ep e hp
  dsimp only at hsel
  have h2 := PA194Site35To2.to2 k args
  dsimp only at h2
  have hf := PA194Site35MarkedFile.markedInput k args
  change F halfCode (fun _ => PA194Site35SecondTo17.output k args) = F ones ![k,file+file+1] at hf
  rw [hf,hw] at h2
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h2,hsel]
  rfl
#print axioms selected
end models
end PA194Site35Selected
