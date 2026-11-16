import PA194Site3671MarkedFile
import PA194Site35SelectedGeneric
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site3671Selected
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

theorem selectedFrom2 (k : M) (args : Fin 11 → M) :
    let e := PA194Site3671MarkedFile.selectedArgs args
    let ep := PA194Site3671MarkedFile.prefixArgs args
    let pl := F (PA194PrefixFile.leftCode 8) (Fin.cases (F ones ![k+1,modelNumeral M 56]) ep)
    let front := (((1 : M)+1)+e 0)+F (costCode 1) (fun i => e i.succ)
    F PA194Stepper.stepper ![((k+1)+F (costCode 8) ep)+front,
      F pairCode ![modelNumeral M 2,F pairCode ![modelNumeral M 56,F halfCode (fun _ => PA194Site3671SecondTo17.output k args)]]] =
      F pairCode ![(1 : M),F pairCode ![F (leftCode 1)
        (Fin.cases (F ones ![e 0,(pl+pl)+(pl+pl)+1]) (fun i => e i.succ)),e 2]] := by
  dsimp only
  let e := PA194Site3671MarkedFile.selectedArgs args
  let ep := PA194Site3671MarkedFile.prefixArgs args
  let file := F (fileCode 8) ep
  have hw : F ones ![k,file+file+1] = F ones ![k+1,file] := by
    rw [modelOnesCommute]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],file]
    rw [modelAddOne,modelOnesSucc]
  have hp : ep (Fin.last 8) = F (markedFile 1) e := rfl
  have hsel := PA194Site35SelectedGeneric.selectedThrough 8 1 (k+1) (modelNumeral M 56) ep e hp
  dsimp only at hsel
  have hf := PA194Site3671MarkedFile.markedInput k args
  change F halfCode (fun _ => PA194Site3671SecondTo17.output k args) = F ones ![k,file+file+1] at hf
  rw [hf,hw]
  exact hsel
#print axioms selectedFrom2
end models
end PA194Site3671Selected
