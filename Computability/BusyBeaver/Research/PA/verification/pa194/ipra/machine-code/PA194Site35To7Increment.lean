import PA194Site35IncrementSelected
import PA194Site35DynamicIncrement
import PA194Site35To2
import PA194Site35MarkedFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site35To7Increment
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194BinaryDouble PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194OnesCommute PA194RightRows PA194StateOne PA194ReturnFile
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem incrementTo7 (k count : M) (args : Fin 11 → M)
    (he : physicalArgs args 10 = F repeatOutput ![count,(0 : M)]) :
    let l := modelNumeral M 1608
    let v := physicalArgs args
    let e : Fin 6 → M := fun i => v ⟨i.val+5,by omega⟩
    let marked := F (markedFile 4) e
    let ep : Fin 6 → M := ![v 0,v 1,v 2,v 3,v 4,marked]
    let file := F (fileCode 5) ep
    let pl := F (PA194PrefixFile.leftCode 5) (Fin.cases (F ones ![k+1,l]) ep)
    let c := F (costCode 4) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 4) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(count+count)+count,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(count+count)+count,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,
                    F PA194Stepper.stepper ![F (costCode 5) ep,
                      F PA194Stepper.stepper ![k+1,F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![F addCode ![PA194Site35To14.clock k args,modelNumeral M 3],PA194Site35SecondTo17.backCost k args],modelNumeral M 25],modelNumeral M 10],
                        PA194SourceSite31Physical.physicalFrame 35 ((k+1)+1) args]]]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => pl),
      F parityCode (fun _ => pl)+(result+result)]] := by
  dsimp only
  let v := physicalArgs args
  let e : Fin 6 → M := fun i => v ⟨i.val+5,by omega⟩
  let ep : Fin 6 → M := ![v 0,v 1,v 2,v 3,v 4,F (markedFile 4) e]
  let file := F (fileCode 5) ep
  have hfile := PA194Site35MarkedFile.markedInput k args
  change F halfCode (fun _ => PA194Site35SecondTo17.output k args) = F ones ![k,file+file+1] at hfile
  have h2 := PA194Site35To2.to2 k args
  dsimp only at h2
  rw [hfile] at h2
  have hi := PA194Site35IncrementSelected.incrementSelected k (modelNumeral M 1608) count args he
  dsimp only at hi
  rw [h2]
  exact hi
#print axioms incrementTo7
end models
end PA194Site35To7Increment
