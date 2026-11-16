import PA194Site35DynamicIncrement
import PA194Site31Selected
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site35IncrementSelected
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194OnesCommute PA194RightRows PA194StateOne PA194ReturnFile
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- From the site-31 third-pass layout, traverse the five-register prefix,
increment logical register seven, and return to the prefix boundary. -/
theorem incrementSelected (k l count : M) (args : Fin 11 → M)
    (he : physicalArgs args 10 = F repeatOutput ![count,(0 : M)]) :
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
                      F PA194Stepper.stepper ![k+1,F pairCode ![modelNumeral M 2,
                        F pairCode ![l,F ones ![k,file+file+1]]]]]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => pl),
      F parityCode (fun _ => pl)+(result+result)]] := by
  dsimp only
  let v := physicalArgs args
  let e : Fin 6 → M := fun i => v ⟨i.val+5,by omega⟩
  let marked := F (markedFile 4) e
  let ep : Fin 6 → M := ![v 0,v 1,v 2,v 3,v 4,marked]
  let file := F (fileCode 5) ep
  let pl := F (PA194PrefixFile.leftCode 5) (Fin.cases (F ones ![k+1,l]) ep)
  have hword : F ones ![k,file+file+1] = F ones ![k+1,file] := by
    rw [modelOnesCommute]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],file]
    rw [modelAddOne,modelOnesSucc]
  have hloop (x y : M) : F PackedClock.encodedStep
      (fun _ => F pairCode ![modelNumeral M 2,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 2,F pairCode ![x+x+1,y]] := by
    have h := rightOne 2 1 2 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h
  have hscan := PA194GenericRightScan.modelFullScan 2 hloop (k+1) l file
  have hf := PA194PrefixFile.modelPrefixFile 5 ep (F ones ![k+1,l])
  have hp : ep (Fin.last 5) = F (markedFile 4) e := by rfl
  rw [hp] at hf
  have hs : e 5 = F repeatOutput ![count,(0 : M)] := he
  have hi := PA194Site35DynamicIncrement.increment count pl e hs
  dsimp only at hi
  rw [hword,hscan,hf,hi]
#print axioms incrementSelected
end models
end PA194Site35IncrementSelected
