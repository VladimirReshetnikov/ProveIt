import PA194Site3671To7Increment
import PA194Site3671MarkedFile
import PA194Site39IncrementReturn
import PA194Site3671IncrementSelected
import PA194Site35ReturnPrefix
import PA194Site31Selected
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site3671ToHeaderReturn
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

theorem toHeaderReturn (k count : M) (args : Fin 11 → M)
    (he : physicalArgs args 10 = F repeatOutput ![count,(0 : M)]) :
    let d := modelNumeral M 28
    let v := physicalArgs args
    let e : Fin 3 → M := fun i => v ⟨i.val+8,by omega⟩
    let marked := F (markedFile 1) e
    let ep : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,marked]
    let file := F (fileCode 8) ep
    let pl := F (PA194PrefixFile.leftCode 8) (Fin.cases (F ones ![k+1,d+d]) ep)
    let c := F (costCode 1) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 1) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 8) (Fin.cases result ep)
    let a := F ones ![k,(1 : M)+out+out]
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![F (costCode 8) ep,
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(count+count)+count,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(count+count)+count,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,
                    F PA194Stepper.stepper ![F (costCode 8) ep,
                      F PA194Stepper.stepper ![k+1,PA194Site3671To7Increment.runTo2 k args]]]]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => d),
      F parityCode (fun _ => d)+(a+a)+(a+a)]] := by
  dsimp only
  let v := physicalArgs args
  let e : Fin 3 → M := fun i => v ⟨i.val+8,by omega⟩
  let ep : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,F (markedFile 1) e]
  let file := F (fileCode 8) ep
  have hfile := PA194Site3671MarkedFile.markedInput k args
  change F halfCode (fun _ => PA194Site3671SecondTo17.output k args) = F ones ![k,file+file+1] at hfile
  have h2 := PA194Site3671To2.to2 k args
  dsimp only at h2
  change PA194Site3671To7Increment.runTo2 k args = _ at h2
  rw [hfile] at h2
  have hi := PA194Site39IncrementReturn.incrementReturn k (modelNumeral M 28) count args he
  dsimp only at hi
  have hn : modelNumeral M 28+modelNumeral M 28 = modelNumeral M 56 := by rw [←PA194FiniteControls.modelNumeralAdd]
  rw [hn] at hi
  rw [h2]
  exact hi
#print axioms toHeaderReturn
end models
end PA194Site3671ToHeaderReturn
