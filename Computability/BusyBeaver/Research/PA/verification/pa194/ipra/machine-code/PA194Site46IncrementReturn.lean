import PA194Site46IncrementSelected
import PA194Site35ReturnPrefix
import PA194Site31Selected
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site46IncrementReturn
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

/-- From the site-31 third-pass layout, traverse the four-register prefix,
increment logical register three, and return to the prefix boundary. -/
theorem incrementReturn (k d count : M) (args : Fin 11 → M)
    (he : physicalArgs args 10 = F repeatOutput ![count,(0 : M)]) :
    let v := physicalArgs args
    let e : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
    let marked := F (markedFile 5) e
    let ep : Fin 5 → M := ![v 0,v 1,v 2,v 3,marked]
    let file := F (fileCode 4) ep
    let pl := F (PA194PrefixFile.leftCode 4) (Fin.cases (F ones ![k+1,d+d]) ep)
    let c := F (costCode 5) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![count,six]
    let rest := F (returnCode 5) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 4) (Fin.cases result ep)
    let a := F ones ![k,(1 : M)+out+out]
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![F (costCode 4) ep,
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(count+count)+count,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(count+count)+count,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,
                    F PA194Stepper.stepper ![F (costCode 4) ep,
                      F PA194Stepper.stepper ![k+1,F pairCode ![modelNumeral M 2,
                        F pairCode ![d+d,F ones ![k,file+file+1]]]]]]]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => d),
      F parityCode (fun _ => d)+(a+a)+(a+a)]] := by
  dsimp only
  let v := physicalArgs args
  let e : Fin 7 → M := fun i => v ⟨i.val+4,by omega⟩
  let marked := F (markedFile 5) e
  let ep : Fin 5 → M := ![v 0,v 1,v 2,v 3,marked]
  let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let tail := F repeatOutput ![count,six]
  let rest := F (returnCode 5) (Fin.cases tail (fun i => e i.succ))
  let result := F block ![e 0+1,rest]
  have hi := PA194Site46IncrementSelected.incrementSelected k (d+d) count args he
  dsimp only at hi
  have hr := PA194Site35ReturnPrefix.returnPrefix 4 k d result ep
  dsimp only at hr
  rw [hi,hr]
#print axioms incrementReturn
end models
end PA194Site46IncrementReturn
