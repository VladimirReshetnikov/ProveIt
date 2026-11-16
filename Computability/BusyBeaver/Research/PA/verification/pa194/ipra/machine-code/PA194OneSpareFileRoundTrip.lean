import PA194OneSpareRoundTrip
import PA194OneSpareIdentities
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194OneSpareFileRoundTrip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194OneSpareIterate PA194OneSpareReturn PA194OneSpareRoundTrip PA194OneSpareIdentities PA194Site28CarryCell PA194ReturnCell PA194UnaryRuns PA194BinaryDouble PA194RegisterFile PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem outputBlockZero :
    F outputBlock (fun _ => (0 : M)) = ((1 : M)+1)+((1 : M)+1)+((1 : M)+1) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelOutputBlock,modelBlock]
  have h1 : F ones ![(1 : M),(0 : M)] = (1 : M) := by
    rw [←modelNumeralOne]
    change F ones ![F Code.succ (fun _ => modelNumeral M 0),(0 : M)] = _
    rw [modelOnesSucc,show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
    simp
    exact modelNumeralOne.symm
  have h2 : F ones ![(1 : M)+1,(0 : M)] = ((1 : M)+1)+1 := by
    rw [show (1 : M)+1 = F Code.succ (fun _ => (1 : M)) from modelAddOne _,modelOnesSucc,h1]
    exact congrArg (fun x => x + (1 : M)) (modelAddOne (1 : M))
  rw [h2]
  simp only [add_assoc,add_comm,add_left_comm]

theorem roundTrip (n spare marked : M) (hl : F parityCode (fun _ => marked) = (1 : M)) :
    let inSuffix := F repeatOutput ![n,(0 : M)]
    let outSuffix := F repeatOutput ![F Code.succ (fun _ => n),(0 : M)]
    let outFile := F block ![spare,outSuffix]
    F PA194Stepper.stepper ![(spare+1)+1,
      F PA194Stepper.stepper ![(n+n)+n,
        F PA194Stepper.stepper ![modelNumeral M 2,
          F PA194Stepper.stepper ![modelNumeral M 3,
            F PA194Stepper.stepper ![(n+n)+n,
              F PA194Stepper.stepper ![(1 : M)+(spare+1),
                F pairCode ![modelNumeral M 3,F pairCode ![marked,F ones ![spare+1,inSuffix]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => marked),outFile+outFile+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let base := F repeatBlock ![n,(0 : M)]
  let left := F ones ![spare+1,marked+marked]
  let t := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let q := F repeatOutput ![n,t]
  have hinput : F repeatOutput ![n,(0 : M)] = base+base := modelSuffixRelation n
  have hleft : left = F ones ![spare,marked+marked]+F ones ![spare,marked+marked]+1 := by
    dsimp only [left]
    rw [show spare+1 = F Code.succ (fun _ => spare) from modelAddOne _,modelOnesSucc]
  have hleftOdd : F parityCode (fun _ => left) = (1 : M) := by rw [hleft,(modelOdd _).1]
  have hleftHalf : F halfCode (fun _ => left) = F ones ![spare,marked+marked] := by rw [hleft,(modelOdd _).2]
  have first := PA194Site28CarryCell.carryCell spare marked base
  have middle := PA194OneSpareRoundTrip.roundTrip n left hleftOdd
  dsimp only at middle
  rw [hleftHalf] at middle
  have final := modelReturnCell spare marked q
  dsimp only at final
  rw [hl] at final
  have hq : q = F repeatOutput ![F Code.succ (fun _ => n),(0 : M)] := by
    dsimp only [q,t]
    rw [←outputBlockZero,modelOutputShift]
  have hout : F block ![spare,q] =
      F ones ![spare,(1 : M)+q+q]+F ones ![spare,(1 : M)+q+q] := by
    rw [←PA194ReturnFileMeaning.modelReturnBlock]
    have ha : q+q+1 = (1 : M)+q+q := by simp only [add_assoc,add_comm,add_left_comm]
    rw [ha]
  have hright : (1 : M)+(F ones ![spare,(1 : M)+q+q]+F ones ![spare,(1 : M)+q+q])+
      (F ones ![spare,(1 : M)+q+q]+F ones ![spare,(1 : M)+q+q]) =
      F block ![spare,q]+F block ![spare,q]+1 := by
    rw [hout]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hright] at final
  rw [hinput,first,middle,final,hq]
#print axioms outputBlockZero
#print axioms roundTrip
end models
end PA194OneSpareFileRoundTrip
