import PA194Site31DynamicTail
import PA194IncrementFront
import PA194ReturnFileMeaning
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site46DynamicIncrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194IncrementFront PA194ReturnFile PA194ReturnFileMeaning PA194ReturnCell PA194OnesCommute
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- Physical increment of a marked register and a five-block file, with a
model-valued number of one-valued trailing spares followed by blank tape. -/
theorem increment (n l : M) (e : Fin 7 → M)
    (he : e 6 = F repeatOutput ![n,(0 : M)]) :
    let selected := F ones ![e 0,(l+l)+(l+l)+1]
    let c := F (costCode 5) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![n,six]
    let rest := F (returnCode 5) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(n+n)+n,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(n+n)+n,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,F pairCode ![modelNumeral M 2,
                    F pairCode ![l,F (markedFile 5) e]]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(result+result)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let selected := F ones ![e 0,(l+l)+(l+l)+1]
  let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let tail := F repeatOutput ![n,six]
  let rest := F (returnCode 5) (Fin.cases tail (fun i => e i.succ))
  have hs := modelSelectedAndCarry 5 e l
  change e (Fin.last 6) = _ at he
  rw [he] at hs
  have ht := PA194Site31DynamicTail.tailRoundTrip n (F (leftCode 5) (Fin.cases selected (fun i => e i.succ)))
  dsimp only at ht
  have hr := modelReturnFile 5 (fun i => e i.succ) selected tail
  have hc := modelReturnCell (e 0+1) l rest
  dsimp only at hc
  have hselected : selected = F ones ![e 0+1,l+l] := by
    dsimp [selected]
    have hs : F ones ![e 0+1,l+l] = F ones ![e 0,l+l]+F ones ![e 0,l+l]+1 := by
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    rw [modelOnesCommute,hs]
  rw [hs,ht,hr,hselected,hc]
  have heq : (1 : M)+rest+rest = rest+rest+1 := by simp only [add_comm,add_left_comm]
  rw [heq,←modelReturnBlock]
  dsimp only [rest,tail,six]
  simp only [add_assoc]
#print axioms increment
end models
end PA194Site46DynamicIncrement
