import PA194IncrementAnywhere
import PA194TwoScanInvariant
import PA194OnesCommute
import PA194ReturnCell
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194MarkedIncrementHead
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile
open PA194IncrementAnywhere PA194OnesCommute PA194ReturnCell PA194ReturnFileMeaning PA194BinaryDouble
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
/-- A partially scanned first regular block, seven-block prefix, and
marked eighth block execute the increment box, then return the first block. -/
theorem incrementAfterHead (k a : M) (ep : Fin 8 → M) (e : Fin 3 → M)
    (hp : ep (Fin.last 7) = F (markedFile 1) e)
    (he : e (Fin.last 2) = (0 : M)) :
    let f := F (fileCode 7) ep
    let prefixCost := F (costCode 7) ep
    let front := (((1 : M)+1)+e 0)+F (costCode 1) (fun i => e i.succ)
    let incrementCost := ((front+modelNumeral M 6)+F (costCode 1) (fun i => e i.succ))+((e 0+1)+1+1)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (fileCode 1) (replaceLast 1 (fun i => e i.succ) six)
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 7) (Fin.cases result ep)
    let clock := (prefixCost+incrementCost)+prefixCost
    F PA194Stepper.stepper ![((k+1)+clock)+((k+1)+1),F pairCode ![modelNumeral M 2,
      F pairCode ![(a+a)+(a+a),F ones ![k,(1 : M)+f+f]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![a,F block ![k,out]+F block ![k,out]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let f := F (fileCode 7) ep
  let L := (a+a)+(a+a)
  let prefixCost := F (costCode 7) ep
  let front := (((1 : M)+1)+e 0)+F (costCode 1) (fun i => e i.succ)
  let incrementCost := ((front+modelNumeral M 6)+F (costCode 1) (fun i => e i.succ))+((e 0+1)+1+1)
  let clock := (prefixCost+incrementCost)+prefixCost
  let c3 := ((1 : M)+1)+1
  let six := c3+c3
  let rest := F (fileCode 1) (replaceLast 1 (fun i => e i.succ) six)
  let result := F block ![e 0+1,rest]
  let out := F (returnCode 7) (Fin.cases result ep)
  let left := F ones ![k,L]
  have hcomm : F ones ![k,(1 : M)+f+f] = F ones ![k+1,f] := by
    have h : (1 : M)+f+f = f+f+1 := by simp only [add_assoc,add_comm,add_left_comm]
    rw [h,modelOnesCommute]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],f]
    rw [modelAddOne,modelOnesSucc]
  have hs := PA194TwoScanInvariant.modelFullScan (k+1) L f
  rw [←hcomm] at hs
  have hl : F ones ![k+1,L] = left+left+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],L] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hl] at hs
  have hi := modelIncrementAnywhere 7 1 ep e (left+left+1) hp he
  dsimp only at hi
  rw [(modelOdd left).1,(modelOdd left).2] at hi
  change _ = F pairCode ![modelNumeral M 7,F pairCode ![left,(1 : M)+(out+out)]] at hi
  have ho : (1 : M)+(out+out) = out+out+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [ho] at hi
  have hret := modelReturnCell k (a+a) out
  dsimp only at hret
  rw [(modelDouble a).1,(modelDouble a).2,zero_add] at hret
  have ht : (1 : M)+out+out = out+out+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [ht,modelReturnBlock] at hret
  change F PA194Stepper.stepper ![F addCode ![(k+1)+clock,(k+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![(k+1)+1,F PA194Stepper.stepper ![F addCode ![k+1,clock],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hs,hi,hret]
#print axioms incrementAfterHead
end models
end PA194MarkedIncrementHead
