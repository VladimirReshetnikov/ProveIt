import PA194IncrementThroughTail
import PA194ReturnFileMeaning
set_option autoImplicit false
namespace PA194IncrementReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns
open PA194IncrementThroughTail PA194ReturnFile PA194ReturnFileMeaning PA194ReturnCell PA194OnesCommute
open BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelReturnRemaining (n : Nat) (e : Fin (n+2) → M) (l : M)
    (he : e (Fin.last (n+1)) = (0 : M)) :
    let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let selected := F ones ![e 0,(l+l)+(l+l)+1]
    let out := F (returnCode n) (Fin.cases six (fun i => e i.succ))
    F PA194Stepper.stepper ![(front+TableDispatch.modelNumeral M 6)+F (costCode n) (fun i => e i.succ),
      F pairCode ![TableDispatch.modelNumeral M 2,F pairCode ![l,F (markedFile n) e]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![selected,out+out+1]] := by
  let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
  change F PA194Stepper.stepper ![F addCode ![front+TableDispatch.modelNumeral M 6,F (costCode n) (fun i => e i.succ)],_] = _
  rw [PA194StepperCompose.modelStepperCompose,modelThroughTail n e l he,modelReturnFile]

/-- A complete physical increment for a first marked register, with a
fixed-arity remaining file, encoded spare, and blank suffix. -/
theorem modelFirstMarkedIncrement (n : Nat) (e : Fin (n+2) → M) (l : M)
    (he : e (Fin.last (n+1)) = (0 : M)) :
    let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let out := F (returnCode n) (Fin.cases six (fun i => e i.succ))
    let result := F block ![e 0+1,out]
    F PA194Stepper.stepper ![((front+TableDispatch.modelNumeral M 6)+F (costCode n) (fun i => e i.succ))+((e 0+1)+1+1),
      F pairCode ![TableDispatch.modelNumeral M 2,F pairCode ![l,F (markedFile n) e]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(result+result)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
  let c3 := ((1 : M)+1)+1
  let six := c3+c3
  let out := F (returnCode n) (Fin.cases six (fun i => e i.succ))
  let selected := F ones ![e 0,(l+l)+(l+l)+1]
  have hselected : selected = F ones ![e 0+1,l+l] := by
    dsimp [selected]
    have hc := modelOnesCommute (e 0) (l+l)
    have hs : F ones ![e 0+1,l+l] = F ones ![e 0,l+l]+F ones ![e 0,l+l]+1 := by
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    rw [hc,hs]
  have hout : F block ![e 0+1,out] =
      F ones ![e 0+1,out+out+1]+F ones ![e 0+1,out+out+1] :=
    (modelReturnBlock (e 0+1) out).symm
  change F PA194Stepper.stepper ![F addCode ![(front+TableDispatch.modelNumeral M 6)+F (costCode n) (fun i => e i.succ),((e 0+1)+1+1)],_] = _
  rw [PA194StepperCompose.modelStepperCompose,modelReturnRemaining n e l he]
  change F PA194Stepper.stepper ![((e 0+1)+1+1),F pairCode ![TableDispatch.modelNumeral M 7,
    F pairCode ![selected,out+out+1]]] = F pairCode ![TableDispatch.modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(F block ![e 0+1,out]+F block ![e 0+1,out])]]
  rw [hselected,modelReturnCell]
  have heq : (1 : M)+out+out = out+out+1 := by simp only [add_comm,add_left_comm]
  rw [heq,hout]
  simp only [add_assoc]
/-- The output is the incremented first register followed by the unchanged
remaining file and an appended one-valued spare. -/
theorem modelFirstMarkedIncrementFile (n : Nat) (e : Fin (n+2) → M) (l : M)
    (he : e (Fin.last (n+1)) = (0 : M)) :
    let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (fileCode n) (replaceLast n (fun i => e i.succ) six)
    let result := F block ![e 0+1,rest]
    F PA194Stepper.stepper ![((front+TableDispatch.modelNumeral M 6)+F (costCode n) (fun i => e i.succ))+((e 0+1)+1+1),
      F pairCode ![TableDispatch.modelNumeral M 2,F pairCode ![l,F (markedFile n) e]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(result+result)]] := by
  have h := modelFirstMarkedIncrement n e l he
  dsimp only at h ⊢
  rw [modelReturnMeaning] at h
  exact h
#print axioms modelFirstMarkedIncrementFile
#print axioms modelReturnRemaining
#print axioms modelFirstMarkedIncrement
end models
end PA194IncrementReturn
