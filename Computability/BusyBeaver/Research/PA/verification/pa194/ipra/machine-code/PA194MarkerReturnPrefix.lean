import PA194MarkerReturnCell
import PA194PrefixFile
import PA194ReturnFile
import PA194OnesCommute
import PA194RegisterFile
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
namespace PA194MarkerReturnPrefix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PA194MarkerReturnCell BinaryTapeCodes PRAModelIOpenPairing PA194UnaryRuns PA194RegisterFile PA194PrefixCell PA194CarryFile PA194StateOne PA194PrefixFile PA194ReturnFile PA194ReturnCell PA194OnesCommute PA194BinaryDouble

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelMarkerReturnPrefixCell (i : Fin 2) (v l t : M) :
    let x := F ones ![v,(l+l)+(l+l)+1]
    let a := F ones ![v,t+t+1]
    F PA194Stepper.stepper ![((1 : M)+1)+v,F pairCode ![TableDispatch.modelNumeral M (returnControl i),
      F pairCode ![F halfCode (fun _ => x),F parityCode (fun _ => x)+t+t]]] =
    F pairCode ![TableDispatch.modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(a+a)+(a+a)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelOnesCommute,(modelOdd (F ones ![v,l+l])).1,(modelOdd (F ones ![v,l+l])).2]
  have h := modelMarkerReturnCell i v l t
  dsimp only at h
  have ht : ((1 : M)+1)+v = (v+1)+1 := by simp only [add_comm,add_left_comm]
  rw [ht]
  convert h using 2 <;> simp only [add_assoc,add_comm,add_left_comm]

theorem modelMarkerReturnPrefix (n : Nat) (i : Fin 2) (e : Fin (n+2) → M) (l t : M) :
    let x := F (PA194PrefixFile.leftCode (n+1)) (Fin.cases l e)
    let a := F (returnCode (n+1)) (Fin.cases t e)
    F PA194Stepper.stepper ![F (costCode (n+1)) e,F pairCode ![TableDispatch.modelNumeral M (returnControl i),
      F pairCode ![F halfCode (fun _ => x),F parityCode (fun _ => x)+t+t]]] =
    F pairCode ![TableDispatch.modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+a+a]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n generalizing l t i with
  | zero =>
    dsimp only
    rw [modelCostSucc,modelCostZero,add_zero,PA194PrefixFile.modelLeftSucc,
      PA194PrefixFile.modelLeftZero,modelReturnCodeSucc,modelReturnCodeZero]
    simp only [Fin.cases_zero,Fin.cases_succ]
    have hl1 : Fin.cases l e (1 : Fin 3) = e 0 := rfl
    have ht1 : Fin.cases t e (1 : Fin 3) = e 0 := rfl
    rw [hl1,ht1]
    have h := modelMarkerReturnPrefixCell i (e 0) l t
    dsimp only at h
    convert h using 2 <;> simp only [add_assoc,add_comm,add_left_comm]
  | succ n ih =>
    dsimp only
    let rest : Fin (n+2) → M := fun j => e j.succ
    let newLeft := F ones ![e 0,(l+l)+(l+l)+1]
    let newTail := F (returnCode (n+1)) (Fin.cases t rest)
    have hc : F (costCode ((n+1)+1)) e = F (costCode (n+1)) rest + (((1 : M)+1)+e 0) := by
      rw [modelCostSucc]
      exact add_comm _ _
    have hl := PA194PrefixFile.modelLeftSucc (n+1) (Fin.cases l e)
    simp only [Fin.cases_zero,Fin.cases_succ] at hl
    have hr := modelReturnCodeSucc (n+1) (Fin.cases t e)
    simp only [Fin.cases_zero,Fin.cases_succ] at hr
    have hl1 : Fin.cases l e (1 : Fin (n+4)) = e 0 := rfl
    have ht1 : Fin.cases t e (1 : Fin (n+4)) = e 0 := rfl
    rw [hl1] at hl
    rw [ht1] at hr
    rw [hc,hl]
    change F PA194Stepper.stepper ![F addCode ![F (costCode (n+1)) rest,((1 : M)+1)+e 0],_] = _
    rw [PA194StepperCompose.modelStepperCompose]
    have hprev := ih i rest newLeft t
    dsimp only at hprev
    rw [hprev]
    have hf := modelMarkerReturnPrefixCell ⟨1,by decide⟩ (e 0) l newTail
    dsimp only at hf
    change F PA194Stepper.stepper ![((1 : M)+1)+e 0,F pairCode ![TableDispatch.modelNumeral M 17,
      F pairCode ![F halfCode (fun _ => newLeft),F parityCode (fun _ => newLeft)+newTail+newTail]]] = _
    have hcontrol : returnControl (⟨1,by decide⟩ : Fin 2) = 17 := rfl
    rw [hcontrol] at hf
    dsimp only [newLeft] at *
    rw [hf,hr]
#print axioms modelMarkerReturnPrefix
#print axioms modelMarkerReturnPrefixCell
end models
end PA194MarkerReturnPrefix
