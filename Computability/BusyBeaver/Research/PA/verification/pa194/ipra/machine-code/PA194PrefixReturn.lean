import PA194PrefixFile
import PA194ReturnFile
import PA194OnesCommute
import PA194RegisterFile
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
namespace PA194PrefixReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open BinaryTapeCodes PRAModelIOpenPairing PA194UnaryRuns PA194RegisterFile PA194PrefixCell PA194CarryFile PA194StateOne PA194PrefixFile PA194ReturnFile PA194ReturnCell PA194OnesCommute PA194BinaryDouble

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelReturnPrefixCell (v l t : M) :
    let x := F ones ![v,(l+l)+(l+l)+1]
    let a := F ones ![v,t+t+1]
    F PA194Stepper.stepper ![((1 : M)+1)+v,F pairCode ![TableDispatch.modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => x),F parityCode (fun _ => x)+t+t]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(a+a)+(a+a)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelOnesCommute,(modelOdd (F ones ![v,l+l])).1,(modelOdd (F ones ![v,l+l])).2]
  have h := modelReturnCell v l t
  dsimp only at h
  have ht : ((1 : M)+1)+v = (v+1)+1 := by simp only [add_comm,add_left_comm]
  rw [ht]
  convert h using 2 <;> simp only [add_assoc,add_comm,add_left_comm]
theorem modelReturnPrefixFile (n : Nat) (e : Fin (n+1) → M) (l t : M) :
    let x := F (PA194PrefixFile.leftCode n) (Fin.cases l e)
    let a := F (returnCode n) (Fin.cases t e)
    F PA194Stepper.stepper ![F (costCode n) e,F pairCode ![TableDispatch.modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => x),F parityCode (fun _ => x)+t+t]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+a+a]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n generalizing l t with
  | zero =>
    dsimp only
    rw [modelCostZero,PA194PrefixFile.modelLeftZero,modelReturnCodeZero]
    exact PA194Stepper.modelStepperZero _
  | succ n ih =>
    dsimp only
    let rest : Fin (n+1) → M := fun i => e i.succ
    let newLeft := F ones ![e 0,(l+l)+(l+l)+1]
    let newTail := F (returnCode n) (Fin.cases t rest)
    have hc : F (costCode (n+1)) e = F (costCode n) rest + (((1 : M)+1)+e 0) := by
      rw [modelCostSucc]
      exact add_comm _ _
    have hl := PA194PrefixFile.modelLeftSucc n (Fin.cases l e)
    simp only [Fin.cases_zero,Fin.cases_succ] at hl
    have hr := modelReturnCodeSucc n (Fin.cases t e)
    simp only [Fin.cases_zero,Fin.cases_succ] at hr
    have hl1 : Fin.cases l e (1 : Fin (n+3)) = e 0 := rfl
    have ht1 : Fin.cases t e (1 : Fin (n+3)) = e 0 := rfl
    rw [hl1] at hl
    rw [ht1] at hr
    rw [hc,hl]
    change F PA194Stepper.stepper ![F addCode ![F (costCode n) rest,((1 : M)+1)+e 0],_] = _
    rw [PA194StepperCompose.modelStepperCompose]
    have hi := ih rest newLeft t
    dsimp only at hi
    rw [hi,modelReturnPrefixCell]
    rw [hr]
#print axioms modelReturnPrefixFile
#print axioms modelReturnPrefixCell
end models
end PA194PrefixReturn
