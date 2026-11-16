import PA194RollbackCell
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PA194RollbackFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194CarryFile PA194ReturnFile PA194ReturnFileMeaning PA194RegisterFile PA194RollbackCell
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelRollbackPrefix (n : Nat) (e : Fin (n+1) → M) (l t : M) :
    let x := F (leftCode n) (Fin.cases l e)
    let a := F (returnCode n) (Fin.cases t e)
    F PA194Stepper.stepper ![F (costCode n) e,F pairCode ![TableDispatch.modelNumeral M 11,
      F pairCode ![F halfCode (fun _ => x),F parityCode (fun _ => x)+t+t]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+a+a]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n generalizing l t with
  | zero =>
    dsimp only
    rw [modelCostZero,modelLeftZero,modelReturnCodeZero]
    exact PA194Stepper.modelStepperZero _
  | succ n ih =>
    dsimp only
    let rest : Fin (n+1) → M := fun i => e i.succ
    let newLeft := F ones ![e 0,(l+l+1)+(l+l+1)]
    let newTail := F (returnCode n) (Fin.cases t rest)
    have hc : F (costCode (n+1)) e = F (costCode n) rest + (((1 : M)+1)+e 0) := by
      rw [modelCostSucc]
      exact add_comm _ _
    have hl := modelLeftSucc n (Fin.cases l e)
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
    have hprev := ih rest newLeft t
    dsimp only at hprev
    rw [hprev]
    have ht : ((1 : M)+1)+e 0 = (e 0+1)+1 := by simp only [add_assoc,add_comm,add_left_comm]
    rw [ht,modelRollbackCell]
    have hb := modelReturnBlock (e 0) newTail
    have ha : F ones ![e 0+1,newTail] = F ones ![e 0,newTail+newTail+1] := by
      have hcomm := PA194OnesCommute.modelOnesCommute (e 0) newTail
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],newTail] = _
      rw [modelAddOne,modelOnesSucc,hcomm]
    rw [ha,hr]
#print axioms modelRollbackPrefix
end models
end PA194RollbackFile
