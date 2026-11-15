import PA194Site28CarryCodes
import PA194ReturnFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28ReturnCarry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28CarryFile PA194Site28CarryCodes PA194CarryFile PA194ReturnFile PA194ReturnCell PA194UnaryRuns PA194BinaryDouble PA194StateOne PRAModelIOpenPairing BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem returnCarry (n : Nat) (e : Fin (n+2) → M) (l t : M)
    (hl : F parityCode (fun _ => l) = (1 : M)) :
    let vals : Fin (n+1) → M := fun i => e i.castSucc
    let out := F (PA194ReturnFile.returnCode n) (Fin.cases t vals)
    F PA194Stepper.stepper ![F (PA194CarryFile.costCode n) vals,
      F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => carryLeft n l e),t+t+1]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),out+out+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n generalizing l t with
  | zero =>
    dsimp only [carryLeft]
    rw [PA194CarryFile.modelCostZero,PA194ReturnFile.modelReturnCodeZero]
    change F PA194Stepper.stepper ![F (Code.zero 0) Fin.elim0,_] = _
    rw [PA194Stepper.modelStepperZero]
    rfl
  | succ n ih =>
    let e1 : Fin (n+2) → M := fun i => e i.succ
    let vals : Fin (n+2) → M := fun i => e i.castSucc
    let vals1 : Fin (n+1) → M := fun i => e1 i.castSucc
    let next := F ones ![e 0+1,l+l]
    let out := F (PA194ReturnFile.returnCode n) (Fin.cases t vals1)
    have hnext : F parityCode (fun _ => next) = (1 : M) := by
      have hs : next = F ones ![e 0,l+l]+F ones ![e 0,l+l]+1 := by
        dsimp only [next]
        change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
        rw [modelAddOne,modelOnesSucc]
      rw [hs,(modelOdd _).1]
    have hv : (fun i : Fin (n+1) => vals i.succ) = vals1 := by
      funext i
      apply congrArg e
      apply Fin.ext
      rfl
    have hcost : F (PA194CarryFile.costCode (n+1)) vals =
        F (PA194CarryFile.costCode n) vals1 + ((e 0+1)+1) := by
      rw [PA194CarryFile.modelCostSucc,hv]
      change ((1 : M)+1)+e 0+F (PA194CarryFile.costCode n) vals1 = _
      simp only [add_assoc,add_comm,add_left_comm]
    have ih' := ih e1 next t hnext
    dsimp only at ih'
    have hhalf : F halfCode (fun _ => next) = F ones ![e 0,l+l] := by
      have hs : next = F ones ![e 0,l+l]+F ones ![e 0,l+l]+1 := by
        dsimp only [next]
        change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
        rw [modelAddOne,modelOnesSucc]
      rw [hs,(modelOdd _).2]
    rw [hhalf] at ih'
    have hc := modelReturnCell (e 0) l out
    dsimp only at hc
    rw [hl] at hc
    have hout : F (PA194ReturnFile.returnCode (n+1)) (Fin.cases t vals) =
        F ones ![e 0,out+out+1]+F ones ![e 0,out+out+1] := by
      rw [PA194ReturnFile.modelReturnCodeSucc]
      congr 2
    dsimp only [carryLeft]
    change F PA194Stepper.stepper ![F (PA194CarryFile.costCode (n+1)) vals,_] = _
    rw [hcost]
    change F PA194Stepper.stepper ![F addCode ![F (PA194CarryFile.costCode n) vals1,(e 0+1)+1],_] = _
    rw [PA194StepperCompose.modelStepperCompose,ih',hc,hout]
    simp only [add_assoc,add_comm,add_left_comm]
#print axioms returnCarry
end models
end PA194Site28ReturnCarry
