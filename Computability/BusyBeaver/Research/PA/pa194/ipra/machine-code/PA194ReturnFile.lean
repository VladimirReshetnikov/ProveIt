import PA194ReturnCell
import PA194CarryFile
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PA194ReturnFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PRAModelIOpenPairing PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194CarryFile PA194ReturnCell

def returnOne {n : Nat} (v t : Code n) : Code n :=
  let a := bin ones v (unary .succ (bin addCode t t))
  bin addCode a a

def returnCode : (n : Nat) → Code (n+2)
  | 0 => .proj 0
  | n+1 => returnOne (.proj 1)
      (.comp (returnCode n) (pack (n+2) (Fin.cases (.proj 0) (fun i => .proj i.succ.succ))))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelReturnOne {n : Nat} (v t : Code n) (e : Fin n → M) :
    F (returnOne v t) e = F ones ![F v e,F t e+F t e+1]+F ones ![F v e,F t e+F t e+1] := by
  simp only [returnOne,modelBin,modelUnary,←modelAddOne]
  rfl

theorem modelReturnCodeZero (e : Fin 2 → M) : F (returnCode 0) e = e 0 := modelProjection 0 e

theorem modelReturnCodeSucc (n : Nat) (e : Fin (n+3) → M) :
    let t := F (returnCode n) (Fin.cases (e 0) (fun i => e i.succ.succ))
    F (returnCode (n+1)) e = F ones ![e 1,t+t+1]+F ones ![e 1,t+t+1] := by
  rw [returnCode,modelReturnOne,modelProjection,modelComposition,getCode_pack]
  have he : (fun i : Fin (n+2) => F (Fin.cases (.proj 0) (fun i => .proj i.succ.succ) i) e) =
      Fin.cases (e 0) (fun i => e i.succ.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection 0 e
    · exact modelProjection j.succ.succ e
  have hv := congrArg (F (returnCode n)) he
  dsimp only
  simp only [hv]

theorem modelReturnCarriedCell (v l t : M) :
    let a := F ones ![v,t+t+1]
    F PA194Stepper.stepper ![((1 : M)+1)+v,F pairCode ![TableDispatch.modelNumeral M 7,
      F pairCode ![F ones ![v,(l+l+1)+(l+l+1)],t+t+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,(a+a)+(a+a)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelReturnCell v (l+l+1) t
  dsimp only at h
  rw [(modelOdd l).1,(modelOdd l).2] at h
  have ht : ((1 : M)+1)+v = (v+1)+1 := by simp only [add_comm,add_left_comm]
  rw [ht]
  convert h using 2; simp only [add_assoc,add_comm,add_left_comm]
/-- Return through every block of a fixed finite physical file, with an
explicit PR clock and output-code and arbitrary candidate-model values. -/
theorem modelReturnFile (n : Nat) (e : Fin (n+1) → M) (l t : M) :
    F PA194Stepper.stepper ![F (costCode n) e,F pairCode ![TableDispatch.modelNumeral M 7,
      F pairCode ![F (leftCode n) (Fin.cases l e),t+t+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,
      F (returnCode n) (Fin.cases t e)+F (returnCode n) (Fin.cases t e)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n generalizing l t with
  | zero =>
    rw [modelCostZero]
    have hz := PA194Stepper.modelStepperZero (F pairCode ![TableDispatch.modelNumeral M 7,
      F pairCode ![F (leftCode 0) (Fin.cases l e),t+t+1]])
    change F PA194Stepper.stepper ![(0 : M),_] = _ at hz
    rw [hz,modelLeftZero,modelReturnCodeZero]
    rfl
  | succ n ih =>
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
    have hi := ih rest newLeft t
    rw [hi,modelReturnCarriedCell]
    rw [hr]
#print axioms modelReturnFile
#print axioms modelReturnCarriedCell
#print axioms modelReturnCodeSucc
end models
end PA194ReturnFile
