import PA194DiagonalLink
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194DecoderRoundCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubtraction
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PackedClock PackedRootModel PackedDecoderModel
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive PA194SourceFetchLoop PA194SchedulerCode PA194UnpairRound PA194UnpairDrainComplete PA194IteratedSimulation

def unitCode : Code 1 := unary Code.succ (.zero 1)
def threeCode : Code 1 := unary Code.succ (unary Code.succ unitCode)
def fiveCode : Code 1 := unary Code.succ (unary Code.succ threeCode)
def ySucc : Code 1 := unary Code.succ (getRegister 7)
def threeY : Code 1 := bin addCode (bin addCode ySucc ySucc) ySucc
def zeroClock : Code 1 := bin addCode threeCode (bin addCode (bin addCode threeY unitCode) unitCode)
noncomputable def roundClock : Code 1 := choose0 (getRegister 6) zeroClock fiveCode
noncomputable def advance : Code 1 := bin PA194SourceControllerCode.run roundClock (.proj 0)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem registerModel (q : Nat) (args : Fin 11 → M) (tail : M) (r : Fin 9) :
    F (getRegister r.val) ![sourceState q args tail] = args ⟨r.val,by have h:=r.isLt; omega⟩ := by
  have hv : (![sourceState q args tail] : Fin 1 → M) = (fun _ => sourceState q args tail) := by
    funext i; fin_cases i; rfl
  rw [getRegister,getAuxModel,hv,file,modelDecodeRight]
  exact stateReg q args tail r

theorem clockModel (args : Fin 11 → M) (tail : M) :
    F roundClock ![sourceState 34 args tail] =
      if args 6 = (0 : M) then (((0 : M)+1)+1)+1 +
        ((PA194UnpairDrainInvariant.three (args 7+1)+1)+1)
      else (((((0 : M)+1)+1)+1)+1)+1 := by
  have h6 : F (getRegister 6) ![sourceState 34 args tail] = args 6 := registerModel 34 args tail (6 : Fin 9)
  have h7 : F (getRegister 7) ![sourceState 34 args tail] = args 7 := registerModel 34 args tail (7 : Fin 9)
  simp only [roundClock,choose0_model,zeroClock,threeY,ySucc,threeCode,fiveCode,unitCode,
    modelBin,modelUnary,PRAMultiplication.modelZero,←modelAddOne,h6,h7]
  by_cases h : args 6 = (0 : M) <;> simp only [h,if_true,if_false,PA194UnpairDrainInvariant.three]
  · change (((0 : M)+1)+1)+1 + (((((args 7+1)+(args 7+1))+(args 7+1))+((0 : M)+1))+((0 : M)+1)) =
      (((0 : M)+1)+1)+1 + (((((args 7+1)+(args 7+1))+(args 7+1))+1)+1)
    simp only [zero_add]
  · rfl
theorem advanceModel (s : M) : F advance ![s] = F PA194SourceControllerCode.run ![F roundClock ![s],s] := by
  rw [advance,modelBin,modelProjection]
  rfl

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem runFive (s : M) :
    F PA194SourceControllerCode.run ![(((((0 : M)+1)+1)+1)+1)+1,s] =
    F step ![F step ![F step ![F step ![F step ![s]]]]] := by
  change F (iterate step) ![(((((0 : M)+1)+1)+1)+1)+1,s] = _
  rw [iterateSucc,iterateSucc,iterateSucc,iterateSucc,iterateSucc,iterateZero]

theorem advancePositive (args : Fin 11 → M) (tail w a : M)
    (hw : args 8 = w+1) (ha : args 6 = a+1) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := Function.update a2 6 a
    F advance ![sourceState 34 args tail] = sourceState 34 out tail := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := Function.update a2 6 a
  have hn : a+1 ≠ (0 : M) := ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ a) (lt_add_one a))
  have h := positiveRound args tail w a hw ha
  change F step ![F step ![F step ![F step ![F step ![sourceState 34 args tail]]]]] = sourceState 34 out tail ∧ _ at h
  rw [advanceModel,clockModel,ha,if_neg hn,runFive]
  exact h.1

theorem advanceZero (args : Fin 11 → M) (tail w : M)
    (hw : args 8 = w+1) (hx : args 6 = (0 : M)) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := PA194UnpairDrainInvariant.argsAt a2 (a2 7)
    F advance ![sourceState 34 args tail] = sourceState 34 out tail := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := PA194UnpairDrainInvariant.argsAt a2 (a2 7)
  have hy : a2 7 = args 7+1 := by simp [a2,a1]
  have h := zeroXRound args tail w hw hx
  change F PA194SourceControllerCode.run ![(((0 : M)+1)+1)+1 + ((PA194UnpairDrainInvariant.three (a2 7)+1)+1),sourceState 34 args tail] = sourceState 34 out tail ∧ _ at h
  change F advance ![sourceState 34 args tail] = sourceState 34 out tail
  rw [advanceModel,clockModel,hx,if_pos rfl,←hy]
  exact h.1
#print axioms advanceModel
#print axioms runFive
#print axioms advancePositive
#print axioms advanceZero
#print axioms registerModel
#print axioms clockModel
end models
end PA194DecoderRoundCode
