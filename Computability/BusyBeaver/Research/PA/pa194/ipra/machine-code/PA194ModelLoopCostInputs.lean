import PA194ModelLoopCost
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ModelLoopCostInputs
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def evalArgs (rs : Fin 9 → Code 1) (x : M) : Fin 11 → M := fun i => F (PA194ModelLoopFrame.args rs i) (fun _ => x)
def evalArgs28 (rs : Fin 9 → Code 1) (x : M) : Fin 11 → M := Function.update (evalArgs rs x) 0 (F predCode (fun _ => evalArgs rs x 0))
def evalArgs29 (rs : Fin 9 → Code 1) (x : M) : Fin 11 → M :=
  Function.update (Function.update (evalArgs28 rs x) 8 (evalArgs28 rs x 8+1)) 10
    (F repeatOutput ![F count (fun _ => x)+1,(0 : M)])
theorem modelInputs27 (rs : Fin 9 → Code 1) (x : M) :
    (fun i => F (inputs27 rs i) (fun _ => x)) = Fin.cases (F k27 (fun _ => x))
      (Fin.cases (F predCode (fun _ => evalArgs rs x 0)) (fun i : Fin 10 => evalArgs rs x i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · change F (prev (PA194ModelLoopFrame.args rs 0)) (fun _ => x) = F predCode (fun _ => evalArgs rs x 0)
      rw [prev,modelUnary]
      rfl
    · rfl
theorem modelInputs28 (rs : Fin 9 → Code 1) (x : M) :
    (fun i => F (inputs28 rs i) (fun _ => x)) = Fin.cases (F k27 (fun _ => x)) (Fin.cases (F count (fun _ => x)) (evalArgs28 rs x)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change F (args28 rs j) (fun _ => x) = evalArgs28 rs x j
      by_cases h : j = 0 <;> simp [args28,prev,evalArgs28,evalArgs,modelUnary,h]
theorem modelInputs29 (rs : Fin 9 → Code 1) (x : M) :
    (fun i => F (inputs29 rs i) (fun _ => x)) = Fin.cases (F k29 (fun _ => x)) (Fin.cases (F count (fun _ => x)+1) (evalArgs29 rs x)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · change F (PA194ModelLoopState.plus1 count) (fun _ => x) = F count (fun _ => x)+1
      simp only [PA194ModelLoopState.plus1,PA194ModelLoopState.one,modelBin,modelConstant,modelNumeralOne]
      rfl
    · change F (args29 rs j) (fun _ => x) = evalArgs29 rs x j
      by_cases h8 : j = 8 <;> by_cases h10 : j = 10 <;> by_cases h0 : j = 0 <;>
        simp_all [args29,args28,prev,nextSuffix,evalArgs29,evalArgs28,evalArgs,
          PA194ModelLoopState.plus1,PA194ModelLoopState.one,modelUnary,modelBin,modelConstant,modelNumeralOne,PRAMultiplication.modelZero] <;> rfl
#print axioms modelInputs27
#print axioms modelInputs28
#print axioms modelInputs29
end models
end PA194ModelLoopCostInputs
