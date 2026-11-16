import PA194ActualLoopOrbit
import PA194ModelLoopCostInputs
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194Site27ZeroCostInput
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelLoopCostInputs PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch
open PA194ActualLoopOrbit PA194ControllerLoopFrame PA194ModelSourceLoop
def inputsZero (rs : Fin 9 → Code 1) : Fin 12 → Code 1 := Fin.cases k27 (PA194ModelLoopFrame.args rs)
def zeroCost (c : Code 12) : Code 1 := applyCodes c (inputsZero PA194ControllerLoopFrame.readers)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem inputs (r : Fin 9 → M) (tail k n spare : M) :
    let x := packed ((k+1)+1) n spare (PA194ModelSourceLoop.source r tail)
    let a := frameArgs r n spare
    (fun i => F (inputsZero PA194ControllerLoopFrame.readers i) (fun _ => x)) = Fin.cases k a := by
  dsimp only
  let a := frameArgs r n spare
  let x := packed ((k+1)+1) n spare (PA194ModelSourceLoop.source r tail)
  have hs := PA194ActualLoopOrbit.controllerSource r n spare tail
  have hregs : PA194ControllerLoopFrame.regsOfArgs a = r := by
    funext i
    fin_cases i <;> simp [a,frameArgs,PA194ControllerLoopFrame.regsOfArgs,PA194ActualSourceLoop.args]
  have hread (i : Fin 9) : F (PA194ControllerLoopFrame.readers i) (fun _ => PA194ModelSourceLoop.source r tail) = r i := by
    have h := PA194ControllerLoopFrame.readSource a tail i
    change F (PA194ControllerLoopFrame.readers i) (fun _ => PA194ControllerLoopFrame.source a tail) = PA194ControllerLoopFrame.regsOfArgs a i at h
    rw [hs,hregs] at h
    exact h
  have ha : evalArgs PA194ControllerLoopFrame.readers x = a := by
    funext i
    fin_cases i <;> simp [evalArgs,PA194ModelLoopFrame.args,PA194ModelLoopFrame.reg,PA194ModelLoopFrame.suffix,
      count,rest,rest2,PA194ModelLoopState.spare,PA194ModelLoopState.control,x,packed,modelBin,modelUnary,
      modelProjection,modelDecodeLeft,modelDecodeRight,modelPairCode,PRAMultiplication.modelZero,pi₁_pair,pi₂_pair,
      hread,a,frameArgs,PA194ActualSourceLoop.args] <;> rfl
  have hg : F gap (fun _ => x) = (k+1)+1 := by
    simp [gap,x,packed,modelDecodeLeft,modelPairCode,pi₁_pair]
  have hp : F k27 (fun _ => x) = k := by
    simp only [k27,prev,modelUnary,hg]
    rw [show (k+1)+1 = F Code.succ (fun _ => k+1) from modelAddOne _,modelPredSucc,
      show k+1 = F Code.succ (fun _ => k) from modelAddOne _,modelPredSucc]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hp
  · change F (PA194ModelLoopFrame.args PA194ControllerLoopFrame.readers j) (fun _ => x) = a j
    exact congrFun ha j

theorem cost (c : Code 12) (r : Fin 9 → M) (tail k n spare : M) :
    F (zeroCost c) (fun _ => packed ((k+1)+1) n spare (PA194ModelSourceLoop.source r tail)) =
      F c (Fin.cases k (frameArgs r n spare)) := by
  rw [zeroCost,modelApplyCodes,inputs]
#print axioms inputs
#print axioms cost
end models
end PA194Site27ZeroCostInput
