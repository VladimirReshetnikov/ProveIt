import PA194ActualLoopOrbit
import PA194ModelLoopCostInputs
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ActualLoopCostInputs
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelLoopCostInputs PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch
open PA194ActualLoopOrbit PA194ControllerLoopFrame PA194ModelSourceLoop
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem inputs (r : Fin 9 → M) (tail k n spare m : M) (hm : r 0 = m+1) :
    let x := packed (((k+1)+1)+1) n spare (PA194ModelSourceLoop.source r tail)
    let a := frameArgs r n spare
    let a28 := Function.update a 0 m
    let a29 := Function.update (Function.update a28 8 (a28 8+1)) 10 (F repeatOutput ![n+1,(0 : M)])
    (fun i => F (inputs27 PA194ControllerLoopFrame.readers i) (fun _ => x)) =
      Fin.cases (k+1) (Fin.cases m (fun i : Fin 10 => a i.succ)) ∧
    (fun i => F (inputs28 PA194ControllerLoopFrame.readers i) (fun _ => x)) =
      Fin.cases (k+1) (Fin.cases n a28) ∧
    (fun i => F (inputs29 PA194ControllerLoopFrame.readers i) (fun _ => x)) =
      Fin.cases k (Fin.cases (n+1) a29) := by
  dsimp only
  let a := frameArgs r n spare
  let x := packed (((k+1)+1)+1) n spare (PA194ModelSourceLoop.source r tail)
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
  have hg : F gap (fun _ => x) = ((k+1)+1)+1 := by
    simp [gap,x,packed,modelDecodeLeft,modelPairCode,pi₁_pair]
  have hn : F count (fun _ => x) = n := by
    simp [count,rest,x,packed,modelUnary,modelProjection,modelDecodeLeft,modelDecodeRight,modelPairCode,pi₁_pair,pi₂_pair]
  have hp27 : F k27 (fun _ => x) = k+1 := by
    simp only [k27,prev,modelUnary,hg]
    rw [show ((k+1)+1)+1 = F Code.succ (fun _ => (k+1)+1) from modelAddOne _,modelPredSucc,
      show (k+1)+1 = F Code.succ (fun _ => k+1) from modelAddOne _,modelPredSucc]
  have hp29 : F k29 (fun _ => x) = k := by
    simp only [k29,prev,modelUnary,hp27]
    rw [show k+1 = F Code.succ (fun _ => k) from modelAddOne _,modelPredSucc]
  have hp0 : F predCode (fun _ => evalArgs PA194ControllerLoopFrame.readers x 0) = m := by
    rw [ha]
    have ha0 : a 0 = r 0 := by simp [a,frameArgs,PA194ActualSourceLoop.args]
    rw [ha0,hm,show m+1 = F Code.succ (fun _ => m) from modelAddOne _,modelPredSucc]
  have hpA : F predCode (fun _ => a 0) = m := by simpa only [ha] using hp0
  rw [modelInputs27,modelInputs28,modelInputs29]
  dsimp only [x,a] at ha hp27 hp29 hp0 hpA hn
  simp only [evalArgs29,evalArgs28,ha,hpA,hp27,hp29,hn]
  tauto
#print axioms inputs
end models
end PA194ActualLoopCostInputs
