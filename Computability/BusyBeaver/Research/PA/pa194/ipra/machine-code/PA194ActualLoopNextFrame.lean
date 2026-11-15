import PA194ActualLoopCostInputs
import PA194Site28DynamicOutput
import PA194Site29DynamicOutput
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ActualLoopNextFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ActualLoopOrbit PA194ControllerLoopFrame PA194ModelSourceLoop PA194ActualSourceLoop PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem nextFrame (r : Fin 9 → M) (tail k n spare m : M) (hm : r 0 = m+1) :
    let x := packed (((k+1)+1)+1) n spare (PA194ModelSourceLoop.source r tail)
    let a := frameArgs r n spare
    let a28 := Function.update a 0 m
    let a29 := PA194Site28DynamicOutput.updated a28 n
    let out := PA194Site29DynamicOutput.updated a29 (n+1)
    F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => F (PA194ModelLoopState.next quad) (fun _ => x)) =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 27)
        (F zeros ![(((k+1)+1)+1)+1,(1 : M)+(F sourceFileCode out+F sourceFileCode out)])]] := by
  dsimp only
  let rr := Function.update (Function.update (Function.update r 0 m) 6 (r 6+1)) 8 (r 8+1)
  let n' := (n+1)+1
  let a := frameArgs r n spare
  let a28 := Function.update a 0 m
  let a29 := PA194Site28DynamicOutput.updated a28 n
  let out := PA194Site29DynamicOutput.updated a29 (n+1)
  have hargs : frameArgs rr n' spare = out := by
    funext i
    fin_cases i <;> simp [rr,n',a,a28,a29,out,frameArgs,PA194ActualSourceLoop.args,
      PA194Site28DynamicOutput.updated,PA194Site29DynamicOutput.updated,←modelAddOne] <;> rfl
  have hstep := PA194ActualSourceLoop.oneLoop r tail m hm
  rw [modelNext,hstep]
  let av := frameArgs rr n' spare
  have htail : av 10 = F repeatOutput ![n',(0 : M)] := by simp [av,frameArgs]
  have hspare : av 9 = spare := by simp [av,frameArgs]
  have hs := PA194ActualLoopOrbit.controllerSource rr n' spare tail
  have hf := PA194ControllerLoopFrame.frameSource av ((((k+1)+1)+1)+1) n' tail htail
  rw [hspare,hs] at hf
  have hav : av = out := hargs
  rw [hav] at hf
  exact hf
#print axioms nextFrame
end models
end PA194ActualLoopNextFrame
