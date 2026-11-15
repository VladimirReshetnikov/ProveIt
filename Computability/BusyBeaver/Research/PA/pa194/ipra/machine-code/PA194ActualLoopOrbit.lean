import PA194ControllerLoopFrame
import PA194ActualSourceLoop
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ActualLoopOrbit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelSourceLoop PA194ActualSourceLoop PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
def frameArgs (r : Fin 9 → M) (n spare : M) : Fin 11 → M :=
  Function.update (Function.update (PA194ActualSourceLoop.args r) 9 spare) 10 (F repeatOutput ![n,(0 : M)])
theorem controllerSource (r : Fin 9 → M) (n spare tail : M) :
    PA194ControllerLoopFrame.source (frameArgs r n spare) tail = PA194ModelSourceLoop.source r tail := by
  simp [PA194ControllerLoopFrame.source,PA194ControllerLoopFrame.regsOfArgs,PA194ModelSourceLoop.source,
    PA194SourceRegisterRelation.pack,frameArgs,PA194ActualSourceLoop.args,Function.update]
theorem frameOrbit (r : Fin 9 → M) (tail g n spare steps : M) (h : steps ≤ r 0) :
    let state := packed g n spare (PA194ModelSourceLoop.source r tail)
    let r' := PA194ModelSourceLoop.running r steps
    let n' := (n+steps)+steps
    let args := frameArgs r' n' spare
    F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers)
      (fun _ => F (iterCode (PA194ModelLoopState.next quad)) ![steps,state]) =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 27)
        (F zeros ![g+steps,(1 : M)+(F sourceFileCode args+F sourceFileCode args)])]] := by
  dsimp only
  have hiter := PA194ModelLoopState.iterPacked (M := M) quad steps g n spare (PA194ModelSourceLoop.source r tail)
  have hsource := PA194ActualSourceLoop.sourceIteration r tail steps h
  rw [hsource] at hiter
  rw [hiter]
  let r' := PA194ModelSourceLoop.running r steps
  let n' := (n+steps)+steps
  let args := frameArgs r' n' spare
  have htail : args 10 = F repeatOutput ![n',(0 : M)] := by simp [args,frameArgs]
  have hspare : args 9 = spare := by simp [args,frameArgs]
  have hs := controllerSource r' n' spare tail
  have hf := PA194ControllerLoopFrame.frameSource args (g+steps) n' tail htail
  rw [hspare,hs] at hf
  exact hf
#print axioms controllerSource
#print axioms frameOrbit
end models
end PA194ActualLoopOrbit
