import PA194ActualPhysicalOrbit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194ActualPhysicalOrbitCode
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
open PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem completeLoop (r : Fin 9 → M) (tail k n spare : M) :
    let g := (((k+1)+1)+1)
    let x := packed g n spare (PA194ModelSourceLoop.source r tail)
    let y := packed (g+r 0) ((n+r 0)+r 0) spare (PA194ModelSourceLoop.source (running r (r 0)) tail)
    F PA194Stepper.stepper ![F (timeCode (PA194ModelLoopState.next quad)
      (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers)) ![r 0,x],
      F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => x)] =
      F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => y) := by
  let g := (((k+1)+1)+1)
  let r' := running r (r 0)
  let n' := (n+r 0)+r 0
  let a := frameArgs r n spare
  let a' := frameArgs r' n' spare
  have ht : a 10 = F repeatOutput ![n,(0 : M)] := by simp [a,frameArgs]
  have ht' : a' 10 = F repeatOutput ![n',(0 : M)] := by simp [a',frameArgs]
  have hs : a 9 = spare := by simp [a,frameArgs]
  have hs' : a' 9 = spare := by simp [a',frameArgs]
  have hf := PA194ControllerLoopFrame.frameSource a g n tail ht
  rw [hs,PA194ActualLoopOrbit.controllerSource r n spare tail] at hf
  have hf' := PA194ControllerLoopFrame.frameSource a' (g+r 0) n' tail ht'
  rw [hs',PA194ActualLoopOrbit.controllerSource r' n' spare tail] at hf'
  change F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => packed g n spare (PA194ModelSourceLoop.source r tail)) = physicalFrame 27 g a at hf
  change F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => packed (g+r 0) n' spare (PA194ModelSourceLoop.source r' tail)) = physicalFrame 27 (g+r 0) a' at hf'
  have hp := PA194ActualPhysicalOrbit.physicalOrbit r tail k n spare (r 0) (le_refl _)
  dsimp only at hp ⊢
  rw [←hf,←hf'] at hp
  exact hp
#print axioms completeLoop
end models
end PA194ActualPhysicalOrbitCode
