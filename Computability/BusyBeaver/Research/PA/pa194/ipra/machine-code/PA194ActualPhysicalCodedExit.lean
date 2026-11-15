import PA194ActualPhysicalOrbitCode
import PA194Site27ZeroCodedStep
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194ActualPhysicalCodedExit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopFrameAt PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194Site27ZeroCostInput PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem exitsAt31 (c : Code 12) (r : Fin 9 → M) (tail k n spare : M)
    (hc : F c (Fin.cases ((k+1)+r 0) (frameArgs (running r (r 0)) ((n+r 0)+r 0) spare)) =
      PA194Site27ZeroClockPhysical.clock24 ((k+1)+r 0) (frameArgs (running r (r 0)) ((n+r 0)+r 0) spare)) :
    let g := (((k+1)+1)+1)
    let x := packed g n spare (PA194ModelSourceLoop.source r tail)
    let y := packed (g+r 0) ((n+r 0)+r 0) spare (PA194ModelSourceLoop.source (running r (r 0)) tail)
    F PA194Stepper.stepper ![F addCode ![F (timeCode (PA194ModelLoopState.next quad)
      (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode readers)) ![r 0,x],
      F (zeroCost c) (fun _ => y)],F (PA194ModelLoopFrame.frame readers) (fun _ => x)] =
      F (frameAt 31 readers) (fun _ => y) := by
  dsimp only
  let g := (((k+1)+1)+1)
  let r' := running r (r 0)
  let n' := (n+r 0)+r 0
  let x := packed g n spare (PA194ModelSourceLoop.source r tail)
  let y := packed (g+r 0) n' spare (PA194ModelSourceLoop.source r' tail)
  have hz : r' 0 = (0 : M) := by
    have h : F subCode ![r 0,r 0] = (0 : M) := by rw [modelSubAsTsub]; simp
    simpa [r',running] using h
  have hg : g+r 0 = (((k+1)+r 0)+1)+1 := by dsimp [g]; simp [add_assoc,add_comm,add_left_comm]
  have loop := PA194ActualPhysicalOrbitCode.completeLoop r tail k n spare
  dsimp only at loop
  have hzero := PA194Site27ZeroCodedStep.zeroStep c r' tail ((k+1)+r 0) n' spare hz hc
  dsimp only at hzero
  rw [←hg] at hzero
  change F PA194Stepper.stepper ![F (zeroCost c) (fun _ => y),F (PA194ModelLoopFrame.frame readers) (fun _ => y)] = F (frameAt 31 readers) (fun _ => y) at hzero
  rw [PA194StepperCompose.modelStepperCompose,loop]
  exact hzero
#print axioms exitsAt31
end models
end PA194ActualPhysicalCodedExit
