import PA194ActualPhysicalOrbit
import PA194SourceSite27Zero
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194ActualPhysicalExit
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

theorem exitsAt31 (r : Fin 9 → M) (tail k n spare : M) :
    let g := (((k+1)+1)+1)
    let a := frameArgs r n spare
    let a' := frameArgs (running r (r 0)) ((n+r 0)+r 0) spare
    ∃ time : M, F PA194Stepper.stepper ![time,physicalFrame 27 g a] =
        physicalFrame 31 (g+r 0) a' := by
  let g := (((k+1)+1)+1)
  let a' := frameArgs (running r (r 0)) ((n+r 0)+r 0) spare
  have hz : a' 0 = (0 : M) := by
    have h : F subCode ![r 0,r 0] = (0 : M) := by rw [modelSubAsTsub]; simp
    simpa [a',frameArgs,PA194ActualSourceLoop.args,running] using h
  have hg : g+r 0 = (((k+1)+r 0)+1)+1 := by dsimp [g]; simp [add_assoc,add_comm,add_left_comm]
  obtain ⟨clock,hzrun⟩ := (PA194SourceSite27Zero.zeroBranch ((k+1)+r 0) tail a' hz).2
  have hp := PA194ActualPhysicalOrbit.physicalOrbit r tail k n spare (r 0) (le_refl _)
  dsimp only at hp ⊢
  rw [hg] at hp ⊢
  refine ⟨F (timeCode (PA194ModelLoopState.next quad)
    (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers))
      ![r 0,packed g n spare (PA194ModelSourceLoop.source r tail)]+clock,?_⟩
  change F PA194Stepper.stepper ![F addCode ![F (timeCode (PA194ModelLoopState.next quad)
    (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers))
      ![r 0,packed g n spare (PA194ModelSourceLoop.source r tail)],clock],physicalFrame 27 g (frameArgs r n spare)] =
    physicalFrame 31 (((k+1)+r 0)+1+1) a'
  rw [PA194StepperCompose.modelStepperCompose,hp,hzrun]
#print axioms exitsAt31
end models
end PA194ActualPhysicalExit
