import PA194ActualPhysicalOrbit
import PA194TransferMacroWidths
import Mathlib.Tactic.Abel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194LoopWidthOrbit
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

theorem physicalOrbitWidth (r : Fin 9 → M) (tail k n spare steps : M) (h : steps ≤ r 0) :
    let g := (((k+1)+1)+1)
    let x := packed g n spare (PA194ModelSourceLoop.source r tail)
    let a := frameArgs r n spare
    let a' := frameArgs (PA194ModelSourceLoop.running r steps) ((n+steps)+steps) spare
    F PA194Stepper.stepper ![F (timeCode (PA194ModelLoopState.next quad)
      (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers)) ![steps,x],physicalFrame 27 g a] =
        physicalFrame 27 (g+steps) a' ∧
    PA194TransferMacroWidths.width 27 (g+steps) = PA194TransferMacroWidths.width 27 g + steps ∧
    PA194TransferMacroWidths.width 27 g ≤ PA194TransferMacroWidths.width 27 (g+steps) := by
  dsimp only
  refine ⟨PA194ActualPhysicalOrbit.physicalOrbit r tail k n spare steps h, ?_, ?_⟩
  · simp only [PA194TransferMacroWidths.width]
    abel
  · have he : PA194TransferMacroWidths.width 27 ((((k+1)+1)+1)+steps) =
        PA194TransferMacroWidths.width 27 (((k+1)+1)+1) + steps := by
      simp only [PA194TransferMacroWidths.width]
      abel
    rw [he]
    exact le_add_of_nonneg_right (zero_le : (0 : M) ≤ steps)
#print axioms physicalOrbitWidth
end models
end PA194LoopWidthOrbit
