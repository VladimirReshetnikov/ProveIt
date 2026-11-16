import PA194LoopWidthOrbit
import PA194MinimumWidthSafety
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194LoopMinimumWidth
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

theorem physicalOrbitMinimum (r : Fin 9 → M) (tail k n spare steps : M) (h : steps ≤ r 0)
    (hwidth : modelNumeral M 48 ≤ PA194TransferMacroWidths.width 27 (((k+1)+1)+1)) :
    let g := (((k+1)+1)+1)
    let x := packed g n spare (PA194ModelSourceLoop.source r tail)
    let a := frameArgs r n spare
    let a' := frameArgs (PA194ModelSourceLoop.running r steps) ((n+steps)+steps) spare
    F PA194Stepper.stepper ![F (timeCode (PA194ModelLoopState.next quad)
      (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers)) ![steps,x],physicalFrame 27 g a] =
        physicalFrame 27 (g+steps) a' ∧
    modelNumeral M 48 ≤ PA194TransferMacroWidths.width 27 (g+steps) ∧
    modelNumeral M 12 ≤ g+steps := by
  dsimp only
  obtain ⟨hp,_,hmono⟩ := PA194LoopWidthOrbit.physicalOrbitWidth r tail k n spare steps h
  have hw : modelNumeral M 48 ≤ PA194TransferMacroWidths.width 27 ((((k+1)+1)+1)+steps) :=
    le_trans hwidth hmono
  refine ⟨hp,hw,?_⟩
  apply PA194MinimumWidthSafety.gapAtLeast12 (modelNumeral M 27)
  rw [PA194PathLengthCode.modelPathLength ⟨27,by decide⟩]
  exact hw
#print axioms physicalOrbitMinimum
end models
end PA194LoopMinimumWidth
