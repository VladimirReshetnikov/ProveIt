import PA194SeedControllerReturn27
import PA194LoopMinimumWidth
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SeedMinimumWidth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ActualSourceLoop PA194ModelLoopState PA194ModelLoopIteration PA194ModelLoopCost PA194ControllerLoopFrame PA194SeedFrameAlignment PA194ModelSourceLoop PA194ActualLoopOrbit PA194SourceSite31Physical PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem seedWidthIs49 : PA194TransferMacroWidths.width 27 (((modelNumeral M 39+1)+1)+1) = modelNumeral M 49 := by
  have hpath : (PA194SourceProgram.path 27).length = 7 := by decide +kernel
  simp only [PA194TransferMacroWidths.width,hpath]
  rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]

theorem blankReachesMinimumWidth :
    let a := seedArgs30 (M := M)
    let g := (((modelNumeral M 39+1)+1)+1)
    ∃ clock : M, F PA194Stepper.stepper ![clock,modelNumeral M 0] = physicalFrame 27 g a ∧
      modelNumeral M 48 ≤ PA194TransferMacroWidths.width 27 g := by
  dsimp only
  obtain ⟨_,clock,hp⟩ := PA194SeedControllerReturn27.blankAndFiveSteps (M := M) (0 : M)
  have hg : (((modelNumeral M 38+1)+1)+1)+1 = (((modelNumeral M 39+1)+1)+1) := by
    have hh : modelNumeral M 38 + (1 : M) = modelNumeral M 39 := by rw [←modelNumeralOne,←modelNumeralAdd]
    rw [hh]
  change F PA194Stepper.stepper ![clock,modelNumeral M 0] = physicalFrame 27
    ((((modelNumeral M 38+1)+1)+1)+1) (seedArgs30 (M := M)) at hp
  rw [hg] at hp
  refine ⟨clock,hp,?_⟩
  rw [seedWidthIs49]
  exact le_of_lt (modelNumeralStrict 48 49 (by decide))
theorem blankToSafeOrbit (tail steps : M) (hsteps : steps ≤ seedRegs (M := M) 0) :
    let r := seedRegs (M := M)
    let n := modelNumeral M 27
    let spare := seedArgs30 (M := M) 9
    let g := (((modelNumeral M 39+1)+1)+1)
    let x := packed g n spare (PA194ModelSourceLoop.source r tail)
    let a := frameArgs r n spare
    let a' := frameArgs (PA194ModelSourceLoop.running r steps) ((n+steps)+steps) spare
    ∃ clock : M,
      F PA194Stepper.stepper ![clock,modelNumeral M 0] = physicalFrame 27 g a ∧
      F PA194Stepper.stepper ![F (timeCode (PA194ModelLoopState.next quad)
        (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers)) ![steps,x],
          F PA194Stepper.stepper ![clock,modelNumeral M 0]] = physicalFrame 27 (g+steps) a' ∧
      modelNumeral M 48 ≤ PA194TransferMacroWidths.width 27 (g+steps) ∧
      modelNumeral M 12 ≤ g+steps := by
  dsimp only
  obtain ⟨clock,hp,hw⟩ := blankReachesMinimumWidth (M := M)
  rw [←seedFrame (M := M)] at hp
  have horbit := PA194LoopMinimumWidth.physicalOrbitMinimum (seedRegs (M := M)) tail
    (modelNumeral M 39) (modelNumeral M 27) (seedArgs30 (M := M) 9) steps hsteps hw
  obtain ⟨hphys,hwidth,hgap⟩ := horbit
  refine ⟨clock,hp,?_,hwidth,hgap⟩
  rw [hp]
  exact hphys
#print axioms blankToSafeOrbit
#print axioms seedWidthIs49
#print axioms blankReachesMinimumWidth
end models
end PA194SeedMinimumWidth
