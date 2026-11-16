import PA194SeedGapBound
import PA194SeedFrameAlignment
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SeedToFirstRestore
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SeedFrameAlignment PA194ModelSourceLoop PA194ActualLoopOrbit PA194SourceSite31Physical PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem blankToFirstRestore (tail : M) :
    let r := seedRegs (M := M)
    let n := modelNumeral M 27
    let spare := seedArgs30 (M := M) 9
    let r31 := running r (r 0)
    let k31 := modelNumeral M 39+r 0
    let count := (n+r 0)+r 0
    modelNumeral M 39 ≤ k31+r31 6 ∧
    ∃ c0 c1 : M, F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,modelNumeral M 0]] =
      physicalFrame 31 (((k31+1)+1)+1) (frameArgs r31 count spare) := by
  dsimp only
  let r := seedRegs (M := M)
  let n := modelNumeral M 27
  let spare := seedArgs30 (M := M) 9
  have hbound := PA194SeedGapBound.firstRestoreGap r tail n spare
  dsimp only at hbound
  obtain ⟨bound,c1,h31⟩ := hbound
  have hseed := PA194SeedControllerReturn27.blankAndFiveSteps (M := M) tail
  dsimp only at hseed
  obtain ⟨_,c0,h27⟩ := hseed
  have hgap : ((((modelNumeral M 38+1)+1)+1)+1) = modelNumeral M 42 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  have ha := seedFrame (M := M)
  change F PA194Stepper.stepper ![c0,modelNumeral M 0] =
    physicalFrame 27 ((((modelNumeral M 38+1)+1)+1)+1) (seedArgs30 (M := M)) at h27
  rw [hgap,←ha] at h27
  refine ⟨bound,c0,c1,?_⟩
  rw [h27,h31]
#print axioms blankToFirstRestore
end models
end PA194SeedToFirstRestore
