import PA194SeedToFirstRestore
import PA194Site35RestoreEntry
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SeedValues
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SeedFrameAlignment PA194StartupSourceFrame PA194ModelSourceLoop PA194ActualLoopOrbit PA194RegisterPermutation PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem reg0 : seedRegs (M := M) 0 = (1 : M) := by
  simp [seedRegs,seedArgs30,PA194Site29OutputWithCarry.updated,PA194Site28OutputFile.updated]
theorem reg6 : seedRegs (M := M) 6 = (1 : M) := by
  simp [seedRegs,seedArgs30,PA194Site29OutputWithCarry.updated,PA194Site28OutputFile.updated,seedArgs]
  rfl
theorem reg8 : seedRegs (M := M) 8 = (1 : M) := by
  simp [seedRegs,seedArgs30,PA194Site29OutputWithCarry.updated,PA194Site28OutputFile.updated,seedArgs]
  rfl

theorem firstSite36Gap :
    let r := seedRegs (M := M)
    let r31 := running r (r 0)
    (modelNumeral M 39+r 0)+r31 6 = modelNumeral M 42 := by
  dsimp only
  rw [show running (seedRegs (M := M)) (seedRegs 0) 6 = seedRegs 6+seedRegs 0 from by simp [running]]
  rw [reg0,reg6]
  rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]

theorem firstSite34Guard :
    let r := seedRegs (M := M)
    let r31 := running r (r 0)
    let n31 := (modelNumeral M 27+r 0)+r 0
    let r' := PA194ModelRestoreSource.running r31 (r31 6)
    let n' := n31+r31 6
    let args := frameArgs r' n' (seedArgs30 (M := M) 9)
    let output := PA194Site31OutputFile.updated args n'
    output 8 = (1 : M)+1 := by
  dsimp only
  simp [PA194Site31OutputFile.updated,frameArgs,PA194ActualSourceLoop.args,
    PA194ModelRestoreSource.running,running,reg0,reg8]
#print axioms reg0
#print axioms reg6
#print axioms reg8
#print axioms firstSite36Gap
#print axioms firstSite34Guard
end models
end PA194SeedValues
