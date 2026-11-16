import PA194ActualPhysicalExit
import PA194RestorePhysicalExit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SeedGapBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ModelSourceLoop PA194ActualLoopOrbit PA194SourceSite31Physical PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem firstRestoreGap (r : Fin 9 → M) (tail n spare : M) :
    let r31 := running r (r 0)
    let k31 := modelNumeral M 39+r 0
    let count := (n+r 0)+r 0
    let site36Gap := k31+r31 6
    modelNumeral M 39 ≤ site36Gap ∧
    ∃ time : M, F PA194Stepper.stepper ![time,physicalFrame 27 (modelNumeral M 42) (frameArgs r n spare)] =
      physicalFrame 31 (((k31+1)+1)+1) (frameArgs r31 count spare) := by
  dsimp only
  let r31 := running r (r 0)
  let k31 := modelNumeral M 39+r 0
  have h0 : modelNumeral M 39 ≤ k31 := le_add_of_nonneg_right (zero_le : (0 : M) ≤ r 0)
  have hb : modelNumeral M 39 ≤ k31+r31 6 := le_trans h0 (le_add_of_nonneg_right (zero_le : (0 : M) ≤ r31 6))
  refine ⟨hb,?_⟩
  have h := PA194ActualPhysicalExit.exitsAt31 r tail (modelNumeral M 39) n spare
  dsimp only at h
  have hg : (((modelNumeral M 39+1)+1)+1)+r 0 = (((k31+1)+1)+1) := by
    dsimp only [k31]
    simp only [add_assoc,add_comm,add_left_comm]
  have h42 : ((modelNumeral M 39+1)+1)+1 = modelNumeral M 42 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  rw [hg,h42] at h
  exact h
#print axioms firstRestoreGap
end models
end PA194SeedGapBound
