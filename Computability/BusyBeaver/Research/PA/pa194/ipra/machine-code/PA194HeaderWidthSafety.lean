import PA194SourcePathDepth
import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SeedFirstSite3661
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194HeaderWidthSafety
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRASubAddition PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem gapAtLeast21 (i : Nat) (gap : M)
    (hwidth : gap + modelNumeral M (PA194SourceProgram.path i).length = modelNumeral M 57) :
    modelNumeral M 21 ≤ gap := by
  have hlen := PA194SourcePathDepth.sourcePathBound i
  have hle : modelNumeral M (PA194SourceProgram.path i).length ≤ modelNumeral M 36 := by
    by_cases heq : (PA194SourceProgram.path i).length = 36
    · rw [heq]
    · exact le_of_lt (modelNumeralStrict _ _ (lt_of_le_of_ne hlen heq))
  have h := add_le_add_left hle (modelNumeral M 21)
  have hnum : modelNumeral M 36 + modelNumeral M 21 = modelNumeral M 57 := by rw [←modelNumeralAdd]
  rw [hnum,←hwidth] at h
  have h' : modelNumeral M 21 + modelNumeral M (PA194SourceProgram.path i).length ≤
      gap + modelNumeral M (PA194SourceProgram.path i).length := by
    calc
      _ = modelNumeral M (PA194SourceProgram.path i).length + modelNumeral M 21 := add_comm _ _
      _ ≤ _ := h
  exact le_of_add_le_add_right h' 

theorem gapAtLeast2 (i : Nat) (gap : M)
    (hwidth : gap + modelNumeral M (PA194SourceProgram.path i).length = modelNumeral M 57) :
    modelNumeral M 2 ≤ gap := by
  have hsmall : modelNumeral M 2 ≤ modelNumeral M 21 := le_of_lt (modelNumeralStrict 2 21 (by decide))
  exact le_trans hsmall (gapAtLeast21 i gap hwidth)
#print axioms gapAtLeast21
#print axioms gapAtLeast2
end models
end PA194HeaderWidthSafety
