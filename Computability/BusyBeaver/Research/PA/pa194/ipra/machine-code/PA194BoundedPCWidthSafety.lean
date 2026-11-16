import PA194HeaderWidthSafety
import PA194SourcePathDepth
import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SeedFirstSite3661
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194BoundedPCWidthSafety
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAExhaustion PRASubAddition PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
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
theorem resolveBoundedPC (pc : M) (hpc : pc < modelNumeral M 3673) :
    ∃ i : Fin 3673, pc = modelNumeral M i.val ∧ (PA194SourceProgram.path i.val).length ≤ 36 := by
  obtain ⟨i,hi⟩ := modelBelowNumeral 3673 pc hpc
  exact ⟨i,hi,PA194SourcePathDepth.sourcePathBound i.val⟩

theorem boundedPCGapAtLeast21 (pc gap : M) (hpc : pc < modelNumeral M 3673)
    (hwidth : ∀ i : Fin 3673, pc = modelNumeral M i.val →
      gap + modelNumeral M (PA194SourceProgram.path i.val).length = modelNumeral M 57) :
    modelNumeral M 21 ≤ gap := by
  obtain ⟨i,hi,_⟩ := resolveBoundedPC pc hpc
  exact PA194HeaderWidthSafety.gapAtLeast21 i.val gap (hwidth i hi)

#print axioms resolveBoundedPC
#print axioms boundedPCGapAtLeast21
end models
end PA194BoundedPCWidthSafety
