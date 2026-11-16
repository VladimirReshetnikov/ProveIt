import PA194BoundedPCWidthSafety
import PA194HeaderWidthSafety
import Mathlib.Data.List.GetD
import PA194SourcePathDepth
import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SeedFirstSite3661
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194PathLengthCode
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAExhaustion PRASubAddition PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing
def pathLengths : List Nat := (List.range 3673).map (fun i => (PA194SourceProgram.path i).length)
def pathLengthCode : Code 1 := TableDispatch.lookupCode 0 pathLengths

theorem pathLengthsAt (i : Fin 3673) : pathLengths.getD i.val 0 = (PA194SourceProgram.path i.val).length := by
  have hi : i.val < pathLengths.length := by simpa only [pathLengths,List.length_map,List.length_range] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp only [pathLengths,List.getElem_map,List.getElem_range]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem modelPathLength (i : Fin 3673) :
    F pathLengthCode (fun _ => modelNumeral M i.val) = modelNumeral M (PA194SourceProgram.path i.val).length := by
  rw [pathLengthCode,TableDispatch.modelLookupNumeral,pathLengthsAt]

theorem modelWidthGapAtLeast21 (pc gap : M) (hpc : pc < modelNumeral M 3673)
    (hwidth : gap + F pathLengthCode (fun _ => pc) = modelNumeral M 57) :
    modelNumeral M 21 ≤ gap := by
  obtain ⟨i,hi,_⟩ := PA194BoundedPCWidthSafety.resolveBoundedPC pc hpc
  rw [hi,modelPathLength i] at hwidth
  exact PA194HeaderWidthSafety.gapAtLeast21 i.val gap hwidth

#print axioms pathLengthsAt
#print axioms modelPathLength
#print axioms modelWidthGapAtLeast21
end models
end PA194PathLengthCode
