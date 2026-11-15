import PA194StartupSourceFrame
import PA194RegisterFileStandard
import PA194StandardCodeBridge
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28SeedTail
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StandardCodeBridge PA194RegisterFile PA194RegisterFileStandard PA194StartupSourceFrame

local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

def spareValues : Fin 26 → Nat := PA194RegisterFileStandard.valuesArg (List.replicate 25 1) 0

theorem wordBits (xs : List Bool) : PA194RegisterFileStandard.word xs 0 = PA194Bounded.bits xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [PA194RegisterFileStandard.word,PA194Bounded.bits,ih]; omega

theorem natFileSeedTail : Structure.func (L := language) (fileCode 25) spareValues = seedTail := by
  have h := PA194RegisterFileStandard.sourceFile (List.replicate 25 1) 0
  change Structure.func (L := language) (fileCode 25) spareValues =
    PA194RegisterFileStandard.word (M6.Runtime.sepsR (List.replicate 25 1)) 0 at h
  rw [wordBits] at h
  exact h

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
theorem modelFileSeedTail :
    F (fileCode 25) (fun i => modelNumeral M (spareValues i)) = modelNumeral M seedTail := by
  have h := (modelStandardCode (M := M) (fileCode 25)) spareValues
  rw [natFileSeedTail] at h
  exact h
#print axioms natFileSeedTail
#print axioms modelFileSeedTail
end models
end PA194Site28SeedTail
