import PA194IncrementOutputStandard
import PA194IncrementAnywhereStandard
set_option autoImplicit false
namespace PA194MarkOutputStandard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194MarkedFile PA194RegisterFileStandard PA194ReturnFile PA194ReturnFileMeaning PA194IncrementOutputStandard PA194IncrementAnywhereStandard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem markedReturn_matches_runtime (pre : List Nat) (v : Nat) (vs : List Nat) (t suffix : Nat) :
    F (returnCode pre.length) (Fin.cases (F (markedFile vs.length) (valuesArg (v::vs) suffix)) (valuesArg pre t)) =
      word (M6.Runtime.sepsM pre.length (pre++v::vs)) suffix := by
  rw [modelReturnMeaning,valuesReplace,markedFile_matches_runtime_anywhere]
#print axioms markedReturn_matches_runtime
end PA194MarkOutputStandard
