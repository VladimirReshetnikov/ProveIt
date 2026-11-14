import PA194MarkedFileStandard
set_option autoImplicit false
namespace PA194IncrementAnywhereStandard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194MarkedFile PA194MarkedFileStandard PA194RegisterFile PA194RegisterFileStandard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem marked_prefix (pre vs : List Nat) :
    M6.Runtime.sepsM pre.length (pre++vs) = M6.Runtime.sepsR pre ++ M6.Runtime.sepsM 0 vs := by
  induction pre with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons,List.cons_append,M6.Runtime.sepsM,M6.Runtime.sepsR,List.flatMap_cons,ih,List.append_assoc]

theorem markedFile_matches_runtime_anywhere (pre : List Nat) (v : Nat) (vs : List Nat) (t : Nat) :
    F (fileCode pre.length)
      (valuesArg pre (F (markedFile vs.length) (valuesArg (v::vs) t))) =
      word (M6.Runtime.sepsM pre.length (pre++v::vs)) t := by
  rw [markedFile_matches_runtime,sourceFile,marked_prefix,word_append]
#print axioms marked_prefix
#print axioms markedFile_matches_runtime_anywhere
end PA194IncrementAnywhereStandard
