import PA194MarkedFile
import PA194RegisterFileStandard
set_option autoImplicit false
namespace PA194MarkedFileStandard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194MarkedFile PA194RegisterFileStandard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem markedFile_matches_runtime (v : Nat) (vs : List Nat) (t : Nat) :
    F (markedFile vs.length) (valuesArg (v::vs) t) =
      word (M6.Runtime.sepsM 0 (v::vs)) t := by
  rw [modelMarkedFile]
  simp only [valuesArg,Fin.cases_zero,Fin.cases_succ]
  rw [modelMarkedBlock,sourceFile,modelOnesNat]
  change F addCode ![F addCode ![word (List.replicate v true) (word (M6.Runtime.sepsR vs) t),
      word (List.replicate v true) (word (M6.Runtime.sepsR vs) t)],
      F addCode ![word (List.replicate v true) (word (M6.Runtime.sepsR vs) t),
      word (List.replicate v true) (word (M6.Runtime.sepsR vs) t)]] = _
  simp only [natAdd]
  simp only [M6.Runtime.sepsM,word, Bool.toNat_false,add_zero,word_append]
  omega
#print axioms markedFile_matches_runtime
end PA194MarkedFileStandard
