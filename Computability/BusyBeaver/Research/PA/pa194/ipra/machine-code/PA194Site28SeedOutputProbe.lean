import Mathlib.Tactic.Ring
import PA194Site28SeedTailRoundTrip
import PA194ReturnFileMeaning
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194Site28SeedOutputProbe
open DiophantineConsistency LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194UnaryRuns PA194RegisterFile PA194ReturnFile PA194ReturnFileMeaning PA194RegisterFileStandard PA194StartupSourceFrame
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)
theorem probe :
  F (returnCode 24) (Fin.cases 54 (fun _ => 1)) = F block ![1,seedTail] := by
  rw [modelReturnMeaning]
  have hv : replaceLast 24 (fun _ => 1) 54 = valuesArg (List.replicate 24 1) 54 := by
    funext i
    fin_cases i <;> rfl
  have hs := sourceFile (List.replicate 24 1) 54
  change F (fileCode 24) (valuesArg (List.replicate 24 1) 54) = _ at hs
  rw [hv,hs]
  have h54 : 54 = word (M6.Runtime.sepsR (List.replicate 2 1)) 0 := by decide +kernel
  have hseed : seedTail = word (M6.Runtime.sepsR (List.replicate 25 1)) 0 :=
    (PA194Site28SeedTail.wordBits _).symm
  have hblock (x : Nat) : F block ![1,x] = word (M6.Runtime.sepsR [1]) x := by
    clear hv hs h54 hseed
    rw [modelBlock]
    change F addCode ![F ones ![2,x],F ones ![2,x]] = _
    rw [natAdd,modelOnesNat]
    simp [M6.Runtime.sepsR,word]
    ring
  have hlist : M6.Runtime.sepsR (List.replicate 24 1) ++ M6.Runtime.sepsR (List.replicate 2 1) =
      M6.Runtime.sepsR [1] ++ M6.Runtime.sepsR (List.replicate 25 1) := by decide +kernel
  rw [h54,hblock,hseed,←word_append,←word_append,hlist]
#print axioms probe
end PA194Site28SeedOutputProbe
