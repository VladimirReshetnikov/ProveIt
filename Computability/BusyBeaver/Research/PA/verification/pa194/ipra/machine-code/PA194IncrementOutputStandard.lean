import PA194MarkedFileStandard
import PA194ReturnFileMeaning
set_option autoImplicit false
namespace PA194IncrementOutputStandard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194MarkedFile PA194MarkedFileStandard PA194RegisterFile PA194RegisterFileStandard PA194ReturnFileMeaning PA194ReturnFile
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem valuesReplace (vs : List Nat) (t u : Nat) :
    replaceLast vs.length (valuesArg vs t) u = valuesArg vs u := by
  induction vs with
  | nil =>
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  | cons v vs ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Fin.snoc _ _ (Fin.castSucc 0) = _
      simp [valuesArg,replaceLast]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · have h := congrFun ih (Fin.last vs.length)
        simp only [replaceLast,Fin.snoc_last] at h
        have hl : (Fin.last vs.length).succ = Fin.last (vs.length+1) := Fin.ext rfl
        simp only [valuesArg,Fin.cases_succ]
        rw [hl]
        change Fin.snoc _ _ (Fin.last (vs.length+1)) = _
        rw [Fin.snoc_last]
        exact h
      · have h := congrFun ih k.castSucc
        simp only [replaceLast,Fin.snoc_castSucc] at h
        change Fin.snoc _ _ (Fin.castSucc k.succ) = _
        simp only [Fin.snoc_castSucc,valuesArg,Fin.cases_succ]
        exact h
theorem incrementOutput_matches_runtime (pre vs : List Nat) (v t : Nat) :
    F (returnCode pre.length) (Fin.cases
      (F block ![v+1,F (fileCode vs.length) (valuesArg vs 6)]) (valuesArg pre t)) =
      word (M6.Runtime.sepsR (pre++((v+1)::vs)++[1])) 0 := by
  rw [modelReturnMeaning,valuesReplace,sourceFile]
  have hv : F block ![v+1,F (fileCode vs.length) (valuesArg vs 6)] =
      word (M6.Runtime.sepsR ((v+1)::vs)) 6 := by
    rw [←sourceFile ((v+1)::vs) 6]
    simp only [List.length_cons]
    rw [modelFileSucc (M := Nat)]
    rfl
  rw [hv]
  have hs : word (M6.Runtime.sepsR [1]) 0 = 6 := by decide
  rw [←hs]
  simp only [M6.Runtime.sepsR,List.flatMap_append,word_append]
#print axioms incrementOutput_matches_runtime
#print axioms valuesReplace
end PA194IncrementOutputStandard
