import PA194MarkAll
import PA194MarkOutputStandard
set_option autoImplicit false
namespace PA194MarkRuntimeStandard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194MarkerScan PA194MarkAll PA194MarkedFile PA194RegisterFile PA194RegisterFileStandard PA194UnaryRuns PA194ReturnFile PA194MarkOutputStandard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem valuesArg_last (vs : List Nat) (t : Nat) : valuesArg vs t (Fin.last vs.length) = t := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have h : (Fin.last vs.length).succ = Fin.last (vs.length+1) := by apply Fin.ext; rfl
    change valuesArg (v::vs) t (Fin.last (vs.length+1)) = t
    rw [←h]
    exact ih

theorem runtimeMarkPositive (first : Nat) (pre vs : List Nat) (v l suffix : Nat)
    (bound : pre.length+1 < 9) :
    let selectedTail := F ones ![v,F (fileCode vs.length) (valuesArg vs suffix)]
    let selectedBlock := (selectedTail+selectedTail+1)+(selectedTail+selectedTail+1)
    let ep := valuesArg (first::pre) selectedBlock
    F PA194Stepper.stepper ![(F (PA194CarryFile.costCode (pre.length+1)) ep+TableDispatch.modelNumeral Nat 3)+F (PA194CarryFile.costCode (pre.length+1)) ep,
      F pairCode ![TableDispatch.modelNumeral Nat (markerControl ⟨pre.length+1,bound⟩),
        F pairCode ![l,word (M6.Runtime.sepsR ((first::pre)++v::vs)) suffix]]] =
    F pairCode ![TableDispatch.modelNumeral Nat 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+word (M6.Runtime.sepsM (pre.length+1) ((first::pre)++v::vs)) suffix+
        word (M6.Runtime.sepsM (pre.length+1) ((first::pre)++v::vs)) suffix]] := by
  let t := F ones ![v,F (fileCode vs.length) (valuesArg vs suffix)]
  let block := (t+t+1)+(t+t+1)
  let ep := valuesArg (first::pre) block
  have ht : ep (Fin.last (pre.length+1)) = (t+t+1)+(t+t+1) := by
    exact valuesArg_last (first::pre) block
  have inputSelected : word (M6.Runtime.sepsR (v::vs)) suffix = block := by
    rw [←sourceFile (v::vs) suffix]
    simp only [List.length_cons]
    rw [modelFileSucc (M := Nat),modelBlock]
    simp only [valuesArg,Fin.cases_zero,Fin.cases_succ]
    have hs := modelOnesSucc (M := Nat) v (F (fileCode vs.length) (valuesArg vs suffix))
    change F ones ![F Code.succ (fun _ => v),_] = F addCode ![F addCode ![t,t],F oneCode Fin.elim0] at hs
    rw [natSucc,natAdd,natAdd,natOne] at hs
    change F addCode ![F ones ![v+1,F (fileCode vs.length) (valuesArg vs suffix)],F ones ![v+1,F (fileCode vs.length) (valuesArg vs suffix)]] = block
    rw [natAdd,hs]
  have inputFile : F (fileCode (pre.length+1)) ep = word (M6.Runtime.sepsR ((first::pre)++v::vs)) suffix := by
    have h := sourceFile (first::pre) block
    simp only [List.length_cons] at h
    rw [h,←inputSelected,←word_append]
    simp [M6.Runtime.sepsR,List.flatMap_append]
  have marked : F (markedFile vs.length) (valuesArg (v::vs) suffix) = (t+t)+(t+t) := by
    rw [modelMarkedFile,modelMarkedBlock]
    simp only [valuesArg,Fin.cases_zero,Fin.cases_succ]
    change F addCode ![F addCode ![t,t],F addCode ![t,t]] = (t+t)+(t+t)
    simp only [natAdd]
  have outputFile : F (returnCode (pre.length+1)) (Fin.cases ((t+t)+(t+t)) ep) =
      word (M6.Runtime.sepsM (pre.length+1) ((first::pre)++v::vs)) suffix := by
    rw [←marked]
    exact markedReturn_matches_runtime (first::pre) v vs block suffix
  have htModel : ep (Fin.last (pre.length+1)) = F addCode ![F addCode ![F addCode ![t,t],F oneCode Fin.elim0],F addCode ![F addCode ![t,t],F oneCode Fin.elim0]] := by
    simpa only [natAdd,natOne] using ht
  have h := modelMarkAllPositive pre.length bound ep l t htModel
  dsimp only at h ⊢
  have outputModel : F (returnCode (pre.length+1)) (Fin.cases (F addCode ![F addCode ![t,t],F addCode ![t,t]]) ep) =
      word (M6.Runtime.sepsM (pre.length+1) ((first::pre)++v::vs)) suffix := by
    simpa only [natAdd] using outputFile
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F (PA194CarryFile.costCode (pre.length+1)) ep,TableDispatch.modelNumeral Nat 3],F (PA194CarryFile.costCode (pre.length+1)) ep],
    F pairCode ![TableDispatch.modelNumeral Nat (markerControl ⟨pre.length+1,bound⟩),F pairCode ![l,F (fileCode (pre.length+1)) ep]]] =
    F pairCode ![TableDispatch.modelNumeral Nat 17,F pairCode ![F halfCode (fun _ => l),F addCode ![F addCode ![F parityCode (fun _ => l), F (returnCode (pre.length+1)) (Fin.cases (F addCode ![F addCode ![t,t],F addCode ![t,t]]) ep)], F (returnCode (pre.length+1)) (Fin.cases (F addCode ![F addCode ![t,t],F addCode ![t,t]]) ep)]]] at h
  rw [inputFile,outputModel] at h
  simp only [natAdd] at h
  exact h
theorem runtimeMarkFirst (v l suffix : Nat) (vs : List Nat) :
    F PA194Stepper.stepper ![TableDispatch.modelNumeral Nat 3,
      F pairCode ![TableDispatch.modelNumeral Nat 113,F pairCode ![l,word (M6.Runtime.sepsR (v::vs)) suffix]]] =
    F pairCode ![TableDispatch.modelNumeral Nat 15,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+word (M6.Runtime.sepsM 0 (v::vs)) suffix+
        word (M6.Runtime.sepsM 0 (v::vs)) suffix]] := by
  let t := F ones ![v,F (fileCode vs.length) (valuesArg vs suffix)]
  have inputSelected : word (M6.Runtime.sepsR (v::vs)) suffix = (t+t+1)+(t+t+1) := by
    rw [←sourceFile (v::vs) suffix]
    simp only [List.length_cons]
    rw [modelFileSucc (M := Nat),modelBlock]
    simp only [valuesArg,Fin.cases_zero,Fin.cases_succ]
    have hs := modelOnesSucc (M := Nat) v (F (fileCode vs.length) (valuesArg vs suffix))
    change F ones ![F Code.succ (fun _ => v),_] = F addCode ![F addCode ![t,t],F oneCode Fin.elim0] at hs
    rw [natSucc,natAdd,natAdd,natOne] at hs
    change F addCode ![F ones ![v+1,F (fileCode vs.length) (valuesArg vs suffix)],F ones ![v+1,F (fileCode vs.length) (valuesArg vs suffix)]] = _
    rw [natAdd,hs]
  have marked : word (M6.Runtime.sepsM 0 (v::vs)) suffix = (t+t)+(t+t) := by
    rw [←PA194MarkedFileStandard.markedFile_matches_runtime,modelMarkedFile (M := Nat),modelMarkedBlock (M := Nat)]
    simp only [valuesArg,Fin.cases_zero,Fin.cases_succ]
    change F addCode ![F addCode ![t,t],F addCode ![t,t]] = _
    simp only [natAdd]
  have h := PA194MarkDelimiter.modelMarkDelimiter (M := Nat) l t
  change F PA194Stepper.stepper ![TableDispatch.modelNumeral Nat 3,
    F pairCode ![TableDispatch.modelNumeral Nat 113,F pairCode ![l,F addCode ![F addCode ![F addCode ![t,t],F oneCode Fin.elim0],F addCode ![F addCode ![t,t],F oneCode Fin.elim0]]]]] =
    F pairCode ![TableDispatch.modelNumeral Nat 15,F pairCode ![F halfCode (fun _ => l),F addCode ![F addCode ![F parityCode (fun _ => l),F addCode ![F addCode ![t,t],F addCode ![t,t]]],F addCode ![F addCode ![t,t],F addCode ![t,t]]]]] at h
  simp only [natAdd,natOne] at h
  rw [←inputSelected,←marked] at h
  exact h
#print axioms runtimeMarkFirst
#print axioms runtimeMarkPositive
end PA194MarkRuntimeStandard
