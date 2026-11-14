import PA194IncrementAnywhere
import PA194IncrementAnywhereStandard
import PA194IncrementOutputStandard
import PA194MarkRuntimeStandard
set_option autoImplicit false
namespace PA194IncrementRuntimeStandard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194IncrementAnywhere PA194MarkedFile PA194RegisterFile PA194RegisterFileStandard PA194ReturnFile PA194ReturnFileMeaning PA194CarryFile PA194IncrementAnywhereStandard PA194IncrementOutputStandard PA194MarkRuntimeStandard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)
local notation a " ⊕ " b => F addCode ![a,b]
def oneN : Nat := F oneCode Fin.elim0

theorem runtimeIncrement (pre vs : List Nat) (v l : Nat) :
    let selected := valuesArg (v::vs) 0
    let prefArgs := valuesArg pre (F (markedFile vs.length) selected)
    let prefCost := F (costCode pre.length) prefArgs
    let restCost := F (costCode vs.length) (fun i => selected i.succ)
    let front := ((oneN ⊕ oneN) ⊕ selected 0) ⊕ restCost
    let incrementCost := (((front ⊕ TableDispatch.modelNumeral Nat 6) ⊕ restCost) ⊕ (((selected 0 ⊕ oneN) ⊕ oneN) ⊕ oneN))
    F PA194Stepper.stepper ![(prefCost ⊕ incrementCost) ⊕ prefCost,
      F pairCode ![TableDispatch.modelNumeral Nat 2,F pairCode ![l,word (M6.Runtime.sepsM pre.length (pre++v::vs)) 0]]] =
    F pairCode ![TableDispatch.modelNumeral Nat 7,F pairCode ![F halfCode (fun _ => l),
      (F parityCode (fun _ => l) ⊕ word (M6.Runtime.sepsR (pre++(v+1)::vs++[1])) 0) ⊕
        word (M6.Runtime.sepsR (pre++(v+1)::vs++[1])) 0]] := by
  let es := valuesArg (v::vs) 0
  let ep := valuesArg pre (F (markedFile vs.length) es)
  have hz : es (Fin.last (vs.length+1)) = 0 := valuesArg_last (v::vs) 0
  have hp : ep (Fin.last pre.length) = F (markedFile vs.length) es := valuesArg_last pre _
  have h := modelIncrementAnywhere pre.length vs.length ep es l hp hz
  dsimp only at h ⊢
  have hi := markedFile_matches_runtime_anywhere pre v vs 0
  change F (fileCode pre.length) ep = _ at hi
  rw [hi] at h
  have he0 : es 0 = v := rfl
  have herest : (fun i => es i.succ) = valuesArg vs 0 := rfl
  have ho := incrementOutput_matches_runtime pre vs v (F (markedFile vs.length) es)
  have hreplace := valuesReplace vs 0 6
  dsimp only [es] at herest
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F (costCode pre.length) ep,
    F addCode ![F addCode ![F addCode ![F addCode ![F addCode ![F addCode ![F oneCode Fin.elim0,F oneCode Fin.elim0],v],F (costCode vs.length) (valuesArg vs 0)],TableDispatch.modelNumeral Nat 6],F (costCode vs.length) (valuesArg vs 0)],F addCode ![F addCode ![F addCode ![v,F oneCode Fin.elim0],F oneCode Fin.elim0],F oneCode Fin.elim0]]],F (costCode pre.length) ep],
    F pairCode ![TableDispatch.modelNumeral Nat 2,F pairCode ![l,word (M6.Runtime.sepsM pre.length (pre++v::vs)) 0]]] =
    F pairCode ![TableDispatch.modelNumeral Nat 7,F pairCode ![F halfCode (fun _ => l),F addCode ![F parityCode (fun _ => l),F addCode ![
      F (returnCode pre.length) (Fin.cases (F block ![F addCode ![v,F oneCode Fin.elim0],F (fileCode vs.length) (replaceLast vs.length (valuesArg vs 0) (F addCode ![F addCode ![F addCode ![F oneCode Fin.elim0,F oneCode Fin.elim0],F oneCode Fin.elim0],F addCode ![F addCode ![F oneCode Fin.elim0,F oneCode Fin.elim0],F oneCode Fin.elim0]]))]) ep),
      F (returnCode pre.length) (Fin.cases (F block ![F addCode ![v,F oneCode Fin.elim0],F (fileCode vs.length) (replaceLast vs.length (valuesArg vs 0) (F addCode ![F addCode ![F addCode ![F oneCode Fin.elim0,F oneCode Fin.elim0],F oneCode Fin.elim0],F addCode ![F addCode ![F oneCode Fin.elim0,F oneCode Fin.elim0],F oneCode Fin.elim0]]))]) ep)]]]] at h
  simp only [natAdd,natOne] at h
  rw [hreplace] at h
  rw [ho] at h
  simp only [oneN,natAdd,natOne]
  simp only [valuesArg,Fin.cases_zero,Fin.cases_succ]
  change F PA194Stepper.stepper ![(F (costCode pre.length) ep + ((((1+1)+v+F (costCode vs.length) (valuesArg vs 0))+TableDispatch.modelNumeral Nat 6+F (costCode vs.length) (valuesArg vs 0))+(v+1+1+1))) + F (costCode pre.length) ep,
    F pairCode ![TableDispatch.modelNumeral Nat 2,F pairCode ![l,word (M6.Runtime.sepsM pre.length (pre++v::vs)) 0]]] =
    F pairCode ![TableDispatch.modelNumeral Nat 7,F pairCode ![F halfCode (fun _ => l),
      (F parityCode (fun _ => l)+word (M6.Runtime.sepsR (pre++(v+1)::vs++[1])) 0)+word (M6.Runtime.sepsR (pre++(v+1)::vs++[1])) 0]]
  simpa only [Nat.add_assoc] using h
#print axioms runtimeIncrement
end PA194IncrementRuntimeStandard
