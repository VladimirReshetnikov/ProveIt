import PA194Site31FileSplit
import PA194Site31UpdateVector
import PA194Site31ReplaceSimple
import PA194ReturnFileMeaning
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace PA194Site31FileCombine
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PA194RegisterFile PA194ReturnFile PA194ReturnFileMeaning PA194StateOne
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem combine (v : Fin 11 → M) (suffix marked : M) :
    let e : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
    let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
    F (fileCode 10) (Function.update (Function.update v 6 (v 6+1)) 10 suffix) =
      F (fileCode 6) (replaceLast 6 ep
        (F block ![e 0+1,F (fileCode 3) (replaceLast 3 (fun i => e i.succ) suffix)])) := by
  dsimp only
  let e : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
  let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
  have hv := PA194Site31UpdateVector.updateVector v suffix
  have h6 := PA194Site31ReplaceSimple.replaceSix v marked
    (F block ![v 6+1,F (fileCode 3) (replaceLast 3 (fun i => e i.succ) suffix)])
  change replaceLast 6 ep (F block ![e 0+1,F (fileCode 3) (replaceLast 3 (fun i => e i.succ) suffix)]) =
      ![v 0,v 1,v 2,v 3,v 4,v 5,F block ![v 6+1,F (fileCode 3) (replaceLast 3 (fun i => e i.succ) suffix)]] at h6
  have h3 := PA194Site31ReplaceSimple.replaceThree v suffix
  change replaceLast 3 (fun i => e i.succ) suffix = ![v 7,v 8,v 9,suffix] at h3
  rw [hv,h6,h3]
  let vv : Fin 11 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6+1,v 7,v 8,v 9,suffix]
  let tt := F block ![v 6+1,F (fileCode 3) ![v 7,v 8,v 9,suffix]]
  have hvv : (fun i : Fin 5 => vv i.succ.succ.succ.succ.succ.succ) =
      ![v 6+1,v 7,v 8,v 9,suffix] := by
    funext i
    fin_cases i <;> rfl
  have htt : F (fileCode 4) (fun i => vv i.succ.succ.succ.succ.succ.succ) = tt := by
    rw [hvv,modelFileSucc]
    rfl
  exact PA194Site31FileSplit.split vv tt htt
#print axioms combine
end models
end PA194Site31FileCombine
