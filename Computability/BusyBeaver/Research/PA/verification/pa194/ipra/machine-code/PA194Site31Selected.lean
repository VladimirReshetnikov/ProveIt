import PA194Site31SelectedThrough
import PA194RegisterPermutation
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31Selected
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194OnesCommute
open TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- From the site-31 third-pass control-2 layout, process the marked
logical register zero and scan the three subsequent registers. -/
theorem selected (k l : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let e : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
    let marked := F (markedFile 3) e
    let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
    let file := F (fileCode 6) ep
    let pl := F (PA194PrefixFile.leftCode 6) (Fin.cases (F ones ![k+1,l]) ep)
    let front := (((1 : M)+1)+e 0)+F (costCode 3) (fun i => e i.succ)
    F PA194Stepper.stepper ![((k+1)+F (costCode 6) ep)+front,
      F pairCode ![modelNumeral M 2,F pairCode ![l,F ones ![k,file+file+1]]]] =
    F pairCode ![(1 : M),F pairCode ![F (leftCode 3)
      (Fin.cases (F ones ![e 0,(pl+pl)+(pl+pl)+1]) (fun i => e i.succ)),e 4]] := by
  dsimp only
  let v := physicalArgs args
  let e : Fin 5 → M := fun i => v ⟨i.val+6,by omega⟩
  let marked := F (markedFile 3) e
  let ep : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,marked]
  let file := F (fileCode 6) ep
  have hword : F ones ![k,file+file+1] = F ones ![k+1,file] := by
    rw [modelOnesCommute]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],file]
    rw [modelAddOne,modelOnesSucc]
  have hp : ep 6 = F (markedFile 3) e := by rfl
  have h := PA194Site31SelectedThrough.selectedThrough (k+1) l ep e hp
  dsimp only at h
  rw [hword]
  exact h
#print axioms selected
end models
end PA194Site31Selected
