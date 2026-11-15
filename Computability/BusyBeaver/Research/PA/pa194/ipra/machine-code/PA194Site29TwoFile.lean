import PA194Site29TwoBlock
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29TwoFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterFile PA194UnaryRuns PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def nextLeft (n l : M) : M :=
  let a := F ones ![n,l]
  (a+a)+(a+a)+1
def finalLeft : (m : Nat) → M → M → (Fin (m+1) → M) → M
  | 0, _, l, _ => l
  | m+1, n, l, e => finalLeft m (e 0) (nextLeft n l) (fun i => e i.succ)
def finalCount : (m : Nat) → M → (Fin (m+1) → M) → M
  | 0, n, _ => n
  | m+1, _, e => finalCount m (e 0) (fun i => e i.succ)
def fileClock : (m : Nat) → M → (Fin (m+1) → M) → M
  | 0, _, _ => 0
  | m+1, n, e => (n+modelNumeral M 2)+fileClock m (e 0) (fun i => e i.succ)

theorem traverseFile (m : Nat) (n l : M) (e : Fin (m+1) → M) :
    F PA194Stepper.stepper ![fileClock m n e,F pairCode ![modelNumeral M 2,
      F pairCode ![l,F ones ![n,F (fileCode m) e]]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![finalLeft m n l e,
      F ones ![finalCount m n e,e (Fin.last m)]]] := by
  induction m generalizing n l with
  | zero =>
    dsimp only [fileClock,finalLeft,finalCount]
    have hz := PA194Stepper.modelStepperZero (F pairCode ![modelNumeral M 2,
      F pairCode ![l,F ones ![n,F (fileCode 0) e]]])
    change F PA194Stepper.stepper ![(0 : M),_] = _ at hz
    rw [hz]
    have he : F (fileCode 0) e = e 0 := by exact modelProjection 0 e
    rw [he]
    rfl
  | succ m ih =>
    dsimp only [fileClock,finalLeft,finalCount]
    let rest : Fin (m+1) → M := fun i => e i.succ
    let left := nextLeft n l
    have h := PA194Site29TwoBlock.fileHop m n l e
    dsimp only at h
    change F PA194Stepper.stepper ![n+modelNumeral M 2,_] =
      F pairCode ![modelNumeral M 2,F pairCode ![left,F ones ![e 0,F (fileCode m) rest]]] at h
    have hr := ih (e 0) left rest
    dsimp only [rest] at hr
    change F PA194Stepper.stepper ![F addCode ![n+modelNumeral M 2,fileClock m (e 0) rest],_] = _
    rw [PA194StepperCompose.modelStepperCompose,h,hr]
    rw [Fin.succ_last]
#print axioms traverseFile
end models
end PA194Site29TwoFile
