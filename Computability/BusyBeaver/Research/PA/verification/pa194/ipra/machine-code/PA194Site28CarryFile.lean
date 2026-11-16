import PA194Site28CarryCell
import PA194RegisterFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28CarryFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28CarryCell PA194RegisterFile PA194UnaryRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

def carryTime : (n : Nat) → (Fin (n+2) → M) → M
  | 0, _ => 0
  | n+1, e => ((1 : M)+(e 0+1))+carryTime n (fun i => e i.succ)

def carryLeft : (n : Nat) → M → (Fin (n+2) → M) → M
  | 0, l, _ => l
  | n+1, l, e => carryLeft n (F ones ![e 0+1,l+l]) (fun i => e i.succ)

theorem carryFile (n : Nat) (e : Fin (n+2) → M) (l : M) :
    F PA194Stepper.stepper ![carryTime n e,F pairCode ![modelNumeral M 3,
      F pairCode ![l,F ones ![e 0+1,F (fileCode n) (fun i => e i.succ)]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![carryLeft n l e,
      F ones ![e ⟨n,by omega⟩+1,e (Fin.last (n+1))]]] := by
  induction n generalizing l with
  | zero =>
    change F PA194Stepper.stepper ![F (Code.zero 0) Fin.elim0,_] = _
    rw [PA194Stepper.modelStepperZero]
    change F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![e 0+1,F (.proj 0) (fun i => e i.succ)]]] = _
    rw [modelProjection]
    rfl
  | succ n ih =>
    let e1 : Fin (n+2) → M := fun i => e i.succ
    let tail := F ones ![e1 0+1,F (fileCode n) (fun i => e1 i.succ)]
    let next := F ones ![e 0+1,l+l]
    have hf : F (fileCode (n+1)) (fun i => e i.succ) = tail+tail := by
      rw [modelFileSucc,modelBlock]
    have h1 := carryCell (M := M) (e 0) l tail
    rw [←hf] at h1
    have h2 := ih e1 next
    change F PA194Stepper.stepper ![F addCode ![(1 : M)+(e 0+1),carryTime n e1],_] = _
    rw [PA194StepperCompose.modelStepperCompose,h1,h2]
    rfl
#print axioms carryFile
end models
end PA194Site28CarryFile
