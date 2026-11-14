import PA194RollbackCell
import PA194ReturnCell
import PA194ReturnFileMeaning
import PA194StepperCompose
import PA194ReturnedDecrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroSelectedRollback
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAExhaustion PA194RollbackCell PA194BinaryDouble
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ReturnCell PA194ReturnFileMeaning PA194BinaryDouble
open PA194ReturnedDecrement PA194MarkedFile PA194CarryFile PA194ReturnFile
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- The selected-register-zero output rolls the residual first block back
across the head. All values and the clock may be nonstandard. -/
theorem rollbackSelectedZero (m a file : M) :
    let left := F ones ![m,(a+a)+(a+a)]
    F PA194Stepper.stepper ![m,F pairCode ![modelNumeral M 11,
      F pairCode ![F halfCode (fun _ => left),F parityCode (fun _ => left)+file+file]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![a+a,
      F ones ![m,file]+F ones ![m,file]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hex := modelZeroOrSuccPred m
  change m = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => m)) = m at hex
  rcases hex with hm | hm
  · subst m
    dsimp only
    rw [modelOnesZero,modelOnesZero]
    change F PA194Stepper.stepper ![F (Code.zero 0) Fin.elim0,_] = _
    rw [PA194Stepper.modelStepperZero,(modelDouble (a+a)).1,(modelDouble (a+a)).2,zero_add]
  · let n := F predCode (fun _ => m)
    have hn : m=n+1 := by
      have ha : F Code.succ (fun _ => n) = n+1 := (modelAddOne n).symm
      exact hm.symm.trans ha
    rw [hn]
    dsimp only
    let w := F ones ![n,(a+a)+(a+a)]
    have hw : F ones ![n+1,(a+a)+(a+a)] = w+w+1 := by
      change F ones ![F addCode ![n,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    rw [hw,(modelOdd w).1,(modelOdd w).2]
    have hr : (1 : M)+file+file = file+file+1 := by simp only [add_assoc,add_comm]
    rw [hr]
    exact modelRollbackBoundary n (a+a) file
#print axioms rollbackSelectedZero
end models
end PA194ZeroSelectedRollback
