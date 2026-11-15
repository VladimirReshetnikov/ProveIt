import PA194LeftZeroWriteOne
import PA194RightRows
import PA194Stepper
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28BlankExit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194LeftZeroWriteOne PA194BinaryDouble PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem blankExit (l : M) :
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 3,F pairCode ![l,(0 : M)]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![l+l,(1 : M)+(1+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h3 := rightZero 3 0 4 (by decide) (by decide +kernel) l (0 : M)
  have h4 := rightZero 4 1 5 (by decide) (by decide +kernel) (l+l) (0 : M)
  have h5 := leftZeroWriteOne 5 7 (by decide) (by decide +kernel) ((l+l)+(l+l)+1) (0 : M)
  rw [(modelOdd (l+l)).1,(modelOdd (l+l)).2] at h5
  simp only [show modelNumeral M 0 = (0 : M) from rfl,show modelNumeral M 1 = (1 : M) from modelNumeralOne,add_zero,zero_add] at h3 h4 h5
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h3,h4,h5]
#print axioms blankExit
end models
end PA194Site28BlankExit
