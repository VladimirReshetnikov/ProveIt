import PA194Site34To93
import PA194GenericRightScan
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34NinetyThree
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem loop (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![l,r+r+1]]) =
      F pairCode ![modelNumeral M 93,F pairCode ![l+l+1,r]] := by
  have h := rightOne 93 1 93 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne] using h

theorem threeRows (l p : M) :
    let a1 := l+l+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 93,
      F pairCode ![l,modelWord [true,true,false] p]]] =
      F pairCode ![modelNumeral M 113,F pairCode ![a3,p]] := by
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero]
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  rw [loop,loop]
  have h93 := rightZero 93 0 113 (by decide) (by decide +kernel) ((l+l+1)+(l+l+1)+1) p
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h93
#print axioms loop
#print axioms threeRows
end models
end PA194Site34NinetyThree
