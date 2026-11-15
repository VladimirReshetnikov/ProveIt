import PA194Site28IncrementWrite
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28CarryCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194UnaryRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem carryCell (n l tail : M) :
    F PA194Stepper.stepper ![(1 : M)+(n+1),F pairCode ![modelNumeral M 3,
      F pairCode ![l,F ones ![n+1,tail+tail]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![F ones ![n+1,l+l],tail]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let r := F ones ![n,tail+tail]
  have ho : F ones ![n+1,tail+tail] = r+r+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h3 := rightOne 3 0 1 (by decide) (by decide +kernel) l r
  simp only [show modelNumeral M 0 = (0 : M) from rfl,show modelNumeral M 1 = (1 : M) from modelNumeralOne,add_zero] at h3
  have hi := PA194Site28IncrementWrite.incrementWrite (M := M) n (l+l) tail
  rw [ho]
  change F PA194Stepper.stepper ![F addCode ![(1 : M),n+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  have hone (x : M) : F PA194Stepper.stepper ![(1 : M),x] = F PackedClock.encodedStep (fun _ => x) := by
    rw [←modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),x] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
  rw [hone,h3,hi]
#print axioms carryCell
end models
end PA194Site28CarryCell
