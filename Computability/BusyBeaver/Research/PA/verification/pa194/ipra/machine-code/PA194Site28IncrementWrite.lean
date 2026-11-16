import PA194ScanInvariant
import PA194RightRows
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28IncrementWrite
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
theorem incrementWrite (n l tail : M) :
    F PA194Stepper.stepper ![n+1,F pairCode ![(1 : M),F pairCode ![l,F ones ![n,tail+tail]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![F ones ![n+1,l],tail]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := PA194ScanInvariant.modelFullScan n l (tail+tail)
  have hr := rightZero 1 1 3 (by decide) (by decide +kernel) (F ones ![n,l]) tail
  simp only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] at hr
  have ho : F ones ![n+1,l] = F ones ![n,l]+F ones ![n,l]+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],l] = _
    rw [modelAddOne,modelOnesSucc]
  change F PA194Stepper.stepper ![F addCode ![n,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,h,hr,ho]
#print axioms incrementWrite
end models
end PA194Site28IncrementWrite
