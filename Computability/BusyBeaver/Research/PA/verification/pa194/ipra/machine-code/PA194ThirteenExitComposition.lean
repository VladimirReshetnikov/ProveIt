import PA194StateThirteenExit
import PA194TwelveThirteenCompose
import PA194ThirteenScanInvariant
import PA194StepperCompose
set_option autoImplicit false
namespace PA194ThirteenExitComposition
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing BinaryTapeCodes ConfigurationStep PackedIterationModel PA194StateThirteenExit PA194TwelveThirteenCompose PA194UnaryRuns PA194ZeroRuns

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelPackedThirteenExit (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 13,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 14,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 13,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 13,l,r+r],F nextL ![TableDispatch.modelNumeral M 13,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 13,l,r+r]) = stepSem (TableDispatch.modelNumeral M 13) l (r+r) at hm
  rw [←hm,modelStateThirteenEven]

/-- The connected two-scan segment takes one further step into state 14. -/
theorem modelTwoScansExit (n m l r : M) :
    F PA194Stepper.stepper ![((n+1)+m)+1,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,F ones ![m,r+r]+F ones ![m,r+r]+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 14,
      F pairCode ![F halfCode (fun _ => F zeros ![m,F zeros ![n,l]+F zeros ![n,l]]),
        F parityCode (fun _ => F zeros ![m,F zeros ![n,l]+F zeros ![n,l]])+(r+r)+(r+r)]] := by
  have hs : F PA194Stepper.stepper ![((n+1)+m)+1,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,F ones ![m,r+r]+F ones ![m,r+r]+1]]]] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![(n+1)+m,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,F ones ![m,r+r]+F ones ![m,r+r]+1]]]]) := by
    change F PA194Stepper.stepper ![F addCode ![(n+1)+m,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  rw [hs,modelTwoScans,modelPackedThirteenExit]
#print axioms modelPackedThirteenExit
#print axioms modelTwoScansExit
end models
end PA194ThirteenExitComposition
