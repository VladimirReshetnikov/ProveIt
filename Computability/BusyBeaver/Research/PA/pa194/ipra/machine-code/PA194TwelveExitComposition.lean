import PA194StateTwelveExit
import PA194TwelveScanInvariant
import PA194ZeroRuns
set_option autoImplicit false
namespace PA194TwelveExitComposition
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194BinaryDouble PA194StateTwelveExit PA194ZeroRuns PackedIterationModel ConfigurationStep PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelPackedTwelveExit (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 12,F pairCode ![l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 13,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 12,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 12,l,r+r+1],F nextL ![TableDispatch.modelNumeral M 12,l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 12,l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 12) l (r+r+1) at hm
  rw [←hm,modelStateTwelveOdd]

/-- Traverse the zero run and consume the following one. -/
theorem modelScanExit (n l r : M) :
    F PA194Stepper.stepper ![n+1,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,r+r+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 13,
      F pairCode ![F zeros ![n,l]+F zeros ![n,l],r]] := by
  have hstep : F PA194Stepper.stepper ![n+1,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,r+r+1]]]] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![n,F pairCode ![TableDispatch.modelNumeral M 12,
        F pairCode ![l,F zeros ![n,r+r+1]]]]) := by
    change F PA194Stepper.stepper ![F addCode ![n,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  rw [hstep,PA194TwelveScanInvariant.modelFullScan,modelPackedTwelveExit]
#print axioms modelScanExit
#print axioms modelPackedTwelveExit
end models
end PA194TwelveExitComposition
