import PA194SixteenScanInvariant
import PA194SixteenBoundary
import PA194SixteenExit
import PA194UnaryRuns
set_option autoImplicit false
namespace PA194SixteenScanExit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194BinaryDouble PA194SixteenScanInvariant PA194SixteenBoundary PA194SixteenExit PA194UnaryRuns PackedIterationModel ConfigurationStep PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelPackedBoundary16 (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 16,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 16,l+l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 16,l+l,r+r+1],F nextL ![TableDispatch.modelNumeral M 16,l+l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 16,l+l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 16) (l+l) (r+r+1) at hm
  rw [←hm,modelSixteenOddEven]

theorem modelPackedExit16 (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 16,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 16,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 16,l,r+r],F nextL ![TableDispatch.modelNumeral M 16,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 16,l,r+r]) = stepSem (TableDispatch.modelNumeral M 16) l (r+r) at hm
  rw [←hm,modelSixteenEven]

/-- The connected state-16 scan crosses its zero boundary and enters state 17. -/
theorem modelScanBoundary (n l r : M) :
    F PA194Stepper.stepper ![n+1,F pairCode ![TableDispatch.modelNumeral M 16,
      F pairCode ![F ones ![n,l+l],r+r+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 16,
      F pairCode ![l,F ones ![n+1,r]+F ones ![n+1,r]]] := by
  have hstep : F PA194Stepper.stepper ![n+1,F pairCode ![TableDispatch.modelNumeral M 16,
      F pairCode ![F ones ![n,l+l],r+r+1]]] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![n,F pairCode ![TableDispatch.modelNumeral M 16,
        F pairCode ![F ones ![n,l+l],r+r+1]]]) := by
    change F PA194Stepper.stepper ![F addCode ![n,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have hscan := PA194SixteenScanInvariant.modelFullScan n (l+l) r
  have hodd : F ones ![n+1,r] = F ones ![n,r]+F ones ![n,r]+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],r] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hstep,hscan,hodd,modelPackedBoundary16,←hodd]

/-- One further transition leaves the scanner at control 7. -/
theorem modelScanExit (n l r : M) :
    F PA194Stepper.stepper ![(n+1)+1,F pairCode ![TableDispatch.modelNumeral M 16,
      F pairCode ![F ones ![n,l+l],r+r+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 17,
      F pairCode ![F halfCode (fun _ => l), F parityCode (fun _ => l) +
        (F ones ![n+1,r]+F ones ![n+1,r]) + (F ones ![n+1,r]+F ones ![n+1,r])]] := by
  have hstep : F PA194Stepper.stepper ![(n+1)+1,F pairCode ![TableDispatch.modelNumeral M 16,
      F pairCode ![F ones ![n,l+l],r+r+1]]] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![n+1,F pairCode ![TableDispatch.modelNumeral M 16,
        F pairCode ![F ones ![n,l+l],r+r+1]]]) := by
    change F PA194Stepper.stepper ![F addCode ![n+1,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  rw [hstep,modelScanBoundary,modelPackedExit16]


#print axioms modelScanExit
end models
end PA194SixteenScanExit
