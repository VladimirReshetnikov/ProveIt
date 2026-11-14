import PA194FifteenBoundary
import PA194FifteenExit
import PA194FifteenExtended
import PA194ZeroScanInvariant
import PA194StepperCompose
set_option autoImplicit false
namespace PA194FifteenExitComposition
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing BinaryTapeCodes ConfigurationStep PackedIterationModel
open PA194FifteenBoundary PA194FifteenExit PA194FifteenExtended PA194UnaryRuns PA194ZeroRuns
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelPackedBoundary15 (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 15,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 15,F pairCode ![l,(r+r)+(r+r)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 15,l+l+1,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 15,l+l+1,r+r],F nextL ![TableDispatch.modelNumeral M 15,l+l+1,r+r],
    F nextR ![TableDispatch.modelNumeral M 15,l+l+1,r+r]) = stepSem (TableDispatch.modelNumeral M 15) (l+l+1) (r+r) at hm
  rw [←hm,modelFifteenOddLeft]

theorem modelPackedExit15 (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 15,F pairCode ![l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 16,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(1+1)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 15,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 15,l,r+r+1],F nextL ![TableDispatch.modelNumeral M 15,l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 15,l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 15) l (r+r+1) at hm
  rw [←hm,modelFifteenOdd]

/-- The connected run crosses the last left-hand one and enters state 16. -/
theorem modelEnterSixteen (n m l r : M) :
    let u := F zeros ![n,F zeros ![m,1+(r+r)+(r+r)]]
    F PA194Stepper.stepper ![(((((((n+1)+(m+1))+1)+1)+m)+n)+1)+1,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l+l+1,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 16,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(1+1)+(u+u+(u+u))+(u+u+(u+u))]] := by
  let initial := F pairCode ![TableDispatch.modelNumeral M 12,
    F pairCode ![l+l+1,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]
  let t := (((((n+1)+(m+1))+1)+1)+m)+n
  let u := F zeros ![n,F zeros ![m,1+(r+r)+(r+r)]]
  have hs (v : M) : F PA194Stepper.stepper ![v+1,initial] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![v,initial]) := by
    change F PA194Stepper.stepper ![F addCode ![v,F oneCode Fin.elim0],initial] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have hdone : F PA194Stepper.stepper ![t,initial] =
      F pairCode ![TableDispatch.modelNumeral M 15,F pairCode ![l+l+1,u+u]] :=
    modelExtendedReturn n m (l+l+1) r
  change F PA194Stepper.stepper ![(t+1)+1,initial] = _
  rw [hs,hs,hdone,modelPackedBoundary15]
  have hr : (u+u)+(u+u)+1 = ((u+u)+(u+u))+1 := rfl
  rw [hr,modelPackedExit15]
#print axioms modelEnterSixteen
#print axioms modelPackedBoundary15
#print axioms modelPackedExit15
end models
end PA194FifteenExitComposition
