import PA194SixteenBoundary
import PA194SixteenExit
import PA194SixteenConnected
import PA194SixteenScanInvariant
import PA194StepperCompose
set_option autoImplicit false
namespace PA194SixteenExitComposition
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open BinaryTapeCodes ConfigurationStep PackedIterationModel PA194SixteenBoundary PA194SixteenExit PA194SixteenConnected
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
theorem modelEnterSeventeen (n m p l r : M) :
    let v := F ones ![p,l+l]
    let u := F zeros ![n,F zeros ![m,1+(r+r)+(r+r)]]
    let a := F ones ![p,1+(u+u)+(u+u)]
    F PA194Stepper.stepper ![((((((((((n+1)+(m+1))+1)+1)+m)+n)+1)+1)+p)+1)+1,
      F pairCode ![TableDispatch.modelNumeral M 12,
        F pairCode ![(v+v+1)+(v+v+1)+1,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 17,
      F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(a+a+1)+(a+a+1)+(a+a+1)+(a+a+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let v := F ones ![p,l+l]
  let u := F zeros ![n,F zeros ![m,1+(r+r)+(r+r)]]
  let a := F ones ![p,1+(u+u)+(u+u)]
  let t := (((((((n+1)+(m+1))+1)+1)+m)+n)+1)+1+p
  let initial := F pairCode ![TableDispatch.modelNumeral M 12,
    F pairCode ![(v+v+1)+(v+v+1)+1,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]
  have hs (w : M) : F PA194Stepper.stepper ![w+1,initial] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![w,initial]) := by
    change F PA194Stepper.stepper ![F addCode ![w,F oneCode Fin.elim0],initial] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have hentry := modelConnectedSixteen n m p (l+l) r
  dsimp only at hentry
  have hodd : F ones ![p+1,1+(u+u)+(u+u)] = a+a+1 := by
    change F ones ![F addCode ![p,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hodd] at hentry
  change F PA194Stepper.stepper ![(t+1)+1,initial] = _
  rw [hs,hs,hentry,modelPackedBoundary16,modelPackedExit16]
  change F pairCode ![TableDispatch.modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
    F parityCode (fun _ => l)+((a+a+1)+(a+a+1))+((a+a+1)+(a+a+1))]] =
    F pairCode ![TableDispatch.modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
    F parityCode (fun _ => l)+(a+a+1)+(a+a+1)+(a+a+1)+(a+a+1)]]
  simp only [add_assoc]
#print axioms modelEnterSeventeen
#print axioms modelPackedBoundary16
#print axioms modelPackedExit16
end models
end PA194SixteenExitComposition
