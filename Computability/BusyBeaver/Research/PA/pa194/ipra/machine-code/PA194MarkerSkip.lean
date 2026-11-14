import Mathlib.Tactic.FinCases
import PA194MarkerScan
import PA194StepperCompose
import PA194StateTwoOdd
set_option autoImplicit false
namespace PA194MarkerSkip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero
open BinaryTapeCodes TableDispatch TableModelSemantics ConfigurationStep PackedRootModel PA194FiniteControls PA194StateOne PA194BinaryDouble PackedIterationModel PA194UnaryRuns

open PA194MarkerScan
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelMarkerZero (i : Fin 8) (l r : M) :
    (F nextQ ![modelNumeral M (markerControl i.succ),l,r+r],F nextL ![modelNumeral M (markerControl i.succ),l,r+r],
      F nextR ![modelNumeral M (markerControl i.succ),l,r+r]) = (modelNumeral M (markerControl i.castSucc),l+l,r) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hn : markerControl i.succ < 194 := by fin_cases i <;> decide
  have hq : modelNumeral M (markerControl i.succ) < modelNumeral M 194 := modelNumeralStrict _ _ hn
  have hactive : F ltBitCode ![modelNumeral M (markerControl i.succ),modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M (markerControl i.succ) + modelNumeral M (markerControl i.succ) + F parityCode (fun _ => r+r) = modelNumeral M (markerControl i.succ+markerControl i.succ) := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M (markerControl i.succ+markerControl i.succ)) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M (markerControl i.succ+markerControl i.succ)) = _
    rw [modelWriteNumeral]
    fin_cases i <;> rfl
  have hd : lookupSem 0 directions (modelNumeral M (markerControl i.succ+markerControl i.succ)) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M (markerControl i.succ+markerControl i.succ)) = _
    rw [modelDirectionNumeral]
    fin_cases i <;> exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M (markerControl i.succ+markerControl i.succ)) = modelNumeral M (markerControl i.castSucc) := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M (markerControl i.succ+markerControl i.succ)) = _
    rw [modelTargetNumeral]
    fin_cases i <;> rfl
  have hn := modelNext (![modelNumeral M (markerControl i.succ),l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M (markerControl i.succ),l,r+r],F nextL ![modelNumeral M (markerControl i.succ),l,r+r],
    F nextR ![modelNumeral M (markerControl i.succ),l,r+r]) = stepSem (modelNumeral M (markerControl i.succ)) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  simp only [hone,ite_false,add_zero]


theorem modelMarkerPackedZero (i : Fin 8) (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M (markerControl i.succ),F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M (markerControl i.castSucc),F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M (markerControl i.succ),l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M (markerControl i.succ),l,r+r],F nextL ![modelNumeral M (markerControl i.succ),l,r+r],
    F nextR ![modelNumeral M (markerControl i.succ),l,r+r]) = stepSem (modelNumeral M (markerControl i.succ)) l (r+r) at hm
  rw [←hm,modelMarkerZero]

theorem modelMarkerSkipCell (i : Fin 8) (v l t : M) :
    let a := F ones ![v,t]
    F PA194Stepper.stepper ![(1 : M)+(v+1),F pairCode ![modelNumeral M (markerControl i.succ),
      F pairCode ![l,(a+a+1)+(a+a+1)]]] =
    F pairCode ![modelNumeral M (markerControl i.castSucc),F pairCode ![F ones ![v+1,l+l],t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let a := F ones ![v,t]
  let c := F pairCode ![modelNumeral M (markerControl i.succ),F pairCode ![l,(a+a+1)+(a+a+1)]]
  have h1 : F PA194Stepper.stepper ![(1 : M),c] =
      F pairCode ![modelNumeral M (markerControl i.castSucc),F pairCode ![l+l,a+a+1]] := by
    have hs : F PA194Stepper.stepper ![(0 : M)+1,c] = F PackedClock.encodedStep (fun _ => c) := by
      change F PA194Stepper.stepper ![F addCode ![(0 : M),F oneCode Fin.elim0],c] = _
      rw [modelAddOne,PA194Stepper.modelStepperSucc]
      have hz := PA194Stepper.modelStepperZero c
      change F PA194Stepper.stepper ![(0 : M),c] = c at hz
      rw [hz]
    rw [zero_add] at hs
    rw [hs]
    exact modelMarkerPackedZero i l (a+a+1)
  change F PA194Stepper.stepper ![F addCode ![(1 : M),v+1],c] = _
  rw [PA194StepperCompose.modelStepperCompose,h1]
  have ha : F ones ![v+1,t] = a+a+1 := by
    change F ones ![F addCode ![v,F oneCode Fin.elim0],t] = _
    rw [modelAddOne,modelOnesSucc]
  rw [←ha,modelMarkerScan]
#print axioms modelMarkerSkipCell
#print axioms modelMarkerZero
end models
end PA194MarkerSkip
