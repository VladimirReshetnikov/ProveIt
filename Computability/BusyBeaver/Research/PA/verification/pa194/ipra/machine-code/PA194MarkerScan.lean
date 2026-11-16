import Mathlib.Tactic.FinCases
import PA194GenericRightScan
set_option autoImplicit false
namespace PA194MarkerScan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero
open BinaryTapeCodes TableDispatch TableModelSemantics ConfigurationStep PackedRootModel PA194FiniteControls PA194StateOne PA194BinaryDouble PackedIterationModel PA194UnaryRuns

def markerControl (i : Fin 9) : Nat := ![113,93,68,114,95,71,106,85,60] i
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelMarkerOne (i : Fin 9) (l r : M) :
    (F nextQ ![modelNumeral M (markerControl i),l,r+r+1],F nextL ![modelNumeral M (markerControl i),l,r+r+1],
      F nextR ![modelNumeral M (markerControl i),l,r+r+1]) = (modelNumeral M (markerControl i),l+l+1,r) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hn : markerControl i < 194 := by fin_cases i <;> decide
  have hq : modelNumeral M (markerControl i) < modelNumeral M 194 := modelNumeralStrict _ _ hn
  have hactive : F ltBitCode ![modelNumeral M (markerControl i),modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelOdd r
  have ha : modelNumeral M (markerControl i) + modelNumeral M (markerControl i) + F parityCode (fun _ => r+r+1) = modelNumeral M (markerControl i+markerControl i+1) := by
    rw [hr.1, ←modelNumeralOne, ←modelNumeralAdd, ←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M (markerControl i+markerControl i+1)) = (1 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M (markerControl i+markerControl i+1)) = _
    rw [modelWriteNumeral]
    fin_cases i <;> exact modelNumeralOne
  have hd : lookupSem 0 directions (modelNumeral M (markerControl i+markerControl i+1)) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M (markerControl i+markerControl i+1)) = _
    rw [modelDirectionNumeral]
    fin_cases i <;> exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M (markerControl i+markerControl i+1)) = modelNumeral M (markerControl i) := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M (markerControl i+markerControl i+1)) = _
    rw [modelTargetNumeral]
    fin_cases i <;> rfl
  have hn := modelNext (![modelNumeral M (markerControl i),l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M (markerControl i),l,r+r+1],F nextL ![modelNumeral M (markerControl i),l,r+r+1],
    F nextR ![modelNumeral M (markerControl i),l,r+r+1]) = stepSem (modelNumeral M (markerControl i)) l (r+r+1) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2]
  have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  simp only [hone,ite_false]

theorem modelMarkerPacked (i : Fin 9) (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M (markerControl i),F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M (markerControl i),F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M (markerControl i),l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M (markerControl i),l,r+r+1],F nextL ![modelNumeral M (markerControl i),l,r+r+1],
    F nextR ![modelNumeral M (markerControl i),l,r+r+1]) = stepSem (modelNumeral M (markerControl i)) l (r+r+1) at hm
  rw [←hm,modelMarkerOne]

theorem modelMarkerScan (i : Fin 9) (n l r : M) :
    F PA194Stepper.stepper ![n,F pairCode ![modelNumeral M (markerControl i),F pairCode ![l,F ones ![n,r]]]] =
      F pairCode ![modelNumeral M (markerControl i),F pairCode ![F ones ![n,l],r]] :=
  PA194GenericRightScan.modelFullScan (markerControl i) (modelMarkerPacked i) n l r
#print axioms modelMarkerScan
end models
end PA194MarkerScan
