import PA194DecrementFour
import PA194IncrementTail
set_option autoImplicit false
namespace PA194DecrementPositiveCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194CarryEntry PA194IncrementTail PA194DecrementFour PA194BinaryDouble PA194StateOne PackedIterationModel ConfigurationStep PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem packedFourOdd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 4,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 4,l+l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 4,l+l,r+r+1],F nextL ![TableDispatch.modelNumeral M 4,l+l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 4,l+l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 4) (l+l) (r+r+1) at hm
  rw [←hm,modelDecrementFourOddEven]

theorem modelPositiveCell (l t : M) :
    let a := t+t+1
    let b := a+a
    F PA194Stepper.stepper ![TableDispatch.modelNumeral M 4,F pairCode ![(1 : M),F pairCode ![l,b+b]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,(b+b)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let a := t+t+1
  let b := a+a
  let x := l+l+1
  have h1 : F PackedClock.encodedStep (fun _ => F pairCode ![(1 : M),F pairCode ![l,b+b]]) =
      F pairCode ![TableDispatch.modelNumeral M 3,F pairCode ![x,b]] := by
    have h := modelPackedCarryOne l b
    rw [modelNumeralOne] at h
    exact h
  have h2 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 3,F pairCode ![x,b]]) =
      F pairCode ![TableDispatch.modelNumeral M 4,F pairCode ![x+x,a]] := by
    exact packedThree x a
  have h3 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 4,F pairCode ![x+x,a]]) =
      F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![x,b]] := by
    exact packedFourOdd x t
  have h4 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![x,b]]) =
      F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,(b+b)+1]] := by
    exact packedSix l a
  have stepNum (k : Nat) (c : M) : F PA194Stepper.stepper ![TableDispatch.modelNumeral M (k+1),c] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![TableDispatch.modelNumeral M k,c]) := by
    rw [PA194FiniteControls.modelNumeralSucc]
    change F PA194Stepper.stepper ![F addCode ![TableDispatch.modelNumeral M k,F oneCode Fin.elim0],c] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  dsimp only
  repeat rw [stepNum]
  have hz : TableDispatch.modelNumeral M 0 = F (Code.zero 0) Fin.elim0 := rfl
  rw [hz,PA194Stepper.modelStepperZero,h1,h2,h3,h4]
#print axioms modelPositiveCell
end models
end PA194DecrementPositiveCell
