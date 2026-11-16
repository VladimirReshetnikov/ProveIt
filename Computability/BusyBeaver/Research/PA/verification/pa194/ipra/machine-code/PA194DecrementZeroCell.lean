import PA194ZeroFive
import PA194ZeroEight
import PA194ZeroEleven
import PA194IncrementTail
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194DecrementZeroCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194ZeroFive PA194ZeroEight PA194ZeroEleven PA194CarryEntry PA194IncrementTail PA194BinaryDouble PA194StateOne PackedIterationModel ConfigurationStep PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem packedFive (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 5,F pairCode ![l+l+1,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![l,(r+r)+(r+r)+(1+1)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 5,l+l+1,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 5,l+l+1,r+r+1],F nextL ![TableDispatch.modelNumeral M 5,l+l+1,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 5,l+l+1,r+r+1]) = stepSem (TableDispatch.modelNumeral M 5) (l+l+1) (r+r+1) at hm
  rw [←hm,modelZeroFive]
theorem packedEight (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 8,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 8,l,r+r+1],F nextL ![TableDispatch.modelNumeral M 8,l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 8,l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 8) (l) (r+r+1) at hm
  rw [←hm,modelZeroEight]
theorem packedEleven (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(1+1)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 11,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 11,l,r+r],F nextL ![TableDispatch.modelNumeral M 11,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 11,l,r+r]) = stepSem (TableDispatch.modelNumeral M 11) (l) (r+r) at hm
  rw [←hm,modelZeroEleven]
theorem modelZeroCell (l t : M) :
    let a := t+t+1
    let b := a+a
    let d := b+b
    let f := d+d
    F PA194Stepper.stepper ![TableDispatch.modelNumeral M 7,F pairCode ![(1 : M),F pairCode ![l,f]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(f+f)+(1+1)+(1+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let a := t+t+1
  let b := a+a
  let d := b+b
  let f := d+d
  let x := l+l+1
  let y := x+x
  let z := y+y+1
  have h1 : F PackedClock.encodedStep (fun _ => F pairCode ![(1 : M),F pairCode ![l,f]]) = F pairCode ![TableDispatch.modelNumeral M 3,F pairCode ![x,d]] := by
    have h := modelPackedCarryOne l d
    rw [modelNumeralOne] at h
    exact h
  have h2 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 3,F pairCode ![x,d]]) = F pairCode ![TableDispatch.modelNumeral M 4,F pairCode ![y,b]] := packedThree x b
  have h3 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 4,F pairCode ![y,b]]) = F pairCode ![TableDispatch.modelNumeral M 5,F pairCode ![z,a]] := packedFour y a
  have h4 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 5,F pairCode ![z,a]]) = F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![y,b+1]] := by
    have h := packedFive y t
    dsimp [a,b,z] at *
    simpa only [add_assoc,add_comm,add_left_comm] using h
  have h5 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![y,b+1]]) = F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![x,d]] := by
    rw [packedEight,(modelDouble x).1,(modelDouble x).2]
    simp only [zero_add,d,b]
  have h6 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![x,d]]) = F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![l,f+(1+1)+1]] := by
    rw [packedEleven,(modelOdd l).1,(modelOdd l).2]
    simp only [f,d]
    simp only [add_assoc,add_comm,add_left_comm]
  have h7 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![l,f+(1+1)+1]]) = F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(f+f)+(1+1)+(1+1)]] := by
    have hr : f+(1+1)+1 = (d+1)+(d+1)+1 := by simp only [f,add_assoc,add_comm,add_left_comm]
    rw [hr,packedEight]
    simp only [f,add_assoc,add_comm,add_left_comm]
  have stepNum (k : Nat) (c : M) : F PA194Stepper.stepper ![TableDispatch.modelNumeral M (k+1),c] = F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![TableDispatch.modelNumeral M k,c]) := by
    rw [PA194FiniteControls.modelNumeralSucc]
    change F PA194Stepper.stepper ![F addCode ![TableDispatch.modelNumeral M k,F oneCode Fin.elim0],c] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  dsimp only
  repeat rw [stepNum]
  have hz : TableDispatch.modelNumeral M 0 = F (Code.zero 0) Fin.elim0 := rfl
  rw [hz,PA194Stepper.modelStepperZero,h1,h2,h3,h4,h5,h6,h7]
#print axioms modelZeroCell
end models
end PA194DecrementZeroCell
