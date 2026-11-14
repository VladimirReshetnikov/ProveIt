import PA194NineOdd
import PA194DecrementZeroCell
import PA194LeftRows
import PA194RightRows
import PA194RollbackCell
import PA194ReturnCell
import PA194ReturnFileMeaning
import PA194StepperCompose
import PA194ReturnedDecrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SelectedZeroTo12
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194NineOdd PA194DecrementZeroCell PA194LeftRows PA194RightRows PackedIterationModel ConfigurationStep
open PRAExhaustion PA194RollbackCell PA194BinaryDouble
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ReturnCell PA194ReturnFileMeaning PA194BinaryDouble
open PA194ReturnedDecrement PA194MarkedFile PA194CarryFile PA194ReturnFile
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem packedNineOdd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 9,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 9,l,r+r+1],F nextL ![modelNumeral M 9,l,r+r+1],
    F nextR ![modelNumeral M 9,l,r+r+1]) = stepSem (modelNumeral M 9) l (r+r+1) at hm
  rw [←hm,modelNineOdd]

/-- Fixed eight-step return from the selected-zero rollback boundary to state 12. -/
theorem boundaryTo12 (h p : M) :
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    let t0 := p+p+1
    let t1 := t0+t0
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let t5 := t4+t4
    let t6 := t5+t5
    F PA194Stepper.stepper ![modelNumeral M 8,
      F pairCode ![modelNumeral M 11,F pairCode ![a3+a3,p+p]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![xx+xx+1,t6]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2
  let t0 := p+p+1
  let t1 := t0+t0
  let t2 := t1+t1
  let t3 := t2+t2
  let t4 := t3+t3
  let t5 := t4+t4
  let t6 := t5+t5
  let t7 := t6+t6
  have h1 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 11,F pairCode ![a3+a3,p+p]]) =
      F pairCode ![modelNumeral M 8,F pairCode ![a3,t1]] := by
    rw [packedEleven,(modelDouble a3).1,(modelDouble a3).2,zero_add]
    dsimp [t1,t0]; simp only [add_assoc,add_comm,add_left_comm]
  have h2 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 8,F pairCode ![a3,t1]]) =
      F pairCode ![modelNumeral M 10,F pairCode ![a2,t2]] := by
    have hh := leftZero 8 10 (by decide) (by decide +kernel) (a2+a2) t0
    dsimp [a3,t1,t2] at *
    simpa only [(modelDouble a2).1,(modelDouble a2).2,zero_add] using hh
  have h3 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 10,F pairCode ![a2,t2]]) =
      F pairCode ![modelNumeral M 9,F pairCode ![a1,t3+1]] := by
    have hh := leftZero 10 9 (by decide) (by decide +kernel) a2 t1
    dsimp [a2,t2,t3] at *
    rw [(modelOdd a1).1,(modelOdd a1).2] at hh
    simpa only [add_assoc,add_comm,add_left_comm] using hh
  have h4 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![a1,t3+1]]) =
      F pairCode ![modelNumeral M 9,F pairCode ![a0,t4+1]] := by
    dsimp [a1,t3,t4]
    rw [packedNineOdd,(modelOdd a0).1,(modelOdd a0).2]
    simp only [add_assoc,add_comm,add_left_comm]
  have h5 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![a0,t4+1]]) =
      F pairCode ![modelNumeral M 9,F pairCode ![ll,t5+1]] := by
    dsimp [a0,t4,t5]
    rw [packedNineOdd,(modelOdd ll).1,(modelOdd ll).2]
    simp only [add_assoc,add_comm,add_left_comm]
  have h6 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![ll,t5+1]]) =
      F pairCode ![modelNumeral M 9,F pairCode ![xx+xx,t6+1]] := by
    dsimp [ll,t5,t6]
    rw [packedNineOdd,(modelOdd (xx+xx)).1,(modelOdd (xx+xx)).2]
    simp only [add_assoc,add_comm,add_left_comm]
  have h7 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![xx+xx,t6+1]]) =
      F pairCode ![modelNumeral M 9,F pairCode ![xx,t7]] := by
    dsimp [t6,t7]
    rw [packedNineOdd,(modelDouble xx).1,(modelDouble xx).2,zero_add]
  have h8 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![xx,t7]]) =
      F pairCode ![modelNumeral M 12,F pairCode ![xx+xx+1,t6]] := by
    have hh := rightZero 9 1 12 (by decide) (by decide +kernel) xx t6
    simpa only [modelNumeralOne,t7] using hh
  have stepNum (k : Nat) (c : M) : F PA194Stepper.stepper ![modelNumeral M (k+1),c] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![modelNumeral M k,c]) := by
    rw [modelNumeralSucc]
    change F PA194Stepper.stepper ![F addCode ![modelNumeral M k,F oneCode Fin.elim0],c] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  repeat rw [stepNum]
  have hz : modelNumeral M 0 = F (Code.zero 0) Fin.elim0 := rfl
  rw [hz,PA194Stepper.modelStepperZero,h1,h2,h3,h4,h5,h6,h7,h8]
#print axioms boundaryTo12
#print axioms packedNineOdd
end models
end PA194SelectedZeroTo12
