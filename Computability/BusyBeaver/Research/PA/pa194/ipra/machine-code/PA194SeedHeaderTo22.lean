import PA194SeedHeaderReturn22
import PA194LeftRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeedHeaderTo22
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderTo17 PA194LeftRows PA194BinaryDouble
open PA194StateOne PRAModelIOpenPairing PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem rowEvenLeft (q dest : Nat) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q) (0,0,194) = (0,0,dest)) (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![l+l,r+r]]) =
    F pairCode ![modelNumeral M dest,F pairCode ![l,(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero q dest hq hrow (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add] using h

theorem row21OddLeft (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 21,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 22,F pairCode ![l,((r+r)+(r+r))+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 21 22 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

/-- Four model-uniform literal transitions, with arbitrary l and tail. -/
theorem fiveSteps (l w : M) :
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let w4 := w3+w3
    let w5 := w4+w4
    let w6 := w5+w5
    let w7 := w6+w6
    F PA194Stepper.stepper ![modelNumeral M 5,
      F pairCode ![modelNumeral M 17,F pairCode ![a4,w2]]] =
    F pairCode ![modelNumeral M 22,F pairCode ![l,w7+1]] := by
  dsimp only
  have h17 := rowEvenLeft (M := M) 17 18 (by decide) (by decide +kernel)
  have h18 := rowEvenLeft (M := M) 18 19 (by decide) (by decide +kernel)
  have h19 := rowEvenLeft (M := M) 19 20 (by decide) (by decide +kernel)
  have h20 := rowEvenLeft (M := M) 20 21 (by decide) (by decide +kernel)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 4),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [h17,h18,h19,h20,row21OddLeft]

#print axioms fiveSteps
end models
end PA194SeedHeaderTo22
