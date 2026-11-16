import PA194SeedHeaderTo21
import PA194LeftOneWriteOne
import PA194HeaderController
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeedHeaderReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderTo21 PA194LeftRows PA194LeftOneWriteOne
open PA194BinaryDouble PA194ZeroRuns PA194HeaderController PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem left21 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 21,F pairCode ![(1 : M),x+x+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![(0 : M),(x+x+1)+(x+x+1)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 21 16 (by decide) (by decide +kernel) (1 : M) x
  have ho := modelOdd (0 : M)
  simp only [zero_add] at ho
  rw [ho.1,ho.2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem left16one (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![(0 : M),x+x+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![(0 : M),(x+x+1)+(x+x+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 16 16 (by decide) (by decide +kernel) (0 : M) x
  have hz := modelDouble (0 : M)
  simp only [zero_add] at hz
  rw [hz.1,hz.2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem leftZeroAtZero (q dest : Nat) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q) (0,0,194) = (0,0,dest)) (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![(0 : M),x+x]]) =
    F pairCode ![modelNumeral M dest,F pairCode ![(0 : M),(x+x)+(x+x)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero q dest hq hrow (0 : M) x
  have hz := modelDouble (0 : M)
  simp only [zero_add] at hz
  rw [hz.1,hz.2] at h
  simpa only [zero_add] using h

theorem fourTo18 (x : M) :
    let a := x+x+1
    let b := a+a+1
    let c := b+b
    let d := c+c
    F PA194Stepper.stepper ![modelNumeral M 4,
      F pairCode ![modelNumeral M 21,F pairCode ![(1 : M),a]]] =
    F pairCode ![modelNumeral M 18,F pairCode ![(0 : M),d+d]] := by
  dsimp only
  have h16 := leftZeroAtZero (M := M) 16 17 (by decide) (by decide +kernel)
  have h17 := leftZeroAtZero (M := M) 17 18 (by decide) (by decide +kernel)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 3),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [left21,left16one,h16,h17]

/-- From the seeded left-half value 1, state 21 returns unchanged to the
root control for any odd right half, even for nonstandard model tails. -/
theorem returnTo24 (x : M) :
    let a := x+x+1
    let c := ((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1
    F PA194Stepper.stepper ![modelNumeral M 4+c,
      F pairCode ![modelNumeral M 21,F pairCode ![(1 : M),a]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),a]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a := x+x+1
  let c := ((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1
  have h4 := fourTo18 x
  dsimp only at h4
  have h0 : F zeros ![modelNumeral M 6,(0 : M)] = (0 : M) := by
    have h := (zerosSix (M := M) (0 : M)).symm
    simpa only [zero_add] using h
  have h18 := headerHandoff (modelNumeral M 2) (0 : M) a
  dsimp only at h18
  simp only [h0,zerosTwo,zero_add,add_zero] at h18
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 4,c],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h4,h18]
#print axioms returnTo24
#print axioms fourTo18
end models
end PA194SeedHeaderReturn
