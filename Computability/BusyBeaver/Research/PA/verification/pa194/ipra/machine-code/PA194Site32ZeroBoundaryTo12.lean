import PA194LeftOneWriteZero
import PA194ZeroReturnTo12
import PA194LeftRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroBoundaryTo12
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RollbackCell PA194DecrementZeroCell PA194SeedHeaderTo21 PA194RightRows PA194LeftRows PA194BinaryDouble PA194UnaryRuns PA194StateOne BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem row10odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 10,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![l,(r+r)+(r+r)+1]] := by
  have h := leftZero 10 9 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem row9odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![l+l+1,r+r+1]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![l,(r+r)+(r+r)+1]] := by
  have h := PA194LeftOneWriteZero.leftOneWriteZero 9 9 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem row9even (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![l,(r+r)+(r+r)]] := by
  have h := PA194LeftOneWriteZero.leftOneWriteZero 9 9 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2,zero_add] at h
  exact h

theorem sevenTo12 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let p := w+w+1
    let r := (p+p)+(p+p)
    let r1 := r+r
    let r2 := r1+r1
    let r3 := r2+r2
    F PA194Stepper.stepper ![modelNumeral M 7,F pairCode ![modelNumeral M 11,
      F pairCode ![(a6+a6)+(a6+a6),w+w]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![a3+1,r3]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5+1
  let p := w+w+1
  let r := (p+p)+(p+p)
  let r1 := r+r
  let r2 := r1+r1
  have h11 := packedEleven ((a6+a6)+(a6+a6)) w
  rw [(modelDouble (a6+a6)).1,(modelDouble (a6+a6)).2,zero_add] at h11
  have h11' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 11,
    F pairCode ![(a6+a6)+(a6+a6),w+w]]) = F pairCode ![modelNumeral M 8,F pairCode ![a6+a6,p+p]] := by
    convert h11 using 1 <;> dsimp only [p] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h8 := rowEvenLeft (M := M) 8 10 (by decide) (by decide +kernel) a6 p
  have h10 := row10odd a5 (p+p)
  have h91 := row9odd a4 r
  have h92 := row9odd a3 r1
  have h93 := row9even a2 r2
  have h9exit := rightZero 9 1 12 (by decide) (by decide +kernel) a2 (r2+r2)
  simp only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] at h9exit
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 6),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 6 = F Code.succ (fun _ => modelNumeral M 5) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 5 = F Code.succ (fun _ => modelNumeral M 4) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,
    h11',h8,h10,h91,h92,h93,h9exit]
#print axioms row10odd
#print axioms row9odd
#print axioms row9even
#print axioms sevenTo12
end models
end PA194Site32ZeroBoundaryTo12
