import PA194LeftRows
import PA194RightRows
import PA194Stepper
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194State61To2
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194LeftRows PA194RightRows PA194BinaryDouble PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem rowLeftEven (q d : Nat) (hq : q < 194)
    (hr : PA194Rows.rows.getD (q+q) (0,0,194) = (0,0,d)) (a b : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![a+a,b+b]]) =
    F pairCode ![modelNumeral M d,F pairCode ![a,(b+b)+(b+b)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero q d hq hr (a+a) b
  rw [(modelDouble a).1,(modelDouble a).2,zero_add] at h
  exact h
theorem rowLeftOdd (q d : Nat) (hq : q < 194)
    (hr : PA194Rows.rows.getD (q+q) (0,0,194) = (0,0,d)) (a b : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![a+a+1,b+b]]) =
    F pairCode ![modelNumeral M d,F pairCode ![a,1+(b+b)+(b+b)]] := by
  have h := leftZero q d hq hr (a+a+1) b
  rw [(modelOdd a).1,(modelOdd a).2] at h
  exact h
theorem rowRightZero (q d : Nat) (hq : q < 194)
    (hr : PA194Rows.rows.getD (q+q) (0,0,194) = (0,1,d)) (a b : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![a,b+b]]) =
    F pairCode ![modelNumeral M d,F pairCode ![a+a,b]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero q 0 d hq hr a b
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem state61To2 (l x : M) :
    let a := l+l+1
    let b := x+x+1
    F PA194Stepper.stepper ![modelNumeral M 10,
      F pairCode ![modelNumeral M 61,F pairCode ![a+a,b+b]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![((a+a)+(a+a))+((a+a)+(a+a)),x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a := l+l+1
  let b := x+x+1
  let c := b+b
  let d := c+c
  have hone : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 65,F pairCode ![l,(d+d)+1]]) =
      F pairCode ![modelNumeral M 49,F pairCode ![a,d]] := by
    have h := rightOne 65 1 49 (by decide) (by decide +kernel) l d
    simpa only [PA194StateOne.modelNumeralOne] using h
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 9),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 9 = F Code.succ (fun _ => modelNumeral M 8) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 8 = F Code.succ (fun _ => modelNumeral M 7) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 7 = F Code.succ (fun _ => modelNumeral M 6) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 6 = F Code.succ (fun _ => modelNumeral M 5) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 5 = F Code.succ (fun _ => modelNumeral M 4) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
  rw [rowLeftEven 61 76 (by decide) (by decide +kernel) a b,
      rowRightZero 76 87 (by decide) (by decide +kernel) a c,
      rowLeftEven 87 46 (by decide) (by decide +kernel) a b,
      rowLeftOdd 46 65 (by decide) (by decide +kernel) l c]
  rw [show (1 : M)+(c+c)+(c+c) = d+d+1 by dsimp [d]; simp only [add_assoc,add_comm,add_left_comm],hone,
      rowRightZero 49 69 (by decide) (by decide +kernel) a c,
      rowLeftEven 69 94 (by decide) (by decide +kernel) a b,
      rowRightZero 94 50 (by decide) (by decide +kernel) a c,
      rowRightZero 50 70 (by decide) (by decide +kernel) (a+a) b]
  have h70 := rightOne 70 0 2 (by decide) (by decide +kernel) ((a+a)+(a+a)) x
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at h70
  exact h70
#print axioms state61To2
end models
end PA194State61To2
