import PA194RightRows
import PA194Path27Header
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194GenericRightTrace
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls TableDispatch PA194RightRows PA194Path27Header PRAModelIOpenPairing

/-- A finite, externally given certificate of right-moving literal rows. -/
inductive Trace : Nat → List Bool → List Nat → Nat → Prop
  | nil (q : Nat) : Trace q [] [] q
  | cons (q w next dest : Nat) (b : Bool) (bs : List Bool) (ws : List Nat)
      (hq : q < 194)
      (hrow : PA194Rows.rows.getD (q+q+(if b then 1 else 0)) (0,0,194) = (w,1,next))
      (tail : Trace next bs ws dest) : Trace q (b::bs) (w::ws) dest

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def pushWrites : List Nat → M → M
  | [], l => l
  | w::ws, l => pushWrites ws (l+l+modelNumeral M w)

theorem traceCorrect {q dest : Nat} {bs : List Bool} {ws : List Nat}
    (trace : Trace q bs ws dest) (l x : M) :
    F PA194Stepper.stepper ![modelNumeral M bs.length,
      F pairCode ![modelNumeral M q,F pairCode ![l,modelWord bs x]]] =
    F pairCode ![modelNumeral M dest,F pairCode ![pushWrites ws l,x]] := by
  induction trace generalizing l with
  | nil q =>
    change F PA194Stepper.stepper ![F (Code.zero 0) Fin.elim0,_] = _
    rw [PA194Stepper.modelStepperZero]
    rfl
  | cons q w next dest b bs ws hq hrow tail ih =>
    let y := modelWord bs x
    have hstep : F PA194Stepper.stepper ![modelNumeral M 1,
        F pairCode ![modelNumeral M q,F pairCode ![l,modelWord (b::bs) x]]] =
        F pairCode ![modelNumeral M next,F pairCode ![l+l+modelNumeral M w,y]] := by
      change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
      rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte,add_zero] at hrow
        change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![l,y+y]]) = _
        exact rightZero q w next hq hrow l y
      | true =>
        simp only [↓reduceIte] at hrow
        change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![l,y+y+1]]) = _
        exact rightOne q w next hq hrow l y
    have hc : modelNumeral M (b::bs).length = F addCode ![modelNumeral M 1,modelNumeral M bs.length] := by
      change modelNumeral M (bs.length+1) = modelNumeral M 1+modelNumeral M bs.length
      rw [←modelNumeralAdd, Nat.add_comm]
    rw [hc,PA194StepperCompose.modelStepperCompose,hstep]
    exact ih (l+l+modelNumeral M w)
#print axioms traceCorrect
end models
end PA194GenericRightTrace
