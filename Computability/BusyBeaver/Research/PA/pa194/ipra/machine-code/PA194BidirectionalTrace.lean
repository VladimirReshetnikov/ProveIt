import PA194BidirectionalRow
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194BidirectionalTrace
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing PA194BidirectionalRow
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def nextLeft (right w : Bool) (l : M) : M :=
  if right then l+l+modelNumeral M (bit w) else F halfCode (fun _ => l)
noncomputable def nextRight (right w : Bool) (l r : M) : M :=
  if right then r else afterLeft w l r

/-- A finite sequence of checked literal rows, with explicit model-valued tape equations. -/
inductive Trace : Nat → M → M → Nat → M → M → Nat → Prop
  | nil (q : Nat) (l r : M) : Trace q l r q l r 0
  | cons (q next dest : Nat) (b w right : Bool) (l r finalL finalR : M) (n : Nat)
      (hq : q < 194)
      (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,bit right,next))
      (tail : Trace next (nextLeft right w l) (nextRight right w l r) dest finalL finalR n) :
      Trace q l (push b r) dest finalL finalR (n+1)

theorem traceCorrect {q dest n : Nat} {l r finalL finalR : M}
    (trace : Trace q l r dest finalL finalR n) :
    F PA194Stepper.stepper ![modelNumeral M n,F pairCode ![modelNumeral M q,F pairCode ![l,r]]] =
      F pairCode ![modelNumeral M dest,F pairCode ![finalL,finalR]] := by
  induction trace with
  | nil q l r =>
    change F PA194Stepper.stepper ![F (Code.zero 0) Fin.elim0,_] = _
    rw [PA194Stepper.modelStepperZero]
  | cons q next dest b w right l r finalL finalR n hq hrow tail ih =>
    have hrow' := PA194BidirectionalRow.rowCorrect q next b w right l r hq hrow
    have hstep : F PA194Stepper.stepper ![modelNumeral M 1,
        F pairCode ![modelNumeral M q,F pairCode ![l,push b r]]] =
        F pairCode ![modelNumeral M next,F pairCode ![nextLeft right w l,nextRight right w l r]] := by
      change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
      rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
      cases right <;> simpa [nextLeft,nextRight] using hrow'
    have hc : modelNumeral M (n+1) = F addCode ![modelNumeral M 1,modelNumeral M n] := by
      change modelNumeral M (n+1) = modelNumeral M 1+modelNumeral M n
      rw [←modelNumeralAdd,Nat.add_comm]
    rw [hc,PA194StepperCompose.modelStepperCompose,hstep,ih]
#print axioms traceCorrect
end models
end PA194BidirectionalTrace
