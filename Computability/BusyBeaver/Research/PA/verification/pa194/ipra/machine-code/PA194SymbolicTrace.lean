import PA194SymbolicMove
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SymbolicTrace
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing PA194BidirectionalRow PA194Path27Header PA194SymbolicMove

structure Config where
  q : Nat
  left : List Bool
  right : List Bool
  deriving Repr, DecidableEq

/-- The tape lists are finite known prefixes, with arbitrary suffixes supplied in the semantics. -/
inductive Step : Config → Config → Prop
  | right (q next : Nat) (b w : Bool) (ls rs : List Bool)
      (hq : q < 194)
      (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,1,next)) :
      Step ⟨q,ls,b::rs⟩ ⟨next,w::ls,rs⟩
  | left (q next : Nat) (a b w : Bool) (ls rs : List Bool)
      (hq : q < 194)
      (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,0,next)) :
      Step ⟨q,a::ls,b::rs⟩ ⟨next,ls,a::w::rs⟩

inductive Run : Config → Config → Nat → Prop
  | nil (s : Config) : Run s s 0
  | cons (s mid fin : Config) (n : Nat) (first : Step s mid) (tail : Run mid fin n) : Run s fin (n+1)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def encode (s : Config) (x y : M) : M :=
  F pairCode ![modelNumeral M s.q,F pairCode ![modelWord s.left x,modelWord s.right y]]

theorem stepCorrect {s t : Config} (h : Step s t) (x y : M) :
    F PackedClock.encodedStep (fun _ => encode s x y) = encode t x y := by
  cases h with
  | right q next b w ls rs hq hrow => exact moveRight q next b w ls rs x y hq hrow
  | left q next a b w ls rs hq hrow => exact moveLeft q next a b w ls rs x y hq hrow

theorem runCorrect {s t : Config} {n : Nat} (h : Run s t n) (x y : M) :
    F PA194Stepper.stepper ![modelNumeral M n,encode s x y] = encode t x y := by
  induction h with
  | nil s =>
    change F PA194Stepper.stepper ![F (Code.zero 0) Fin.elim0,_] = _
    rw [PA194Stepper.modelStepperZero]
  | cons s mid fin n first tail ih =>
    have hstep : F PA194Stepper.stepper ![modelNumeral M 1,encode s x y] = encode mid x y := by
      change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
      rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
      exact stepCorrect first x y
    have hc : modelNumeral M (n+1) = F addCode ![modelNumeral M 1,modelNumeral M n] := by
      change modelNumeral M (n+1) = modelNumeral M 1+modelNumeral M n
      rw [←modelNumeralAdd,Nat.add_comm]
    rw [hc,PA194StepperCompose.modelStepperCompose,hstep,ih]
#print axioms stepCorrect
#print axioms runCorrect
end models
end PA194SymbolicTrace
