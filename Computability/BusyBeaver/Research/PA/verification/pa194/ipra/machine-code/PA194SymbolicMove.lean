import PA194BidirectionalRow
import PA194Path27Header
import PA194BinaryDouble
import Mathlib.Tactic.Abel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SymbolicMove
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing PA194BidirectionalRow PA194Path27Header PA194BinaryDouble
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem wordPush (b : Bool) (bs : List Bool) (x : M) :
    modelWord (b::bs) x = push b (modelWord bs x) := by cases b <;> rfl

theorem halfPush (b : Bool) (x : M) : F halfCode (fun _ => push b x) = x := by
  cases b with
  | false => exact (modelDouble x).2
  | true => exact (modelOdd x).2

theorem parityPush (b : Bool) (x : M) : F parityCode (fun _ => push b x) = modelNumeral M (bit b) := by
  cases b with
  | false => exact (modelDouble x).1
  | true => simpa only [bit,push,↓reduceIte,modelNumeralOne] using (modelOdd x).1

theorem rightWrite (w : Bool) (x : M) : x+x+modelNumeral M (bit w) = push w x := by
  cases w <;> simp [bit,push,modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]

theorem leftWrite (a w : Bool) (l r : M) : afterLeft w (push a l) r = push a (push w r) := by
  simp only [afterLeft,parityPush]
  cases a <;> cases w <;> simp [bit,push,modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl] <;> abel

theorem moveRight (q next : Nat) (b w : Bool) (ls rs : List Bool) (x y : M)
    (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,1,next)) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![modelWord ls x,modelWord (b::rs) y]]) =
    F pairCode ![modelNumeral M next,F pairCode ![modelWord (w::ls) x,modelWord rs y]] := by
  rw [wordPush,wordPush]
  have h := PA194BidirectionalRow.rowCorrect q next b w true (modelWord ls x) (modelWord rs y) hq hrow
  simpa only [↓reduceIte,rightWrite] using h

theorem moveLeft (q next : Nat) (a b w : Bool) (ls rs : List Bool) (x y : M)
    (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,0,next)) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![modelWord (a::ls) x,modelWord (b::rs) y]]) =
    F pairCode ![modelNumeral M next,F pairCode ![modelWord ls x,modelWord (a::w::rs) y]] := by
  rw [wordPush,wordPush,wordPush,wordPush]
  have h := PA194BidirectionalRow.rowCorrect q next b w false (push a (modelWord ls x)) (modelWord rs y) hq hrow
  simpa only [Bool.false_eq_true,↓reduceIte,halfPush,leftWrite] using h
#print axioms wordPush
#print axioms halfPush
#print axioms parityPush
#print axioms rightWrite
#print axioms leftWrite
#print axioms moveRight
#print axioms moveLeft
end models
end PA194SymbolicMove
