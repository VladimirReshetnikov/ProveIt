import PA194RightRows
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftZeroWriteOne
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194BidirectionalRow
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194StateOne PA194FiniteControls TableDispatch PA194RightRows PA194LeftRows PA194LeftOneRows PA194LeftZeroWriteOne PA194LeftOneWriteOne PRAModelIOpenPairing

def bit (b : Bool) : Nat := if b then 1 else 0
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def push (b : Bool) (x : M) : M := if b then x+x+1 else x+x
noncomputable def afterLeft (w : Bool) (l r : M) : M :=
  F parityCode (fun _ => l) + (if w then ((1 : M)+1) else 0) + (r+r)+(r+r)

theorem rowCorrect (q next : Nat) (b w right : Bool) (l r : M)
    (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,bit right,next)) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![l,push b r]]) =
      if right then F pairCode ![modelNumeral M next,F pairCode ![l+l+modelNumeral M (bit w),r]]
      else F pairCode ![modelNumeral M next,F pairCode ![F halfCode (fun _ => l),afterLeft w l r]] := by
  cases b <;> cases w <;> cases right <;>
    simp only [bit, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hrow ⊢
  · simpa [push,afterLeft] using leftZero q next hq hrow l r
  · simpa [push] using rightZero q 0 next hq hrow l r
  · simpa [push,afterLeft] using leftZeroWriteOne q next hq hrow l r
  · simpa [push] using rightZero q 1 next hq hrow l r
  · simpa [push,afterLeft] using leftOne q next hq hrow l r
  · simpa [push] using rightOne q 0 next hq hrow l r
  · simpa [push,afterLeft] using leftOneWriteOne q next hq hrow l r
  · simpa [push] using rightOne q 1 next hq hrow l r
#print axioms rowCorrect
end models
end PA194BidirectionalRow
