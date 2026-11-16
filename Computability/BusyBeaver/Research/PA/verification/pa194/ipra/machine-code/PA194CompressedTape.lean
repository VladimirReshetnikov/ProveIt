import PA194BidirectionalRunScan
import PA194StepperCompose
import M6.Runtime

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedTape
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRAOpenInduction PRABooleanOps
open PA194StateOne PA194FiniteControls TableDispatch PA194BidirectionalRow
open PA194BidirectionalRunScan PA194SymbolicMove PA194Stepper PA194StepperCompose
open M6.Runtime

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def runLength (gap : M) (a c : Nat) : M :=
  modelNumeral M a * gap + modelNumeral M c

/-- Only final register boxes appear in the certified executor. Their packed
contents are supplied by the model of the register engine. -/
noncomputable def packSegments (gap : M) (box : BoxSt → M) : List Seg → M
  | [] => 0
  | .bit b :: bs => PA194BidirectionalRow.push b (packSegments gap box bs)
  | .run b a c :: bs => F (runCode b) ![runLength gap a c,packSegments gap box bs]
  | .box x :: _ => box x

noncomputable def encode (label : Nat → Nat) (gap : M) (box : BoxSt → M) : SConf → M
  | (q, false, l, r) => frame true (label q) (packSegments gap box l) (packSegments gap box r)
  | (q, true, l, r) => frame false (label q) (packSegments gap box r) (packSegments gap box l)

def Reach (x y : M) : Prop := ∃ n : M, F stepper ![n,x] = y
def Reach1 (x y : M) : Prop := ∃ n : M, (0 : M) < n ∧ F stepper ![n,x] = y

theorem ofEq {x y : M} (h : x = y) : Reach x y := by
  subst y
  exact ⟨0, modelStepperZero x⟩

theorem one {x y : M} (h : F PackedClock.encodedStep (fun _ => x) = y) : Reach1 x y := by
  refine ⟨1, _root_.zero_lt_one, ?_⟩
  change F stepper ![F oneCode Fin.elim0,x] = y
  rw [modelOneSuccZero, modelStepperSucc, modelStepperZero, h]

theorem trans {x y z : M} (h : Reach x y) (g : Reach y z) : Reach x z := by
  obtain ⟨s,hs⟩ := h
  obtain ⟨t,ht⟩ := g
  exact ⟨s+t, by change F stepper ![F addCode ![s,t],x] = z; rw [modelStepperCompose,hs,ht]⟩

theorem transPositive {x y z : M} (h : Reach x y) (g : Reach1 y z) : Reach1 x z := by
  obtain ⟨s,hs⟩ := h
  obtain ⟨t,ht,hz⟩ := g
  refine ⟨s+t,lt_of_lt_of_le ht ?_,?_⟩
  · rw [add_comm]
    exact le_self_add
  · change F stepper ![F addCode ![s,t],x] = z
    rw [modelStepperCompose,hs,hz]

theorem positiveTrans {x y z : M} (h : Reach1 x y) (g : Reach y z) : Reach1 x z := by
  obtain ⟨s,hs,hy⟩ := h
  obtain ⟨t,ht⟩ := g
  refine ⟨s+t,lt_of_lt_of_le hs le_self_add,?_⟩
  change F stepper ![F addCode ![s,t],x] = z
  rw [modelStepperCompose,hy,ht]

theorem reachable {x y : M} (h : Reach1 x y) : Reach x y := by
  obtain ⟨n,_,h⟩ := h
  exact ⟨n,h⟩

theorem lengthSucc (gap : M) (a c : Nat) :
    runLength gap a (c+1) = runLength gap a c + 1 := by
  rw [runLength, runLength, ← modelNumeralOne (M := M), modelNumeralAdd, add_assoc]

theorem lengthZero (gap : M) : runLength gap 0 0 = 0 := by
  unfold runLength
  change (0 : M)*gap+0 = 0
  simp

theorem peelRun (gap : M) (box : BoxSt → M) (b : Bool) (a c : Nat) (xs : List Seg) :
    packSegments gap box (.run b a (c+1) :: xs) =
      packSegments gap box (.bit b :: .run b a c :: xs) := by
  simp only [packSegments, lengthSucc, runSucc]

theorem removeEmptyRun (gap : M) (box : BoxSt → M) (b : Bool) (xs : List Seg) :
    packSegments gap box (.run b 0 0 :: xs) = packSegments gap box xs := by
  simp only [packSegments,lengthZero,runZero]

theorem turnRight (q : Nat) (b : Bool) (l r : M) :
    frame false q r (PA194BidirectionalRow.push b l) =
      frame true q l (PA194BidirectionalRow.push b r) :=
  leftFrameBit q b l r

theorem turnBlank (q : Nat) (r : M) :
    frame false q r 0 = frame true q 0 (PA194BidirectionalRow.push false r) := by
  have hz : PA194BidirectionalRow.push false (0 : M) = (0 : M) := by
    simp [PA194BidirectionalRow.push]
  simpa only [hz] using turnRight q false (0 : M) r

theorem rightRow (q q' : Nat) (b w : Bool) (l r : M) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,1,q')) :
    Reach1 (frame true q l (PA194BidirectionalRow.push b r))
      (frame true q' (PA194BidirectionalRow.push w l) r) := by
  apply one
  have h := rowCorrect q q' b w true l r hq hrow
  simpa only [frame,packed,↓reduceIte,rightWrite] using h

theorem leftRow (q q' : Nat) (b w : Bool) (l r : M) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,0,q')) :
    Reach1 (frame true q l (PA194BidirectionalRow.push b r))
      (frame false q' (PA194BidirectionalRow.push w r) l) := by
  apply one
  have h := rowCorrect q q' b w false l r hq hrow
  have hw : afterLeft w l r = F BinaryTapeCodes.parityCode (fun _ => l) +
      (PA194BidirectionalRow.push w r + PA194BidirectionalRow.push w r) := by
    cases w <;> simp only [afterLeft, PA194BidirectionalRow.push, Bool.false_eq_true, ↓reduceIte,add_zero] <;> abel
  simpa only [frame,packed,Bool.false_eq_true,↓reduceIte,hw] using h

#print axioms transPositive
#print axioms peelRun
#print axioms removeEmptyRun
#print axioms rightRow
#print axioms leftRow

end models
end PA194CompressedTape
