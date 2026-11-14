import PA194PositiveMarkerRoute
import PA194RightRows
import PA194ThresholdRows
import PA194MarkDelimiter
/-! All-model state-35 one-run classification and the five-one marker-return branch. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194PositiveThreshold
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194RightRows
open PA194ThresholdRows PA194MarkDelimiter PA194PositiveMarkerRoute PA194IncrementDispatch PA194MarkToHeader PA194OnesCommute PA194ReturnFile
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194MarkerScan PRAModelIOpenPairing TableDispatch PA194StateOne
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem row35 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 35,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 47,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 35 1 47 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne] using h

theorem row47 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 47,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 67,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 47 1 67 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne] using h

theorem row67one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 67,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 33,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 67 1 33 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne] using h

theorem row33one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 33,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 43,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 33 1 43 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne] using h

theorem row43one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 43,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [PackedIterationModel.modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := ConfigurationStep.modelNext (![modelNumeral M 43,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F ConfigurationStep.nextQ ![modelNumeral M 43,l,r+r+1],F ConfigurationStep.nextL ![modelNumeral M 43,l,r+r+1],
    F ConfigurationStep.nextR ![modelNumeral M 43,l,r+r+1]) = ConfigurationStep.stepSem (modelNumeral M 43) l (r+r+1) at hm
  rw [←hm,model43Odd]

theorem fiveThreshold (l r : M) :
    let t0 := r+r+1
    let t1 := t0+t0+1
    let t2 := t1+t1+1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let a0 := l+l+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let outR := ((r+r)+(r+r))+((r+r)+(r+r))+1
    F PA194Stepper.stepper ![modelNumeral M 6,F pairCode ![modelNumeral M 35,F pairCode ![l,t4]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![a1,outR]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 5),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 5 = F Code.succ (fun _ => modelNumeral M 4) from rfl,
      PA194Stepper.modelStepperSucc,
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
  rw [row35,row47,row67one,row33one,row43one]
  simp only [(modelOdd _).1,(modelOdd _).2]
  rw [show (1 : M)+(r+r)+(r+r) = (r+r)+(r+r)+1 by simp only [add_assoc,add_comm,add_left_comm]]
  rw [modelPackedWrite]
  simp only [(modelOdd _).1,(modelOdd _).2]
  simp only [add_assoc,add_comm,add_left_comm]
/-- Uniform threshold branch: if a state-35 one-run has at least five
ones, six steps mark its fifth/fourth cells and return to state 15. The
residual one-run length `n` may be nonstandard. -/
theorem modelRunAtLeastFive (n l w : M) :
    let r := F ones ![n,w]
    let a0 := l+l+1
    let a1 := a0+a0+1
    let outR := ((r+r)+(r+r))+((r+r)+(r+r))+1
    F PA194Stepper.stepper ![modelNumeral M 6,F pairCode ![modelNumeral M 35,
      F pairCode ![l,F ones ![((((n+1)+1)+1)+1)+1,w]]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![a1,outR]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have hs (x : M) : F ones ![x+1,w] = F ones ![x,w]+F ones ![x,w]+1 := by
    change F ones ![F addCode ![x,F oneCode Fin.elim0],w] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hs,hs,hs,hs,hs]
  exact fiveThreshold l (F ones ![n,w])
/-- Every model run length is either one of 0,…,4 or is five plus a
(possibly nonstandard) residual length. -/
theorem classifyLength (v : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    (∃ i : Fin 5, v = modelNumeral M i.val) ∨
      (∃ n : M, v = ((((n+1)+1)+1)+1)+1) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  by_cases hv : v < modelNumeral M 5
  · exact Or.inl (PA194FiniteControls.modelBelowNumeral 5 v hv)
  · right
    let n := v - modelNumeral M 5
    have hv' : modelNumeral M 5 ≤ v := le_of_not_gt hv
    have hn : modelNumeral M 5 + n = v := add_tsub_cancel_of_le hv'
    have hc : modelNumeral M 5 = ((((0 : M)+1)+1)+1)+1+1 := by
      rw [PA194FiniteControls.modelNumeralSucc,PA194FiniteControls.modelNumeralSucc,
        PA194FiniteControls.modelNumeralSucc,PA194FiniteControls.modelNumeralSucc,
        PA194FiniteControls.modelNumeralSucc]
      rfl
    refine ⟨n, ?_⟩
    rw [hc] at hn
    simpa only [zero_add,add_assoc,add_comm,add_left_comm] using hn.symm
/-- Zero scanned ones: the state and both tape halves are unchanged. -/
theorem shortTraverse0 (l r : M) :
    F PA194Stepper.stepper ![(0 : M),F pairCode ![modelNumeral M 35,F pairCode ![l,r]]] =
    F pairCode ![modelNumeral M 35,F pairCode ![l,r]] := PA194Stepper.modelStepperZero _

/-- Scan exactly 1 leading ones from state 35. -/
theorem shortTraverse1 (l r : M) :
    let t0 := r+r+1
    let a0 := l+l+1
    F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 35,F pairCode ![l,t0]]] =
    F pairCode ![modelNumeral M 47,F pairCode ![a0,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [row35]

/-- Scan exactly 2 leading ones from state 35. -/
theorem shortTraverse2 (l r : M) :
    let t0 := r+r+1
    let t1 := t0+t0+1
    let a0 := l+l+1
    let a1 := a0+a0+1
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 35,F pairCode ![l,t1]]] =
    F pairCode ![modelNumeral M 67,F pairCode ![a1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [row35,row47]

/-- Scan exactly 3 leading ones from state 35. -/
theorem shortTraverse3 (l r : M) :
    let t0 := r+r+1
    let t1 := t0+t0+1
    let t2 := t1+t1+1
    let a0 := l+l+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 35,F pairCode ![l,t2]]] =
    F pairCode ![modelNumeral M 33,F pairCode ![a2,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [row35,row47,row67one]

/-- Scan exactly 4 leading ones from state 35. -/
theorem shortTraverse4 (l r : M) :
    let t0 := r+r+1
    let t1 := t0+t0+1
    let t2 := t1+t1+1
    let t3 := t2+t2+1
    let a0 := l+l+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    F PA194Stepper.stepper ![modelNumeral M 4,F pairCode ![modelNumeral M 35,F pairCode ![l,t3]]] =
    F pairCode ![modelNumeral M 43,F pairCode ![a3,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
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
  rw [row35,row47,row67one,row33one]

#print axioms shortTraverse0
#print axioms shortTraverse1
#print axioms shortTraverse2
#print axioms shortTraverse3
#print axioms shortTraverse4

def shortControl (i : Fin 5) : Nat := ![35,47,67,33,43] i
def shortExit (i : Fin 5) : Nat := ![46,36,86,42,61] i
/-- If the remaining prefix run has length i < 5, these are the controls
reached on its following zero. The left and right halves are exact. -/
theorem shortBoundary (i : Fin 5) (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M (shortControl i),F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M (shortExit i),F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  fin_cases i

  · have h := rightZero 35 0 46 (by decide) (by decide +kernel) l r
    simpa [shortControl,shortExit,show modelNumeral M 0 = (0 : M) from rfl] using h
  · have h := rightZero 47 0 36 (by decide) (by decide +kernel) l r
    simpa [shortControl,shortExit,show modelNumeral M 0 = (0 : M) from rfl] using h
  · have h := rightZero 67 0 86 (by decide) (by decide +kernel) l r
    simpa [shortControl,shortExit,show modelNumeral M 0 = (0 : M) from rfl] using h
  · have h := rightZero 33 0 42 (by decide) (by decide +kernel) l r
    simpa [shortControl,shortExit,show modelNumeral M 0 = (0 : M) from rfl] using h
  · have h := rightZero 43 0 61 (by decide) (by decide +kernel) l r
    simpa [shortControl,shortExit,show modelNumeral M 0 = (0 : M) from rfl] using h
theorem onesThree (x : M) :
    let a := x+x+1
    let b := a+a+1
    F ones ![modelNumeral M 3,x] = b+b+1 := by
  dsimp only
  rw [show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]

/-- With the displayed even padding immediately to its left, the ≥5
threshold branch returns to the marker-exit controller state 17. -/
theorem thresholdReturn (x r : M) :
    let l := (x+x)+(x+x)+1
    let t0 := r+r+1
    let t1 := t0+t0+1
    let t2 := t1+t1+1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let a := F ones ![modelNumeral M 3,(1 : M)+((r+r)+(r+r))+((r+r)+(r+r))]
    let markClock := (modelNumeral M 3+1)+1
    F PA194Stepper.stepper ![modelNumeral M 6+markClock,
      F pairCode ![modelNumeral M 35,F pairCode ![l,t4]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x),F parityCode (fun _ => x)+(a+a)+(a+a)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let l := (x+x)+(x+x)+1
  let t := (r+r)+(r+r)
  have hf := fiveThreshold l r
  dsimp only at hf
  have hl : (l+l+1)+(l+l+1)+1 = F ones ![modelNumeral M 3,x+x] := by
    rw [onesThree]
  rw [hl] at hf
  have hm := PA194MarkerReturnCell.modelMarkerReturnCell ⟨0,by decide⟩ (modelNumeral M 3) x t
  dsimp only at hm
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 6,(modelNumeral M 3+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hf]
  exact hm
#print axioms thresholdReturn
#print axioms onesThree
#print axioms shortBoundary
#print axioms classifyLength
#print axioms modelRunAtLeastFive
#print axioms fiveThreshold
end models
end PA194PositiveThreshold
