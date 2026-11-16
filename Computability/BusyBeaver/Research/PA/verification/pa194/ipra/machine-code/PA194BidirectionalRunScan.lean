import PA194SymbolicMove
import PA194GenericRightScan
import PA194ZeroRuns

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194BidirectionalRunScan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction
open PA194UnaryRuns PA194ZeroRuns PA194Stepper PackedDecoderModel TableDispatch BinaryTapeCodes
open PA194BidirectionalRow PA194SymbolicMove

/-- Prepend a run of the indicated bit to a packed tape half. -/
def runCode (bit : Bool) : Code 2 := if bit then ones else zeros

abbrev Tm := Semiterm language Nat 1
open PA194GenericRightScan (state app2 pack k total valApp2 valState)

def farTerm : Tm := .fvar 1
def nearTerm : Tm := .fvar 2
def app1 (f : Code 1) (a : Tm) : Tm := .func f ![a]
def frameTerm (right : Bool) (q : Nat) (far near : Tm) : Tm :=
  if right then pack q far near else
    pack q (app1 halfCode near) (app2 addCode (app1 parityCode near) (app2 addCode far far))

def beginTerm (right b : Bool) (q : Nat) : Tm :=
  frameTerm right q farTerm (app2 (runCode b) total nearTerm)

def endTerm (right b w : Bool) (q : Nat) : Tm :=
  frameTerm right q (app2 (runCode w) k farTerm) (app2 (runCode b) (app2 subCode total k) nearTerm)

def body (right b w : Bool) (q : Nat) : Semiformula language Nat 1 :=
  .or (.rel Language.ORing.Rel.lt ![total,k])
    (.rel Language.ORing.Rel.eq ![app2 stepper k (beginTerm right b q), endTerm right b w q])

theorem body_open (right b w : Bool) (q : Nat) : (body right b w q).Open := by
  simp [body,Semiformula.Open,Semiformula.qr]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def packed (q : Nat) (l r : M) : M :=
  F pairCode ![modelNumeral M q,F pairCode ![l,r]]

/-- The near half includes the head. For leftward scans, the ordinary packed
configuration stores the head bit in its right half, so move it back there. -/
noncomputable def frame (right : Bool) (q : Nat) (far near : M) : M :=
  if right then packed q far near else
    packed q (F halfCode (fun _ => near)) (F parityCode (fun _ => near) + (far+far))

@[simp] theorem runZero (b : Bool) (x : M) : F (runCode b) ![(0 : M),x] = x := by
  cases b
  · exact modelZerosZero x
  · exact modelOnesZero x

theorem runSucc (b : Bool) (n x : M) : F (runCode b) ![n+1,x] = push b (F (runCode b) ![n,x]) := by
  have hs : n+1 = F Code.succ (fun _ => n) := by
    change F addCode ![n,F oneCode Fin.elim0] = _
    exact modelAddOne n
  rw [hs]
  cases b
  · exact modelZerosSucc n x
  · exact modelOnesSucc n x

@[simp] theorem leftFrameBit (q : Nat) (b : Bool) (l r : M) :
    frame false q r (push b l) = packed q l (push b r) := by
  simp only [frame, Bool.false_eq_true, ↓reduceIte,halfPush,parityPush]
  rw [← rightWrite b]
  congr 1
  ac_rfl

theorem scanStep (right b w : Bool) (q : Nat) (far near : M)
    (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,bit right,q)) :
    F PackedClock.encodedStep (fun _ => frame right q far (push b near)) =
      frame right q (push w far) near := by
  cases right with
  | true =>
    have h := rowCorrect q q b w true far near hq hrow
    simpa only [frame, ↓reduceIte, packed, rightWrite] using h
  | false =>
    rw [leftFrameBit]
    have h := rowCorrect q q b w false near far hq hrow
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hw : afterLeft w near far = F parityCode (fun _ => near) + (push w far + push w far) := by
      cases w <;> simp only [afterLeft, push, Bool.false_eq_true, ↓reduceIte,add_zero] <;> abel
    rw [hw] at h
    simpa only [frame, packed, Bool.false_eq_true, ↓reduceIte] using h

theorem valApp1 (x : M) (e : Nat → M) (f : Code 1) (a : Tm) :
    Semiterm.val ![x] e (app1 f a) = F f (fun _ => Semiterm.val ![x] e a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

theorem valFrame (x : M) (e : Nat → M) (right : Bool) (q : Nat) (far near : Tm) :
    Semiterm.val ![x] e (frameTerm right q far near) =
      frame right q (Semiterm.val ![x] e far) (Semiterm.val ![x] e near) := by
  cases right <;> simp only [frameTerm,frame,PA194GenericRightScan.pack,packed,Bool.false_eq_true,↓reduceIte,valApp1,valApp2,valState]
  all_goals rfl

theorem body_eval (right b w : Bool) (q : Nat) (x : M) (e : Nat → M) :
    (body right b w q).Eval ![x] e ↔ e 0 < x ∨
      F stepper ![x,frame right q (e 1) (F (runCode b) ![e 0,e 2])] =
        frame right q (F (runCode w) ![x,e 1]) (F (runCode b) ![F subCode ![e 0,x],e 2]) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (body right b w q) ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : Tm) : (fun i => Semiterm.val ![x] e (![a,b] i)) =
      ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := val_pair ![x] e a b
  rw [hv]
  simp [k,total,farTerm,nearTerm,beginTerm,endTerm,valFrame,valApp2,Semiterm.val_bvar,Semiterm.val_fvar]
  rfl

/-- A certified self-loop transfers the scanned prefix of a model-length run
to the opposite half, possibly writing the opposite bit. -/
theorem partialScan (right b w : Bool) (q : Nat) (n time far near : M) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,bit right,q)) (ht : time ≤ n) :
    F stepper ![time,frame right q far (F (runCode b) ![n,near])] =
      frame right q (F (runCode w) ![time,far]) (F (runCode b) ![F subCode ![n,time],near]) := by
  let e : Nat → M := fun i => if i=0 then n else if i=1 then far else near
  have he0 : e 0 = n := by simp [e]
  have he1 : e 1 = far := by simp [e]
  have he2 : e 2 = near := by simp [e]
  have h (x : M) := body_eval right b w q x e
  simp only [he0,he1,he2] at h
  have full : (body right b w q).Eval ![time] e := by
    apply modelOpenInduction (M := M) (body right b w q) (body_open right b w q) e
    · apply (h (0 : M)).mpr
      right
      have hzero := modelStepperZero (M := M) (frame right q far (F (runCode b) ![n,near]))
      change F stepper ![(0 : M), _] = _ at hzero
      have hsub : F subCode ![n,(0 : M)] = n := PRASubtraction.modelSubZero n
      rw [hzero, runZero, hsub]
    · intro u hu
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      rw [hs]
      apply (h (u+1)).mpr
      by_cases hbound : n < u+1
      · exact Or.inl hbound
      · right
        have hle : u+1 ≤ n := le_of_not_gt hbound
        have hu_lt : u < n := lt_of_lt_of_le (lt_add_one u) hle
        have prev := ((h u).mp hu).resolve_left (not_lt_of_ge (le_of_lt hu_lt))
        have subeq : F subCode ![n,u] = F subCode ![n,u+1] + 1 := by
          rw [modelSubAsTsub,modelSubAsTsub]
          have hn : (u+1) + (n-(u+1)) = n := add_tsub_cancel_of_le hle
          calc
            n-u = ((u+1)+(n-(u+1)))-u := congrArg (fun z => z-u) hn.symm
            _ = (n-(u+1))+1 := by simp [add_assoc,add_comm]
        have hstep : F stepper ![u+1,frame right q far (F (runCode b) ![n,near])] =
            F PackedClock.encodedStep (fun _ => F stepper ![u,frame right q far (F (runCode b) ![n,near])]) := by
          rw [←hs,modelStepperSucc]
        rw [hstep,prev,subeq,runSucc,runSucc,scanStep _ _ _ _ _ _ hq hrow]
  exact ((h time).mp full).resolve_left (not_lt_of_ge ht)

/-- A certified self-loop moves across precisely `n` cells in every PRA model. -/
theorem fullScan (right b w : Bool) (q : Nat) (n far near : M) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+bit b) (0,0,194) = (bit w,bit right,q)) :
    F stepper ![n,frame right q far (F (runCode b) ![n,near])] =
      frame right q (F (runCode w) ![n,far]) near := by
  have h := partialScan right b w q n n far near hq hrow le_rfl
  have hsub : F subCode ![n,n] = (0 : M) := by rw [modelSubAsTsub]; simp
  simpa only [hsub,runZero] using h

#print axioms scanStep
#print axioms partialScan
#print axioms fullScan
end models
end PA194BidirectionalRunScan
