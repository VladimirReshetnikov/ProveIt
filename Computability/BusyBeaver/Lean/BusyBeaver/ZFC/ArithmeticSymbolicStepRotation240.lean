import BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240
import BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240
import BusyBeaver.ZFC.ArithmeticMachineScansRotation240

set_option autoImplicit false

/-!
Arithmetic checked-step mirror of the actual Rotation240 finite symbolic syntax.
Literal transitions and affine scans are proved for arbitrary IΣ1 model values.
The concrete nine-primary box interpretation has 167 plus extra one-valued
spares. Only four explicit numeric box endpoint fields remain conditional.
Positive decrement retains the actual additional left bit. Only literal steps
set moved=true; no scan/box or syntax normalization fabricates progress.

This ports the checked ArithmeticSymbolicExecutionPerm252 proof structure to
actual SymbolicRotation240, using its exact fast-table equality and current
arithmetic run. No internal-variable symbolic syntax/fuel graph, first-exit,
full dispatch simulation or PA endpoint is asserted. Mira-Cult, Jeff Ketchersid,
Andrew James Wade and ProveIt retain their machine/framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor
open ArithmeticMachineGraphPerm252 (lookupNat actionNumber)
open ArithmeticMachineGraphRotation240 ArithmeticMachineStepRotation240
open ArithmeticMachineRunFromRotation240 ArithmeticMachineUniformScansPerm252
open ArithmeticMachineScansRotation240
open ArithmeticSymbolicTapeRotation240
open ArithmeticSymbolicTapePerm252 (affine)
open ArithmeticSymbolicBoxesRotation240 (boxPrefix ValidValues boxPrefix_even)
open SymbolicRotation240 (Branch Reg Box Effect Segment SConfig)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Numeric state codes are those of the exact Rotation240 table. -/
noncomputable def stateValue (q : Option (Fin 240)) : V :=
  (ArithmeticMachinePerm252.stateCode q : Nat)

noncomputable def tapeValue (values : List V) (extra gap : V) (xs : List Segment) : V :=
  tapePrefix gap (boxPrefix values extra) xs 0
noncomputable def value (values : List V) (extra gap : V) (s : SConfig) : V :=
  configValue gap (boxPrefix values extra) s

@[simp] lemma tape_nil (values : List V) (extra gap : V) :
    tapeValue values extra gap [] = 0 := rfl
@[simp] lemma tape_bit (values : List V) (extra gap : V) (b : Bool) (xs : List Segment) :
    tapeValue values extra gap (.bit b::xs) = 2*tapeValue values extra gap xs+digit b := rfl
@[simp] lemma tape_run (values : List V) (extra gap : V) (b : Bool) (a c : Nat)
    (xs : List Segment) :
    tapeValue values extra gap (.run b a c::xs) =
      bitPrefix b (affine gap a c) (tapeValue values extra gap xs) := rfl
@[simp] lemma tape_box (values : List V) (extra gap : V) (x : Box) (xs : List Segment) :
    tapeValue values extra gap (.box x::xs) = boxPrefix values extra x (tapeValue values extra gap xs) := rfl
@[simp] lemma value_right (values : List V) (extra gap : V)
    (q : Option (Fin 240)) (l r : List Segment) :
    value values extra gap ⟨q,false,l,r⟩ =
      frame (stateValue q) (tapeValue values extra gap l) (tapeValue values extra gap r) := rfl
@[simp] lemma value_left (values : List V) (extra gap : V)
    (q : Option (Fin 240)) (l r : List Segment) :
    value values extra gap ⟨q,true,l,r⟩ =
      leftFrame (stateValue q) (tapeValue values extra gap l) (tapeValue values extra gap r) := rfl

lemma affine_succ (gap : V) (a c : Nat) :
    affine gap a (c+1) = affine gap a c+1 := by
  simp only [affine,Nat.cast_add]
  ring
lemma leftFrame_digit (state left right : V) (b : Bool) :
    leftFrame state (2*left+digit b) right = frame state left (2*right+digit b) := by
  unfold leftFrame
  rw [digit_div_two,digit_mod_two]
  congr 1
  ring

/-- A typed actual native transition lifts to the arithmetic lookup in every
model. A halt successor still has a positive action retaining write and move. -/
lemma right_row_of_transition (q : Fin 240) (next : Option (Fin 240)) (read write : Bool)
    (ht : machineRotation240.transition q read = ⟨write,.right,next⟩) :
    actionLookup (stateValue (V := V) (some q)) (digit read) =
      4*stateValue next+3+digit write := by
  have h := literal_lookup_actual q read
  rw [ht] at h
  have hn : lookupNat literalRows 0 (q.val+1) read.toNat =
      4*ArithmeticMachinePerm252.stateCode next+3+write.toNat := by
    calc
      _ = actionNumber ⟨write,.right,next⟩ := h
      _ = _ := by dsimp [actionNumber]; omega
  simpa only [stateValue,ArithmeticMachinePerm252.stateCode] using
    right_transition_of_nat (V := V) read write (q.val+1)
      (ArithmeticMachinePerm252.stateCode next) hn

lemma left_row_of_transition (q : Fin 240) (next : Option (Fin 240)) (read write : Bool)
    (ht : machineRotation240.transition q read = ⟨write,.left,next⟩) :
    actionLookup (stateValue (V := V) (some q)) (digit read) =
      4*stateValue next+1+digit write := by
  have h := literal_lookup_actual q read
  rw [ht] at h
  have hn : lookupNat literalRows 0 (q.val+1) read.toNat =
      4*ArithmeticMachinePerm252.stateCode next+1+write.toNat := by
    calc
      _ = actionNumber ⟨write,.left,next⟩ := h
      _ = _ := by dsimp [actionNumber]; omega
  simpa only [stateValue,ArithmeticMachinePerm252.stateCode] using
    left_transition_of_nat (V := V) read write (q.val+1)
      (ArithmeticMachinePerm252.stateCode next) hn

/-- The same original values/extra interpret both source and target effects. -/
def StepSound (br : Branch) (s t : SConfig) (moved : Bool) : Prop :=
  ∀ (values : List V), ValidValues br values → ∀ extra gap : V,
    ∃ time : V, runFrom time (value values extra gap s) = value values extra gap t ∧
      (moved = true → 0 < time)

/-- One literal transition supplies a positive internal clock. -/
theorem literal_right (br : Branch) (q : Fin 240) (next : Option (Fin 240))
    (read written : Bool) (l r : List Segment)
    (ht : machineRotation240.transition q read = ⟨written,.right,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,.bit read::r⟩
      ⟨next,false,.bit written::l,r⟩ true := by
  intro values _ extra gap
  refine ⟨1,?_,by intro _; simp⟩
  simpa only [runFrom_one,value_right,tape_bit] using
    step_right_row read written (stateValue (some q)) (stateValue next)
      (right_row_of_transition q next read written ht)
      (tapeValue values extra gap l) (tapeValue values extra gap r)

theorem literal_left (br : Branch) (q : Fin 240) (next : Option (Fin 240))
    (read written : Bool) (l r : List Segment)
    (ht : machineRotation240.transition q read = ⟨written,.left,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,.bit read::r⟩
      ⟨next,true,l,.bit written::r⟩ true := by
  intro values _ extra gap
  refine ⟨1,?_,by intro _; simp⟩
  simpa only [runFrom_one,value_right,value_left,tape_bit] using
    step_left_row read written (stateValue (some q)) (stateValue next)
      (left_row_of_transition q next read written ht)
      (tapeValue values extra gap l) (tapeValue values extra gap r)

theorem left_empty (br : Branch) (q : Option (Fin 240)) (r : List Segment) :
    StepSound (V := V) br ⟨q,true,[],r⟩ ⟨q,false,[],.bit false::r⟩ false := by
  intro values _ extra gap
  refine ⟨0,?_,by simp⟩
  simp [leftFrame,digit]

theorem left_bit (br : Branch) (q : Option (Fin 240)) (b : Bool) (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.bit b::l,r⟩ ⟨q,false,l,.bit b::r⟩ false := by
  intro values _ extra gap
  refine ⟨0,?_,by simp⟩
  simp only [runFrom_zero,value_left,value_right,tape_bit,leftFrame_digit]

theorem peel_right (br : Branch) (q : Option (Fin 240)) (b : Bool) (a c : Nat)
    (l r : List Segment) :
    StepSound (V := V) br ⟨q,false,l,.run b a (c+1)::r⟩
      ⟨q,false,l,.bit b::.run b a c::r⟩ false := by
  intro values _ extra gap
  refine ⟨0,?_,by simp⟩
  simp only [runFrom_zero,value_right,tape_run,tape_bit,affine_succ,bitPrefix_succ]

theorem peel_left (br : Branch) (q : Option (Fin 240)) (b : Bool) (a c : Nat)
    (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.run b a (c+1)::l,r⟩
      ⟨q,true,.bit b::.run b a c::l,r⟩ false := by
  intro values _ extra gap
  refine ⟨0,?_,by simp⟩
  simp only [runFrom_zero,value_left,tape_run,tape_bit,affine_succ,bitPrefix_succ]

theorem empty_run_right (br : Branch) (q : Option (Fin 240)) (b : Bool)
    (l r : List Segment) :
    StepSound (V := V) br ⟨q,false,l,.run b 0 0::r⟩ ⟨q,false,l,r⟩ false := by
  intro values _ extra gap
  refine ⟨0,?_,by simp⟩
  simp [affine]

theorem empty_run_left (br : Branch) (q : Option (Fin 240)) (b : Bool)
    (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.run b 0 0::l,r⟩ ⟨q,true,l,r⟩ false := by
  intro values _ extra gap
  refine ⟨0,?_,by simp⟩
  simp [affine]

/-- A writing scan uses the whole affine internal length but does not mark progress. -/
theorem scan_right (br : Branch) (q : Fin 240) (read written : Bool) (a c : Nat)
    (l r : List Segment)
    (ht : machineRotation240.transition q read = ⟨written,.right,some q⟩) :
    StepSound (V := V) br ⟨some q,false,l,.run read a c::r⟩
      ⟨some q,false,.run written a c::l,r⟩ false := by
  intro values _ extra gap
  refine ⟨affine gap a c,?_,by simp⟩
  simpa only [value_right,tape_run] using
    ArithmeticMachineScansRotation240.scan_right read written (stateValue (some q))
      (right_row_of_transition q (some q) read written ht) (affine gap a c)
      (tapeValue values extra gap l) (tapeValue values extra gap r)

theorem scan_left (br : Branch) (q : Fin 240) (read written : Bool) (a c : Nat)
    (l r : List Segment)
    (ht : machineRotation240.transition q read = ⟨written,.left,some q⟩) :
    StepSound (V := V) br ⟨some q,true,.run read a c::l,r⟩
      ⟨some q,true,l,.run written a c::r⟩ false := by
  intro values _ extra gap
  refine ⟨affine gap a c,?_,by simp⟩
  simpa only [value_left,tape_run] using
    ArithmeticMachineScansRotation240.scan_left read written (stateValue (some q))
      (left_row_of_transition q (some q) read written ht) (affine gap a c)
      (tapeValue values extra gap l) (tapeValue values extra gap r)

/-- The only remaining dynamic premises are the four whole-file box endpoints.
Each field uses the concrete nine-primary interpretation and the same internal
extra-spare parameter. No symbolic-step or executor soundness premise occurs. -/
structure BoxRuntime : Prop where
  mark : ∀ (br : Branch) (values : List V), ValidValues br values →
    ∀ (r : Reg) (extra left : V), ∃ time : V,
      runFrom time (frame (stateValue (some (RegisterMarkRotation240.skip r.val))) left
        (boxPrefix values extra (.plain .unchanged) 0)) =
      leftFrame (stateValue (some (SymbolicRotation240.markExit r))) left
        (boxPrefix values extra (.marked r) 0)
  increment : ∀ (br : Branch) (values : List V), ValidValues br values →
    ∀ (r : Reg) (extra left : V), ∃ time : V,
      runFrom time (frame (stateValue (some Rotation240Boxes.seek)) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (stateValue (some Rotation240Boxes.returnZero)) left
        (boxPrefix values extra (.plain (.increment r)) 0)
  zero_decrement : ∀ (values : List V) (r : Reg), ValidValues (some (r,true)) values →
    ∀ (extra left : V), ∃ time : V,
      runFrom time (frame (stateValue (some Rotation240Boxes.carry)) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (stateValue (some Rotation240Boxes.rollback)) left
        (boxPrefix values extra (.plain .unchanged) 0)
  positive_decrement : ∀ (values : List V) (r : Reg), ValidValues (some (r,false)) values →
    ∀ (extra left : V), ∃ time : V,
      runFrom time (frame (stateValue (some Rotation240Boxes.carry)) left
        (boxPrefix values extra (.marked r) 0)) =
      leftFrame (stateValue (some Rotation240Boxes.returnZero)) (2*left+1)
        (boxPrefix values extra (.plain (.decrement r)) 0)

/-- The actual nine-selector mark macro, conditional only on its numeric endpoint. -/
theorem box_mark (runtime : BoxRuntime (V := V)) (br : Branch) (r : Reg) (l : List Segment) :
    StepSound (V := V) br
      ⟨some (RegisterMarkRotation240.skip r.val),false,l,[.box (.plain .unchanged)]⟩
      ⟨some (SymbolicRotation240.markExit r),true,l,[.box (.marked r)]⟩ false := by
  intro values hv extra gap
  obtain ⟨time,ht⟩ := runtime.mark br values hv r extra (tapeValue values extra gap l)
  exact ⟨time,by simpa only [value_right,value_left,tape_box,tape_nil] using ht,by simp⟩

theorem box_increment (runtime : BoxRuntime (V := V)) (br : Branch) (r : Reg) (l : List Segment) :
    StepSound (V := V) br
      ⟨some Rotation240Boxes.seek,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.returnZero,true,l,[.box (.plain (.increment r))]⟩ false := by
  intro values hv extra gap
  obtain ⟨time,ht⟩ := runtime.increment br values hv r extra (tapeValue values extra gap l)
  exact ⟨time,by simpa only [value_right,value_left,tape_box,tape_nil] using ht,by simp⟩

theorem box_zero_decrement (runtime : BoxRuntime (V := V)) (r : Reg) (l : List Segment) :
    StepSound (V := V) (some (r,true))
      ⟨some Rotation240Boxes.carry,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.rollback,true,l,[.box (.plain .unchanged)]⟩ false := by
  intro values hv extra gap
  obtain ⟨time,ht⟩ := runtime.zero_decrement values r hv extra (tapeValue values extra gap l)
  exact ⟨time,by simpa only [value_right,value_left,tape_box,tape_nil] using ht,by simp⟩

/-- The extra left one is part of the actual target syntax and is never erased. -/
theorem box_positive_decrement (runtime : BoxRuntime (V := V)) (r : Reg) (l : List Segment) :
    StepSound (V := V) (some (r,false))
      ⟨some Rotation240Boxes.carry,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.returnZero,true,.bit true::l,
        [.box (.plain (.decrement r))]⟩ false := by
  intro values hv extra gap
  obtain ⟨time,ht⟩ := runtime.positive_decrement values r hv extra (tapeValue values extra gap l)
  exact ⟨time,by simpa only [value_right,value_left,tape_box,tape_nil,tape_bit,digit,if_true]
    using ht,by simp⟩

/-- A literal left move over the box's leading zero retains its terminal write/move. -/
theorem box_back (br : Branch) (q : Fin 240) (next : Option (Fin 240))
    (x : Box) (l : List Segment)
    (ht : machineRotation240.transition q false = ⟨false,.left,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,[.box x]⟩ ⟨next,true,l,[.box x]⟩ true := by
  intro values hv extra gap
  refine ⟨1,?_,by intro _; simp⟩
  obtain ⟨half,hh⟩ := boxPrefix_even values hv.1 extra x (0 : V)
  simp only [runFrom_one,value_right,value_left,tape_box,tape_nil]
  rw [hh]
  simpa only [digit,Bool.false_eq_true,if_false,add_zero] using
    step_left_row false false (stateValue (some q)) (stateValue next)
      (left_row_of_transition q next false false ht) (tapeValue values extra gap l) half

structure CheckedStep (br : Branch) (s : SConfig) where
  target : SConfig
  moved : Bool
  sound : StepSound (V := V) br s target moved

private theorem action_eta (a : Action 240) : a = ⟨a.write, a.move, a.next⟩ := rfl

def peelRightChecked (br : Branch) (q : Option (Fin 240)) (b : Bool) (a c : Nat)
    (l r : List Segment) : Option (CheckedStep (V := V) br ⟨q, false, l, .run b a c :: r⟩) :=
  match c, a with
  | c + 1, a => some ⟨_, false, peel_right br q b a c l r⟩
  | 0, 0 => some ⟨_, false, empty_run_right br q b l r⟩
  | 0, _ + 1 => none

def peelLeftChecked (br : Branch) (q : Option (Fin 240)) (b : Bool) (a c : Nat)
    (l r : List Segment) : Option (CheckedStep (V := V) br ⟨q, true, .run b a c :: l, r⟩) :=
  match c, a with
  | c + 1, a => some ⟨_, false, peel_left br q b a c l r⟩
  | 0, 0 => some ⟨_, false, empty_run_left br q b l r⟩
  | 0, _ + 1 => none

def boxChecked (runtime : BoxRuntime (V := V)) (br : Branch) (q : Fin 240) (x : Box) (l : List Segment) :
    Option (CheckedStep (V := V) br ⟨some q, false, l, [.box x]⟩) := by
  cases x with
  | plain e =>
    cases e with
    | unchanged =>
      cases hs : SymbolicRotation240.skipTarget q with
      | none => exact none
      | some r =>
        exact some ⟨_, false, by
          rw [SymbolicRotation240.skipTarget_sound q r hs]
          exact box_mark runtime br r l⟩
    | increment _ => exact none
    | decrement _ => exact none
  | marked r =>
    by_cases hi : q = Rotation240Boxes.seek
    · exact some ⟨_, false, by
        subst q
        exact box_increment runtime br r l⟩
    · by_cases hd : q = Rotation240Boxes.carry
      · cases br with
        | none => exact none
        | some pair =>
          rcases pair with ⟨r', zero⟩
          by_cases hr : r = r'
          · subst r'
            subst q
            cases zero with
            | false => exact some ⟨_, false, box_positive_decrement runtime r l⟩
            | true => exact some ⟨_, false, box_zero_decrement runtime r l⟩
          · exact none
      · exact none

/-- A proof-producing version of the pinned executor's one-step function.
Only literal transitions set moved=true. Scans and boxes can consume many
steps but never manufacture the required positive-progress certificate. -/
def checkedStep (runtime : BoxRuntime (V := V)) (br : Branch) (s : SConfig) : Option (CheckedStep (V := V) br s) := by
  rcases s with ⟨state, onLeft, l, r⟩
  cases state with
  | none => exact none
  | some q =>
    cases onLeft with
    | true =>
      cases l with
      | nil => exact some ⟨_, false, left_empty br (some q) r⟩
      | cons x l =>
        cases x with
        | bit b => exact some ⟨_, false, left_bit br (some q) b l r⟩
        | box _ => exact none
        | run b a c =>
          let act := FastTableRotation240.fastMachine.transition q b
          by_cases hm : act.move = .left
          · by_cases hn : act.next = some q
            · have ht : machineRotation240.transition q b = ⟨act.write, .left, some q⟩ := by
                rw [← FastTableRotation240.fast_transition_eq q b]
                simpa only [hm, hn] using action_eta act
              exact some ⟨_, false, scan_left br q b act.write a c l r ht⟩
            · exact peelLeftChecked (V := V) br (some q) b a c l r
          · exact peelLeftChecked (V := V) br (some q) b a c l r
    | false =>
      cases r with
      | nil => exact none
      | cons x r =>
        cases x with
        | bit b =>
          let act := FastTableRotation240.fastMachine.transition q b
          cases hm : act.move with
          | right =>
            have ht : machineRotation240.transition q b = ⟨act.write, .right, act.next⟩ := by
              rw [← FastTableRotation240.fast_transition_eq q b]
              simpa only [hm] using action_eta act
            exact some ⟨_, true, literal_right br q act.next b act.write l r ht⟩
          | left =>
            have ht : machineRotation240.transition q b = ⟨act.write, .left, act.next⟩ := by
              rw [← FastTableRotation240.fast_transition_eq q b]
              simpa only [hm] using action_eta act
            exact some ⟨_, true, literal_left br q act.next b act.write l r ht⟩
        | run b a c =>
          let act := FastTableRotation240.fastMachine.transition q b
          by_cases hm : act.move = .right
          · by_cases hn : act.next = some q
            · have ht : machineRotation240.transition q b = ⟨act.write, .right, some q⟩ := by
                rw [← FastTableRotation240.fast_transition_eq q b]
                simpa only [hm, hn] using action_eta act
              exact some ⟨_, false, scan_right br q b act.write a c l r ht⟩
            · exact peelRightChecked (V := V) br (some q) b a c l r
          · exact peelRightChecked (V := V) br (some q) b a c l r
        | box x =>
          cases r with
          | cons _ _ => exact none
          | nil =>
            cases ho : boxChecked (V := V) runtime br q x l with
            | some out => exact some out
            | none =>
              let act := FastTableRotation240.fastMachine.transition q false
              by_cases hm : act.move = .left
              · by_cases hw : act.write = false
                · have ht : machineRotation240.transition q false = ⟨false, .left, act.next⟩ := by
                    rw [← FastTableRotation240.fast_transition_eq q false]
                    simpa only [hm, hw] using action_eta act
                  exact some ⟨_, true, box_back br q act.next x l ht⟩
                · exact none
              · exact none

def sstep (runtime : BoxRuntime (V := V)) (br : Branch) (s : SConfig) : Option (SConfig × Bool) :=
  (checkedStep (V := V) runtime br s).map (fun out => (out.target, out.moved))

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240
