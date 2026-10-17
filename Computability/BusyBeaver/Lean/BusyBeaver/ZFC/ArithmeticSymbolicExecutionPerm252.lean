import BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252

/-!
Arithmetic meaning of successful traces of the actual finite symbolic checker.
The finite syntax, coefficients, physical branch and executor fuel are external;
register values, gap, spare count, complete tape halves and execution clocks
range over every IΣ1 model. Concrete boxes use the fixed nine-primary-file
interpretation. Only a literal transition supplies positive progress.

The proof-producing arithmetic mirror below has the same target/moved erasure
as the existing SymbolicPerm252 checker. The erasure equality is an explicit
obligation, not an assumed execution oracle. No internal-variable syntax/fuel
graph, first-exit, whole runtime invariant or PA endpoint is asserted.
Mira-Cult, Jeff and Wade retain their machine/framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterReturnPerm252
open ArithmeticSymbolicTapePerm252
open ArithmeticSymbolicBoxesPerm252 (boxPrefix ValidValues stateValue)
open SymbolicPerm252 (Branch Reg Box Effect Segment SConfig)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def tapeValue (values : List V) (count gap : V) (xs : List Segment) : V :=
  tapePrefix gap (boxPrefix values count) xs 0
noncomputable def value (values : List V) (count gap : V) (s : SConfig) : V :=
  configValue gap (boxPrefix values count) s

@[simp] lemma tape_nil (values : List V) (count gap : V) :
    tapeValue values count gap [] = 0 := rfl
@[simp] lemma tape_bit (values : List V) (count gap : V) (b : Bool) (xs : List Segment) :
    tapeValue values count gap (.bit b::xs) = 2*tapeValue values count gap xs+digit b := rfl
@[simp] lemma tape_run (values : List V) (count gap : V) (b : Bool) (a c : Nat)
    (xs : List Segment) :
    tapeValue values count gap (.run b a c::xs) =
      bitPrefix b (affine gap a c) (tapeValue values count gap xs) := rfl
@[simp] lemma tape_box (values : List V) (count gap : V) (x : Box) (xs : List Segment) :
    tapeValue values count gap (.box x::xs) = boxPrefix values count x (tapeValue values count gap xs) := rfl
@[simp] lemma value_right (values : List V) (count gap : V)
    (q : Option (Fin 252)) (l r : List Segment) :
    value values count gap ⟨q,false,l,r⟩ =
      frame (stateValue q) (tapeValue values count gap l) (tapeValue values count gap r) := rfl
@[simp] lemma value_left (values : List V) (count gap : V)
    (q : Option (Fin 252)) (l r : List Segment) :
    value values count gap ⟨q,true,l,r⟩ =
      leftFrame (stateValue q) (tapeValue values count gap l) (tapeValue values count gap r) := rfl

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
lemma right_row_of_transition (q : Fin 252) (next : Option (Fin 252)) (read write : Bool)
    (ht : machinePerm252.transition q read = ⟨write,.right,next⟩) :
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

lemma left_row_of_transition (q : Fin 252) (next : Option (Fin 252)) (read write : Bool)
    (ht : machinePerm252.transition q read = ⟨write,.left,next⟩) :
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

/-- The same original values/count interpret both source and target effects. -/
def StepSound (br : Branch) (s t : SConfig) (moved : Bool) : Prop :=
  ∀ (values : List V), ValidValues br values → ∀ count gap : V,
    ∃ time : V, runFrom time (value values count gap s) = value values count gap t ∧
      (moved = true → 0 < time)

/-- One literal transition supplies a positive internal clock. -/
theorem literal_right (br : Branch) (q : Fin 252) (next : Option (Fin 252))
    (read written : Bool) (l r : List Segment)
    (ht : machinePerm252.transition q read = ⟨written,.right,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,.bit read::r⟩
      ⟨next,false,.bit written::l,r⟩ true := by
  intro values _ count gap
  refine ⟨1,?_,by intro _; simp⟩
  simpa only [runFrom_one,value_right,tape_bit] using
    step_right_row read written (stateValue (some q)) (stateValue next)
      (right_row_of_transition q next read written ht)
      (tapeValue values count gap l) (tapeValue values count gap r)

theorem literal_left (br : Branch) (q : Fin 252) (next : Option (Fin 252))
    (read written : Bool) (l r : List Segment)
    (ht : machinePerm252.transition q read = ⟨written,.left,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,.bit read::r⟩
      ⟨next,true,l,.bit written::r⟩ true := by
  intro values _ count gap
  refine ⟨1,?_,by intro _; simp⟩
  simpa only [runFrom_one,value_right,value_left,tape_bit] using
    step_left_row read written (stateValue (some q)) (stateValue next)
      (left_row_of_transition q next read written ht)
      (tapeValue values count gap l) (tapeValue values count gap r)

theorem left_empty (br : Branch) (q : Option (Fin 252)) (r : List Segment) :
    StepSound (V := V) br ⟨q,true,[],r⟩ ⟨q,false,[],.bit false::r⟩ false := by
  intro values _ count gap
  refine ⟨0,?_,by simp⟩
  simp [leftFrame,digit]

theorem left_bit (br : Branch) (q : Option (Fin 252)) (b : Bool) (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.bit b::l,r⟩ ⟨q,false,l,.bit b::r⟩ false := by
  intro values _ count gap
  refine ⟨0,?_,by simp⟩
  simp only [runFrom_zero,value_left,value_right,tape_bit,leftFrame_digit]

theorem peel_right (br : Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List Segment) :
    StepSound (V := V) br ⟨q,false,l,.run b a (c+1)::r⟩
      ⟨q,false,l,.bit b::.run b a c::r⟩ false := by
  intro values _ count gap
  refine ⟨0,?_,by simp⟩
  simp only [runFrom_zero,value_right,tape_run,tape_bit,affine_succ,bitPrefix_succ]

theorem peel_left (br : Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.run b a (c+1)::l,r⟩
      ⟨q,true,.bit b::.run b a c::l,r⟩ false := by
  intro values _ count gap
  refine ⟨0,?_,by simp⟩
  simp only [runFrom_zero,value_left,tape_run,tape_bit,affine_succ,bitPrefix_succ]

theorem empty_run_right (br : Branch) (q : Option (Fin 252)) (b : Bool)
    (l r : List Segment) :
    StepSound (V := V) br ⟨q,false,l,.run b 0 0::r⟩ ⟨q,false,l,r⟩ false := by
  intro values _ count gap
  refine ⟨0,?_,by simp⟩
  simp [affine]

theorem empty_run_left (br : Branch) (q : Option (Fin 252)) (b : Bool)
    (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.run b 0 0::l,r⟩ ⟨q,true,l,r⟩ false := by
  intro values _ count gap
  refine ⟨0,?_,by simp⟩
  simp [affine]

/-- A writing scan uses the whole affine internal length but does not mark progress. -/
theorem scan_right (br : Branch) (q : Fin 252) (read written : Bool) (a c : Nat)
    (l r : List Segment)
    (ht : machinePerm252.transition q read = ⟨written,.right,some q⟩) :
    StepSound (V := V) br ⟨some q,false,l,.run read a c::r⟩
      ⟨some q,false,.run written a c::l,r⟩ false := by
  intro values _ count gap
  refine ⟨affine gap a c,?_,by simp⟩
  simpa only [value_right,tape_run] using
    ArithmeticWritingScansPerm252.scan_right read written (stateValue (some q))
      (right_row_of_transition q (some q) read written ht) (affine gap a c)
      (tapeValue values count gap l) (tapeValue values count gap r)

theorem scan_left (br : Branch) (q : Fin 252) (read written : Bool) (a c : Nat)
    (l r : List Segment)
    (ht : machinePerm252.transition q read = ⟨written,.left,some q⟩) :
    StepSound (V := V) br ⟨some q,true,.run read a c::l,r⟩
      ⟨some q,true,l,.run written a c::r⟩ false := by
  intro values _ count gap
  refine ⟨affine gap a c,?_,by simp⟩
  simpa only [value_left,tape_run] using
    ArithmeticWritingScansPerm252.scan_left read written (stateValue (some q))
      (left_row_of_transition q (some q) read written ht) (affine gap a c)
      (tapeValue values count gap l) (tapeValue values count gap r)

/-- The actual nine-selector mark macro. -/
theorem box_mark (br : Branch) (r : Reg) (l : List Segment) :
    StepSound (V := V) br
      ⟨some (RegisterMarkPerm252.skip r.val),false,l,[.box (.plain .unchanged)]⟩
      ⟨some (SymbolicPerm252.markExit r),true,l,[.box (.marked r)]⟩ false := by
  intro values hv count gap
  obtain ⟨time,ht⟩ := ArithmeticSymbolicBoxesPerm252.box_mark br values hv r count
    (tapeValue values count gap l)
  exact ⟨time,by simpa only [value_right,value_left,tape_box,tape_nil] using ht,by simp⟩

theorem box_increment (br : Branch) (r : Reg) (l : List Segment) :
    StepSound (V := V) br
      ⟨some RegisterIncrementPerm252.seekInc,false,l,[.box (.marked r)]⟩
      ⟨some RegisterIncrementPerm252.incReturnZero,true,l,[.box (.plain (.increment r))]⟩ false := by
  intro values hv count gap
  obtain ⟨time,ht⟩ := ArithmeticSymbolicBoxesPerm252.box_increment br values hv r count
    (tapeValue values count gap l)
  exact ⟨time,by simpa only [value_right,value_left,tape_box,tape_nil] using ht,by simp⟩

theorem box_zero_decrement (r : Reg) (l : List Segment) :
    StepSound (V := V) (some (r,true))
      ⟨some RegisterBoxesPerm252.seekDec,false,l,[.box (.marked r)]⟩
      ⟨some RegisterBoxesPerm252.returnZero,true,l,[.box (.plain .unchanged)]⟩ false := by
  intro values hv count gap
  obtain ⟨time,ht⟩ := ArithmeticSymbolicBoxesPerm252.box_zero_decrement values r hv count
    (tapeValue values count gap l)
  exact ⟨time,by simpa only [value_right,value_left,tape_box,tape_nil] using ht,by simp⟩

theorem box_positive_decrement (r : Reg) (l : List Segment) :
    StepSound (V := V) (some (r,false))
      ⟨some RegisterBoxesPerm252.seekDec,false,l,[.box (.marked r)]⟩
      ⟨some (SymbolicPerm252.positiveExit r),true,l,[.box (.plain (.decrement r))]⟩ false := by
  intro values hv count gap
  obtain ⟨time,ht⟩ := ArithmeticSymbolicBoxesPerm252.box_positive_decrement values r hv count
    (tapeValue values count gap l)
  exact ⟨time,by simpa only [value_right,value_left,tape_box,tape_nil] using ht,by simp⟩

/-- The actual final left move is retained even when next is halt. -/
theorem box_back (br : Branch) (q : Fin 252) (next : Option (Fin 252))
    (x : Box) (l : List Segment)
    (ht : machinePerm252.transition q false = ⟨false,.left,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,[.box x]⟩ ⟨next,true,l,[.box x]⟩ true := by
  intro values hv count gap
  refine ⟨1,?_,by intro _; simp⟩
  simpa only [value_right,value_left,tape_box,tape_nil] using
    ArithmeticSymbolicBoxesPerm252.box_back values hv.1 count (stateValue (some q))
      (stateValue next) (tapeValue values count gap l) x
      (left_row_of_transition q next false false ht)

structure CheckedStep (br : Branch) (s : SConfig) where
  target : SConfig
  moved : Bool
  sound : StepSound (V := V) br s target moved

private theorem action_eta (a : Action 252) : a = ⟨a.write, a.move, a.next⟩ := rfl

def peelRightChecked (br : Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List Segment) : Option (CheckedStep (V := V) br ⟨q, false, l, .run b a c :: r⟩) :=
  match c, a with
  | c + 1, a => some ⟨_, false, peel_right br q b a c l r⟩
  | 0, 0 => some ⟨_, false, empty_run_right br q b l r⟩
  | 0, _ + 1 => none

def peelLeftChecked (br : Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List Segment) : Option (CheckedStep (V := V) br ⟨q, true, .run b a c :: l, r⟩) :=
  match c, a with
  | c + 1, a => some ⟨_, false, peel_left br q b a c l r⟩
  | 0, 0 => some ⟨_, false, empty_run_left br q b l r⟩
  | 0, _ + 1 => none

def boxChecked (br : Branch) (q : Fin 252) (x : Box) (l : List Segment) :
    Option (CheckedStep (V := V) br ⟨some q, false, l, [.box x]⟩) := by
  cases x with
  | plain e =>
    cases e with
    | unchanged =>
      cases hs : SymbolicPerm252.skipTarget q with
      | none => exact none
      | some r =>
        exact some ⟨_, false, by
          rw [SymbolicPerm252.skipTarget_sound q r hs]
          exact box_mark br r l⟩
    | increment _ => exact none
    | decrement _ => exact none
  | marked r =>
    by_cases hi : q = RegisterIncrementPerm252.seekInc
    · exact some ⟨_, false, by
        subst q
        exact box_increment br r l⟩
    · by_cases hd : q = RegisterBoxesPerm252.seekDec
      · cases br with
        | none => exact none
        | some pair =>
          rcases pair with ⟨r', zero⟩
          by_cases hr : r = r'
          · subst r'
            subst q
            cases zero with
            | false => exact some ⟨_, false, box_positive_decrement r l⟩
            | true => exact some ⟨_, false, box_zero_decrement r l⟩
          · exact none
      · exact none

/-- A proof-producing version of the pinned executor's one-step function.
Only literal transitions set moved=true. Scans and boxes can consume many
steps but never manufacture the required positive-progress certificate. -/
def checkedStep (br : Branch) (s : SConfig) : Option (CheckedStep (V := V) br s) := by
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
          let act := BootPerm252.fastMachinePerm252.transition q b
          by_cases hm : act.move = .left
          · by_cases hn : act.next = some q
            · have ht : machinePerm252.transition q b = ⟨act.write, .left, some q⟩ := by
                rw [← BootPerm252.fast_transition_eq q b]
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
          let act := BootPerm252.fastMachinePerm252.transition q b
          cases hm : act.move with
          | right =>
            have ht : machinePerm252.transition q b = ⟨act.write, .right, act.next⟩ := by
              rw [← BootPerm252.fast_transition_eq q b]
              simpa only [hm] using action_eta act
            exact some ⟨_, true, literal_right br q act.next b act.write l r ht⟩
          | left =>
            have ht : machinePerm252.transition q b = ⟨act.write, .left, act.next⟩ := by
              rw [← BootPerm252.fast_transition_eq q b]
              simpa only [hm] using action_eta act
            exact some ⟨_, true, literal_left br q act.next b act.write l r ht⟩
        | run b a c =>
          let act := BootPerm252.fastMachinePerm252.transition q b
          by_cases hm : act.move = .right
          · by_cases hn : act.next = some q
            · have ht : machinePerm252.transition q b = ⟨act.write, .right, some q⟩ := by
                rw [← BootPerm252.fast_transition_eq q b]
                simpa only [hm, hn] using action_eta act
              exact some ⟨_, false, scan_right br q b act.write a c l r ht⟩
            · exact peelRightChecked (V := V) br (some q) b a c l r
          · exact peelRightChecked (V := V) br (some q) b a c l r
        | box x =>
          cases r with
          | cons _ _ => exact none
          | nil =>
            cases ho : boxChecked (V := V) br q x l with
            | some out => exact some out
            | none =>
              let act := BootPerm252.fastMachinePerm252.transition q false
              by_cases hm : act.move = .left
              · by_cases hw : act.write = false
                · have ht : machinePerm252.transition q false = ⟨false, .left, act.next⟩ := by
                    rw [← BootPerm252.fast_transition_eq q false]
                    simpa only [hm, hw] using action_eta act
                  exact some ⟨_, true, box_back br q act.next x l ht⟩
                · exact none
              · exact none

def sstep (br : Branch) (s : SConfig) : Option (SConfig × Bool) :=
  (checkedStep (V := V) br s).map (fun out => (out.target, out.moved))

/-- Move equality-indexed casts from function results into their proof
arguments. Erasing a proof record then removes those arguments entirely. -/
private theorem rec_apply {A : Sort*} {a b : A} (h : a = b)
    {P : A → Sort*} {C : Sort*} (f : P a → C) (p : P b) :
    (h ▸ f) p = f (h.symm ▸ p) := by
  cases h
  rfl

private theorem map_option_cases {A B C : Type*} (erase : B → C)
    (x : Option A) (f : x = none → Option B) (g : ∀ a, x = some a → Option B) :
    (Option.rec (motive := fun y => x = y → Option B) f g x rfl).map erase =
      Option.rec (motive := fun y => x = y → Option C)
        (fun h => (f h).map erase) (fun a h => (g a h).map erase) x rfl := by
  cases x <;> rfl

private theorem map_move_cases {B C : Type*} (erase : B → C)
    (x : Move) (f : x = .left → Option B) (g : x = .right → Option B) :
    (Move.rec (motive := fun y => x = y → Option B) f g x rfl).map erase =
      Move.rec (motive := fun y => x = y → Option C)
        (fun h => (f h).map erase) (fun h => (g h).map erase) x rfl := by
  cases x <;> rfl

private theorem boxChecked_erasure (br : Branch) (q : Fin 252) (x : Box) (l : List Segment) :
    (boxChecked (V := V) br q x l).map (fun out => (out.target,out.moved)) =
      (SymbolicPerm252.boxChecked br q x l).map (fun out => (out.target,out.moved)) := by
  cases x with
  | plain effect =>
    cases effect with
    | unchanged =>
      dsimp only [boxChecked,SymbolicPerm252.boxChecked]
      simp only [map_option_cases,rec_apply]
      rfl
    | increment r => rfl
    | decrement r => rfl
  | marked r =>
    by_cases hi : q = RegisterIncrementPerm252.seekInc
    · subst q
      rfl
    · by_cases hd : q = RegisterBoxesPerm252.seekDec
      · subst q
        cases br with
        | none => rfl
        | some pair =>
          rcases pair with ⟨r',zero⟩
          by_cases hr : r = r'
          · subst r'
            cases zero <;>
              dsimp only [boxChecked,SymbolicPerm252.boxChecked] <;>
              simp only [dif_neg hi] <;> rfl
          · simp [boxChecked,SymbolicPerm252.boxChecked,hr]
      · simp [boxChecked,SymbolicPerm252.boxChecked,hi,hd]

/-- Exact computational linkage to the actual checker. Finite control cases
are needed because map does not definitionally distribute over the decision
branches and the two structures have different proof fields. -/
theorem sstep_eq (br : Branch) (s : SConfig) :
    sstep (V := V) br s = SymbolicPerm252.sstep br s := by
  unfold sstep SymbolicPerm252.sstep
  rcases s with ⟨state,onLeft,l,r⟩
  cases state with
  | none => rfl
  | some q =>
    cases onLeft with
    | true =>
      cases l with
      | nil => rfl
      | cons x l =>
        cases x with
        | bit b => rfl
        | box x => rfl
        | run b a c =>
          by_cases hm : (BootPerm252.fastMachinePerm252.transition q b).move = .left <;>
          by_cases hn : (BootPerm252.fastMachinePerm252.transition q b).next = some q <;>
          cases c <;> cases a <;>
            simp [checkedStep,SymbolicPerm252.checkedStep,hm,hn,
              peelLeftChecked,SymbolicPerm252.peelLeftChecked]
    | false =>
      cases r with
      | nil => rfl
      | cons x r =>
        cases x with
        | bit b =>
          dsimp only [checkedStep,SymbolicPerm252.checkedStep]
          simp only [map_move_cases,rec_apply]
          rfl
        | run b a c =>
          by_cases hm : (BootPerm252.fastMachinePerm252.transition q b).move = .right <;>
          by_cases hn : (BootPerm252.fastMachinePerm252.transition q b).next = some q <;>
          cases c <;> cases a <;>
            simp [checkedStep,SymbolicPerm252.checkedStep,hm,hn,
              peelRightChecked,SymbolicPerm252.peelRightChecked]
        | box x =>
          cases r with
          | cons y r => rfl
          | nil =>
            have hb := boxChecked_erasure (V := V) br q x l
            dsimp only [checkedStep,SymbolicPerm252.checkedStep]
            simp only [map_option_cases,rec_apply]
            cases ho : boxChecked (V := V) br q x l with
            | none =>
              cases hn : SymbolicPerm252.boxChecked br q x l with
              | some out => simp [ho,hn] at hb
              | none =>
                by_cases hm : (BootPerm252.fastMachinePerm252.transition q false).move = .left <;>
                by_cases hw : (BootPerm252.fastMachinePerm252.transition q false).write = false <;>
                  simp [hm,hw]
            | some out =>
              cases hn : SymbolicPerm252.boxChecked br q x l with
              | none => simp [ho,hn] at hb
              | some out' =>
                simpa [ho,hn] using hb

theorem sstep_sound (br : Branch) (s t : SConfig) (m : Bool)
    (hs : sstep (V := V) br s = some (t, m)) : StepSound (V := V) br s t m := by
  unfold sstep at hs
  cases hc : checkedStep (V := V) br s with
  | none => simp [hc] at hs
  | some out =>
    simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨ht, hm⟩
    simpa only [ht, hm] using out.sound

/-- Every successful step of the ACTUAL native finite checker has its stated
all-model arithmetic meaning. -/
theorem actual_sstep_sound (br : Branch) (s t : SConfig) (m : Bool)
    (hs : SymbolicPerm252.sstep br s = some (t,m)) : StepSound (V := V) br s t m := by
  apply sstep_sound br s t m
  rw [sstep_eq]
  exact hs

/-- External finite-fuel induction composes internal clocks. -/
theorem exec_sound (fuel : Nat) (br : Branch) (target : SConfig → Bool)
    (s t : SConfig) (moved : Bool)
    (he : SymbolicPerm252.exec fuel br target s moved = some t) :
    target t = true ∧ StepSound (V := V) br s t (!moved) := by
  induction fuel generalizing s moved with
  | zero => simp [SymbolicPerm252.exec] at he
  | succ fuel ih =>
    simp only [SymbolicPerm252.exec] at he
    split at he
    next halt =>
      have ht : moved = true ∧ target s = true := Bool.and_eq_true_iff.mp halt
      cases he
      refine ⟨ht.2,?_⟩
      intro values _ count gap
      exact ⟨0,by simp,by simp [ht.1]⟩
    next _ =>
      cases hs : SymbolicPerm252.sstep br s with
      | none => simp [hs] at he
      | some pair =>
        rcases pair with ⟨u,m⟩
        simp only [hs] at he
        obtain ⟨ht,hh⟩ := ih u (moved || m) he
        refine ⟨ht,?_⟩
        intro values hv count gap
        obtain ⟨k,hk,hp⟩ := actual_sstep_sound br s u m hs values hv count gap
        obtain ⟨j,hj,hq⟩ := hh values hv count gap
        refine ⟨k+j,?_,?_⟩
        · rw [runFrom_add,hk,hj]
        · intro hmove
          cases moved <;> cases m
          · exact lt_of_lt_of_le (hq rfl) (by simp)
          · exact lt_of_lt_of_le (hp rfl) (by simp)
          · simp at hmove
          · simp at hmove

theorem exec_to_matches (fuel : Nat) (br : Branch) (s wanted reached : SConfig)
    (he : SymbolicPerm252.exec fuel br (fun t => SymbolicPerm252.isMatch t wanted)
      s false = some reached)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values count gap s) =
      value values count gap wanted := by
  obtain ⟨hm,hs⟩ := exec_sound (V := V) fuel br (fun t => SymbolicPerm252.isMatch t wanted)
    s reached false he
  obtain ⟨time,ht,hp⟩ := hs values hv count gap
  have hvv : value values count gap reached = value values count gap wanted :=
    isMatch_value gap (boxPrefix values count) reached wanted hm
  exact ⟨time,hp rfl,ht.trans hvv⟩

lemma value_state (values : List V) (count gap : V) (s : SConfig) :
    first (value values count gap s) = stateValue s.state := by
  rcases s with ⟨q,onLeft,l,r⟩
  cases onLeft <;> simp [value,configValue,frame,leftFrame,stateValue]

theorem exec_to_halt (fuel : Nat) (br : Branch) (s reached : SConfig)
    (he : SymbolicPerm252.exec fuel br (fun t => decide (t.state = none))
      s false = some reached)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values count gap s)) = 0 := by
  obtain ⟨hm,hs⟩ := exec_sound (V := V) fuel br (fun t => decide (t.state = none)) s reached false he
  obtain ⟨time,ht,hp⟩ := hs values hv count gap
  have hsnone : reached.state = none := of_decide_eq_true hm
  refine ⟨time,hp rfl,?_⟩
  rw [ht,value_state,hsnone]
  simp [stateValue,ArithmeticMachinePerm252.stateCode]

/-- Existing Boolean certificate acceptance, with no new certificate format. -/
theorem verifies_sound (fuel : Nat) (br : Branch) (s wanted : SConfig)
    (he : SymbolicPerm252.verifies fuel br s wanted = true)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values count gap s) =
      value values count gap wanted := by
  cases hx : SymbolicPerm252.exec fuel br (fun t => SymbolicPerm252.isMatch t wanted) s false with
  | none => simp [SymbolicPerm252.verifies,hx] at he
  | some reached => exact exec_to_matches fuel br s wanted reached hx values hv count gap

theorem verifiesHalt_sound (fuel : Nat) (br : Branch) (s : SConfig)
    (he : SymbolicPerm252.verifiesHalt fuel br s = true)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values count gap s)) = 0 := by
  cases hx : SymbolicPerm252.exec fuel br (fun t => decide (t.state = none)) s false with
  | none => simp [SymbolicPerm252.verifiesHalt,hx] at he
  | some reached => exact exec_to_halt fuel br s reached hx values hv count gap

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252
