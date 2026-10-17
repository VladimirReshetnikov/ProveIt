import BusyBeaver.ZFC.BootPerm252
import BusyBeaver.ZFC.RegisterMarkPerm252
import BusyBeaver.ZFC.RegisterIncrementPerm252
import BusyBeaver.ZFC.RegisterDecrementPerm252
import BusyBeaver.ZFC.WritingRuns

/-!
A sound affine symbolic executor for the actual permutation252 table.

The segment language and execution strategy are adapted from Mira-Cult's
`ZF/m254/coq/tm/SymExec.v` at upstream commit
297ab8df7e5de329605c3875b4934643b371a5e3. The published machine and
verification are attributed to Mira-Cult and Jeff, with Wade's compiler
framework. The register lemmas imported above are new Lean proofs of the
literal candidate table, not hypotheses supplied to this executor.

A tape run has affine length `a*n+c`, uniformly in every natural gap parameter.
The register file is a separate symbolic object with at most one effect.
Its physical spare suffix is arbitrary and remains on the tape; positive
decrement appends a zero block. A named physical-register guard justifies
which decrement branch is taken.

The interpretation uses the existing whole-tape ZipRep and Core.runFrom.
Its boundary coordinate is existential, so list recentering does not require
a second symbolic displacement language. A true progress flag certifies at
least one literal transition. A halting transition retains its final write
and head move, with state `none`.

This module is the generic checker layer. It does not itself enumerate all
instruction sites, prove a decoder invariant, or connect the machine to ZFC.
-/

namespace SetTheory.BusyBeaver.ZFC.SymbolicPerm252

open FiniteZipper ZipperRuns
open RegisterBoxesPerm252 (registerBits width)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev Reg := Fin 9
abbrev Branch := Option (Reg × Bool)

inductive Effect where
  | unchanged
  | increment (r : Reg)
  | decrement (r : Reg)
  deriving DecidableEq, Repr

inductive Box where
  | plain (effect : Effect)
  | marked (r : Reg)
  deriving DecidableEq, Repr

def incr : Nat → List Nat → List Nat
  | _, [] => []
  | 0, v :: vs => (v + 1) :: vs
  | r + 1, v :: vs => v :: incr r vs

def decr : Nat → List Nat → List Nat
  | _, [] => []
  | 0, v :: vs => v.pred :: vs
  | r + 1, v :: vs => v :: decr r vs

def markedBits : Nat → List Nat → List Bool
  | _, [] => []
  | 0, v :: vs => false :: false :: (List.replicate v true ++ registerBits vs)
  | r + 1, v :: vs => false :: true :: (List.replicate v true ++ markedBits r vs)

/-- The final false cell is explicit padding in the existing box contracts.
The surrounding interpretation still specifies the entire blank exterior. -/
def boxBits (x : Box) (vs : List Nat) : List Bool :=
  (match x with
  | .plain .unchanged => registerBits vs
  | .plain (.increment r) => registerBits (incr r.val vs)
  | .plain (.decrement r) => registerBits (decr r.val vs ++ [0])
  | .marked r => markedBits r.val vs) ++ [false]

def Valid (br : Branch) (vs : List Nat) : Prop :=
  9 ≤ vs.length ∧ match br with
  | none => True
  | some (r, zero) => if zero then vs.getD r.val 0 = 0 else vs.getD r.val 0 ≠ 0

inductive Segment where
  | bit (b : Bool)
  | run (b : Bool) (a c : Nat)
  | box (x : Box)
  deriving DecidableEq, Repr

def segmentBits (n : Nat) (vs : List Nat) : Segment → List Bool
  | .bit b => [b]
  | .run b a c => List.replicate (a * n + c) b
  | .box x => boxBits x vs

def flat (n : Nat) (vs : List Nat) (xs : List Segment) : List Bool :=
  xs.flatMap (segmentBits n vs)

structure SConfig where
  state : Option (Fin 252)
  onLeft : Bool
  left : List Segment
  right : List Segment
  deriving DecidableEq, Repr

def zAtS (q : Option (Fin 252)) (h : Int) (l r : List Bool) : ZipConfig 252 :=
  { state := q, head := h, left := l, right := r }

def leftAtS (q : Option (Fin 252)) (h : Int) (l r : List Bool) : ZipConfig 252 :=
  { state := q, head := h - 1, left := l.tail, right := l.getD 0 false :: r }

def concrete (n : Nat) (vs : List Nat) (s : SConfig) (h : Int) : ZipConfig 252 :=
  if s.onLeft then leftAtS s.state h (flat n vs s.left) (flat n vs s.right)
  else zAtS s.state h (flat n vs s.left) (flat n vs s.right)

def Represents (n : Nat) (vs : List Nat) (s : SConfig) (c : Config 252) : Prop :=
  ∃ h : Int, ZipRep c (concrete n vs s h)

/-- Soundness includes every cell of the source and target tapes. The clock
may depend on the actual gap and register values, but is positive whenever
the symbolic executor marks literal progress. -/
def StepSound (br : Branch) (s t : SConfig) (moved : Bool) : Prop :=
  ∀ n vs, Valid br vs → ∀ c, Represents n vs s c →
    ∃ k : Nat, Represents n vs t (machinePerm252.runFrom c k) ∧
      (moved = true → 0 < k)

theorem flat_cons (n : Nat) (vs : List Nat) (x : Segment) (xs : List Segment) :
    flat n vs (x :: xs) = segmentBits n vs x ++ flat n vs xs := rfl

theorem flat_append (n : Nat) (vs : List Nat) (a b : List Segment) :
    flat n vs (a ++ b) = flat n vs a ++ flat n vs b := by
  simp [flat, List.flatMap_append]

theorem incr_split (pre : List Nat) (v : Nat) (rest : List Nat) :
    incr pre.length (pre ++ v :: rest) = pre ++ (v + 1) :: rest := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simpa [incr] using congrArg (List.cons a) ih

theorem decr_split (pre : List Nat) (v : Nat) (rest : List Nat) :
    decr pre.length (pre ++ v :: rest) = pre ++ v.pred :: rest := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simpa [decr] using congrArg (List.cons a) ih

theorem markedBits_split (pre : List Nat) (v : Nat) (rest : List Nat) :
    markedBits pre.length (pre ++ v :: rest) =
      registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest) := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [markedBits, registerBits, ih, List.append_assoc]

theorem split_register (r : Nat) (vs : List Nat) (hr : r < vs.length) :
    ∃ pre v rest, vs = pre ++ v :: rest ∧ pre.length = r ∧ vs.getD r 0 = v := by
  induction r generalizing vs with
  | zero =>
    cases vs with
    | nil => simp at hr
    | cons v rest => exact ⟨[], v, rest, rfl, rfl, rfl⟩
  | succ r ih =>
    cases vs with
    | nil => simp at hr
    | cons a vs =>
      obtain ⟨pre, v, rest, he, hl, hv⟩ := ih vs (by simpa using hr)
      exact ⟨a :: pre, v, rest, by simp [he], by simp [hl], hv⟩

theorem box_head (x : Box) (vs : List Nat) (hne : vs ≠ []) :
    ∃ t, boxBits x vs = false :: t := by
  cases vs with
  | nil => exact False.elim (hne rfl)
  | cons v vs =>
    cases x with
    | plain e => cases e with
      | unchanged => simp [boxBits, registerBits]
      | increment r => cases hr : r.val <;> simp [boxBits, incr, hr, registerBits]
      | decrement r => cases hr : r.val <;> simp [boxBits, decr, hr, registerBits]
    | marked r => cases hr : r.val <;> simp [boxBits, markedBits, hr]

private theorem step_right_option (q : Fin 252) (next : Option (Fin 252))
    (read written : Bool) (h : Int) (l r : List Bool)
    (ht : machinePerm252.transition q read = ⟨written, .right, next⟩) :
    zipStep machinePerm252 (zAtS (some q) h l (read :: r)) =
      zAtS next (h + 1) (written :: l) r := by
  simp [zipStep, zAtS, ht, zipWrite, zipRight]

private theorem step_left_option (q : Fin 252) (next : Option (Fin 252))
    (read written : Bool) (h : Int) (l r : List Bool)
    (ht : machinePerm252.transition q read = ⟨written, .left, next⟩) :
    zipStep machinePerm252 (zAtS (some q) h l (read :: r)) =
      leftAtS next h l (written :: r) := by
  simp [zipStep, zAtS, leftAtS, ht, zipWrite, zipLeft]

theorem literal_right (br : Branch) (q : Fin 252) (next : Option (Fin 252))
    (read written : Bool) (l r : List Segment)
    (ht : machinePerm252.transition q read = ⟨written, .right, next⟩) :
    StepSound br ⟨some q, false, l, .bit read :: r⟩
      ⟨next, false, .bit written :: l, r⟩ true := by
  intro n vs hv c hc
  obtain ⟨h, hc⟩ := hc
  have hs := zipStep_sound machinePerm252 hc
  simp only [concrete, Bool.false_eq_true, if_false, flat_cons, segmentBits,
    List.singleton_append] at hc hs ⊢
  rw [step_right_option q next read written h _ _ ht] at hs
  exact ⟨1, ⟨h + 1, hs⟩, by omega⟩

theorem literal_left (br : Branch) (q : Fin 252) (next : Option (Fin 252))
    (read written : Bool) (l r : List Segment)
    (ht : machinePerm252.transition q read = ⟨written, .left, next⟩) :
    StepSound br ⟨some q, false, l, .bit read :: r⟩
      ⟨next, true, l, .bit written :: r⟩ true := by
  intro n vs hv c hc
  obtain ⟨h, hc⟩ := hc
  have hs := zipStep_sound machinePerm252 hc
  simp only [concrete, Bool.false_eq_true, if_false,
    flat_cons, segmentBits, List.singleton_append] at hc hs ⊢
  rw [step_left_option q next read written h _ _ ht] at hs
  exact ⟨1, ⟨h, hs⟩, by omega⟩

theorem left_empty (br : Branch) (q : Option (Fin 252)) (r : List Segment) :
    StepSound br ⟨q, true, [], r⟩ ⟨q, false, [], .bit false :: r⟩ false := by
  intro n vs hv c hc
  obtain ⟨h, hc⟩ := hc
  exact ⟨0, ⟨h - 1, hc⟩, by simp⟩

theorem left_bit (br : Branch) (q : Option (Fin 252)) (b : Bool)
    (l r : List Segment) :
    StepSound br ⟨q, true, .bit b :: l, r⟩ ⟨q, false, l, .bit b :: r⟩ false := by
  intro n vs hv c hc
  obtain ⟨h, hc⟩ := hc
  exact ⟨0, ⟨h - 1, hc⟩, by simp⟩

theorem peel_right (br : Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List Segment) :
    StepSound br ⟨q, false, l, .run b a (c + 1) :: r⟩
      ⟨q, false, l, .bit b :: .run b a c :: r⟩ false := by
  intro n vs hv conf hc
  refine ⟨0, ?_, by simp⟩
  simpa [Represents, concrete, flat_cons, segmentBits, ← Nat.add_assoc,
    List.replicate_succ, Machine.runFrom] using hc

theorem peel_left (br : Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List Segment) :
    StepSound br ⟨q, true, .run b a (c + 1) :: l, r⟩
      ⟨q, true, .bit b :: .run b a c :: l, r⟩ false := by
  intro n vs hv conf hc
  refine ⟨0, ?_, by simp⟩
  simpa [Represents, concrete, flat_cons, segmentBits, ← Nat.add_assoc,
    List.replicate_succ, Machine.runFrom] using hc

theorem empty_run_right (br : Branch) (q : Option (Fin 252)) (b : Bool)
    (l r : List Segment) :
    StepSound br ⟨q, false, l, .run b 0 0 :: r⟩ ⟨q, false, l, r⟩ false := by
  intro n vs hv conf hc
  exact ⟨0, by simpa [Represents, concrete, flat_cons, segmentBits, Machine.runFrom] using hc, by simp⟩

theorem empty_run_left (br : Branch) (q : Option (Fin 252)) (b : Bool)
    (l r : List Segment) :
    StepSound br ⟨q, true, .run b 0 0 :: l, r⟩ ⟨q, true, l, r⟩ false := by
  intro n vs hv conf hc
  exact ⟨0, by simpa [Represents, concrete, flat_cons, segmentBits, Machine.runFrom] using hc, by simp⟩

theorem scan_right (br : Branch) (q : Fin 252) (read written : Bool) (a c : Nat)
    (l r : List Segment)
    (ht : machinePerm252.transition q read = ⟨written, .right, some q⟩) :
    StepSound br ⟨some q, false, l, .run read a c :: r⟩
      ⟨some q, false, .run written a c :: l, r⟩ false := by
  intro n vs hv conf hc
  obtain ⟨h, hc⟩ := hc
  have hs := WritingRuns.scan_right_write_core machinePerm252 q read written ht
    (a * n + c) h (flat n vs l) (flat n vs r) hc
  exact ⟨a * n + c, ⟨h + ((a * n + c : Nat) : Int), hs⟩, by simp⟩

theorem scan_left (br : Branch) (q : Fin 252) (read written : Bool) (a c : Nat)
    (l r : List Segment)
    (ht : machinePerm252.transition q read = ⟨written, .left, some q⟩) :
    StepSound br ⟨some q, true, .run read a c :: l, r⟩
      ⟨some q, true, l, .run written a c :: r⟩ false := by
  intro n vs hv conf hc
  obtain ⟨h, hc⟩ := hc
  have hs := WritingRuns.scan_left_write_core machinePerm252 q read written ht
    (a * n + c) h (flat n vs l) (flat n vs r) hc
  exact ⟨a * n + c, ⟨h - ((a * n + c : Nat) : Int), hs⟩, by simp⟩

def markExit (r : Reg) : Fin 252 :=
  if r.val = 0 then RegisterMarkPerm252.markFirst else RegisterMarkPerm252.markReturnZero

def positiveExit (r : Reg) : Fin 252 :=
  if r.val = 0 then RegisterIncrementPerm252.incReturnOnes
  else RegisterIncrementPerm252.incReturnZero

private theorem markExit_split (pre : List Nat) (r : Reg) (hr : pre.length = r.val) :
    RegisterMarkPerm252.markExit pre = markExit r := by
  cases pre <;> simp [RegisterMarkPerm252.markExit, markExit, ← hr]

private theorem positiveExit_split (pre : List Nat) (r : Reg) (hr : pre.length = r.val) :
    RegisterDecrementPerm252.positiveExit pre = positiveExit r := by
  cases pre <;> simp [RegisterDecrementPerm252.positiveExit, positiveExit, ← hr]

theorem box_mark (br : Branch) (r : Reg) (l : List Segment) :
    StepSound br ⟨some (RegisterMarkPerm252.skip r.val), false, l, [.box (.plain .unchanged)]⟩
      ⟨some (markExit r), true, l, [.box (.marked r)]⟩ false := by
  intro n vs hv conf hc
  obtain ⟨h, hc⟩ := hc
  obtain ⟨pre, v, rest, he, hl, _⟩ := split_register r.val vs (by have hlen := hv.1; omega)
  subst vs
  have hp : pre.length < 9 := by omega
  have input : ZipRep conf
      (zAt (RegisterMarkPerm252.skip pre.length) h (flat n (pre ++ v :: rest) l)
        (registerBits (pre ++ v :: rest) ++ [false])) := by
    simpa [concrete, flat, segmentBits, boxBits, hl, zAtS, zAt] using hc
  have hs := RegisterMarkPerm252.mark pre v rest hp h _ input
  refine ⟨2 * width pre + 3, ⟨h, ?_⟩, by simp⟩
  simpa [concrete, flat, segmentBits, boxBits, ← hl, markedBits_split,
    List.append_assoc, markExit_split pre r hl, leftAtS, leftAt] using hs

theorem box_increment (br : Branch) (r : Reg) (l : List Segment) :
    StepSound br
      ⟨some RegisterIncrementPerm252.seekInc, false, l, [.box (.marked r)]⟩
      ⟨some RegisterIncrementPerm252.incReturnZero, true, l,
        [.box (.plain (.increment r))]⟩ false := by
  intro n vs hv conf hc
  obtain ⟨h, hc⟩ := hc
  obtain ⟨pre, v, rest, he, hl, _⟩ := split_register r.val vs (by have hlen := hv.1; omega)
  subst vs
  have input : ZipRep conf
      (zAt RegisterIncrementPerm252.seekInc h (flat n (pre ++ v :: rest) l)
        (registerBits pre ++ false :: false ::
          (List.replicate v true ++ registerBits rest ++ [false]))) := by
    simpa [concrete, flat, segmentBits, boxBits, ← hl, markedBits_split,
      List.append_assoc, zAtS, zAt] using hc
  have hs := RegisterIncrementPerm252.increment pre v rest h _ input
  refine ⟨2 * width (pre ++ v :: rest) + 3, ⟨h, ?_⟩, by simp⟩
  simpa [concrete, flat, segmentBits, boxBits, ← hl, incr_split,
    leftAtS, leftAt] using hs

theorem box_zero_decrement (r : Reg) (l : List Segment) :
    StepSound (some (r, true))
      ⟨some RegisterBoxesPerm252.seekDec, false, l, [.box (.marked r)]⟩
      ⟨some RegisterBoxesPerm252.returnZero, true, l,
        [.box (.plain .unchanged)]⟩ false := by
  intro n vs hv conf hc
  obtain ⟨h, hc⟩ := hc
  obtain ⟨pre, v, rest, he, hl, hvalue⟩ := split_register r.val vs (by have hlen := hv.1; omega)
  have hz : v = 0 := hvalue.symm.trans hv.2
  rw [hz] at he
  subst vs
  have input : ZipRep conf
      (zAt RegisterBoxesPerm252.seekDec h (flat n (pre ++ 0 :: rest) l)
        (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))) := by
    simpa [concrete, flat, segmentBits, boxBits, ← hl, markedBits_split,
      List.append_assoc, zAtS, zAt] using hc
  have hs := RegisterBoxesPerm252.zero_decrement pre rest h _ input
  refine ⟨2 * width pre + 5, ⟨h, ?_⟩, by simp⟩
  simpa [concrete, flat, segmentBits, boxBits, leftAtS, leftAt] using hs

theorem box_positive_decrement (r : Reg) (l : List Segment) :
    StepSound (some (r, false))
      ⟨some RegisterBoxesPerm252.seekDec, false, l, [.box (.marked r)]⟩
      ⟨some (positiveExit r), true, l,
        [.box (.plain (.decrement r))]⟩ false := by
  intro n vs hv conf hc
  obtain ⟨h, hc⟩ := hc
  obtain ⟨pre, v, rest, he, hl, hvalue⟩ := split_register r.val vs (by have hlen := hv.1; omega)
  have hn : v ≠ 0 := by
    intro he
    exact hv.2 (hvalue.trans he)
  cases v with
  | zero => exact False.elim (hn rfl)
  | succ v =>
    subst vs
    have input : ZipRep conf
        (zAt RegisterBoxesPerm252.seekDec h (flat n (pre ++ (v + 1) :: rest) l)
          (registerBits pre ++ false :: false ::
            (List.replicate (v + 1) true ++ registerBits rest ++ [false]))) := by
      simpa [concrete, flat, segmentBits, boxBits, ← hl, markedBits_split,
        List.append_assoc, zAtS, zAt] using hc
    have hs := RegisterDecrementPerm252.positive_decrement pre v rest h _ input
    refine ⟨2 * width (pre ++ (v + 1) :: rest) + 3, ⟨h, ?_⟩, by simp⟩
    simpa [concrete, flat, segmentBits, boxBits, ← hl, decr_split,
      positiveExit_split pre r hl, leftAtS, leftAt] using hs

/-- A literal left move over the register file's leading zero is allowed
only when it writes the same zero. Its successor may be the real halt. -/
theorem box_back (br : Branch) (q : Fin 252) (next : Option (Fin 252))
    (x : Box) (l : List Segment)
    (ht : machinePerm252.transition q false = ⟨false, .left, next⟩) :
    StepSound br ⟨some q, false, l, [.box x]⟩
      ⟨next, true, l, [.box x]⟩ true := by
  intro n vs hv conf hc
  obtain ⟨h, hc⟩ := hc
  have hne : vs ≠ [] := by
    intro he
    have hlen := hv.1
    simp [he] at hlen
  obtain ⟨tail, he⟩ := box_head x vs hne
  have hs := zipStep_sound machinePerm252 hc
  simp only [concrete, Bool.false_eq_true, if_false, flat, List.flatMap_cons,
    segmentBits, List.flatMap_nil, List.append_nil] at hs
  rw [he, step_left_option q next false false h _ _ ht] at hs
  refine ⟨1, ⟨h, ?_⟩, by omega⟩
  simpa [concrete, flat, segmentBits, he, Machine.runFrom] using hs

/-- Recognize only the nine literal selector-entry states. This is a lookup
on compact states, independently of the logical-register permutation. -/
def skipTarget (q : Fin 252) : Option Reg :=
  match q.val with
  | 59 => some ⟨0, by decide⟩
  | 43 => some ⟨1, by decide⟩
  | 30 => some ⟨2, by decide⟩
  | 55 => some ⟨3, by decide⟩
  | 37 => some ⟨4, by decide⟩
  | 39 => some ⟨5, by decide⟩
  | 27 => some ⟨6, by decide⟩
  | 0 => some ⟨7, by decide⟩
  | 67 => some ⟨8, by decide⟩
  | _ => none

theorem skipTarget_sound : ∀ (q : Fin 252) (r : Reg),
    skipTarget q = some r → q = RegisterMarkPerm252.skip r.val := by decide

/-- Proof fields are erased from computation. Thus sstep is an executable
finite checker, while its proof of soundness cannot become an assumed box. -/
structure CheckedStep (br : Branch) (s : SConfig) where
  target : SConfig
  moved : Bool
  sound : StepSound br s target moved

private theorem action_eta (a : Action 252) : a = ⟨a.write, a.move, a.next⟩ := rfl

def peelRightChecked (br : Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List Segment) : Option (CheckedStep br ⟨q, false, l, .run b a c :: r⟩) :=
  match c, a with
  | c + 1, a => some ⟨_, false, peel_right br q b a c l r⟩
  | 0, 0 => some ⟨_, false, empty_run_right br q b l r⟩
  | 0, _ + 1 => none

def peelLeftChecked (br : Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List Segment) : Option (CheckedStep br ⟨q, true, .run b a c :: l, r⟩) :=
  match c, a with
  | c + 1, a => some ⟨_, false, peel_left br q b a c l r⟩
  | 0, 0 => some ⟨_, false, empty_run_left br q b l r⟩
  | 0, _ + 1 => none

def boxChecked (br : Branch) (q : Fin 252) (x : Box) (l : List Segment) :
    Option (CheckedStep br ⟨some q, false, l, [.box x]⟩) := by
  cases x with
  | plain e =>
    cases e with
    | unchanged =>
      cases hs : skipTarget q with
      | none => exact none
      | some r =>
        exact some ⟨_, false, by
          rw [skipTarget_sound q r hs]
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
def checkedStep (br : Branch) (s : SConfig) : Option (CheckedStep br s) := by
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
            · exact peelLeftChecked br (some q) b a c l r
          · exact peelLeftChecked br (some q) b a c l r
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
            · exact peelRightChecked br (some q) b a c l r
          · exact peelRightChecked br (some q) b a c l r
        | box x =>
          cases r with
          | cons _ _ => exact none
          | nil =>
            cases ho : boxChecked br q x l with
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
  (checkedStep br s).map (fun out => (out.target, out.moved))

theorem sstep_sound (br : Branch) (s t : SConfig) (m : Bool)
    (hs : sstep br s = some (t, m)) : StepSound br s t m := by
  unfold sstep at hs
  cases hc : checkedStep br s with
  | none => simp [hc] at hs
  | some out =>
    simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨ht, hm⟩
    simpa only [ht, hm] using out.sound

def exec : Nat → Branch → (SConfig → Bool) → SConfig → Bool → Option SConfig
  | 0, _, _, _, _ => none
  | fuel + 1, br, target, s, moved =>
    if moved && target s then some s
    else match sstep br s with
      | none => none
      | some (t, m) => exec fuel br target t (moved || m)

theorem exec_sound (fuel : Nat) (br : Branch) (target : SConfig → Bool)
    (s t : SConfig) (moved : Bool) (he : exec fuel br target s moved = some t) :
    target t = true ∧ StepSound br s t (!moved) := by
  induction fuel generalizing s moved with
  | zero => simp [exec] at he
  | succ fuel ih =>
    simp only [exec] at he
    split at he
    next halt =>
      have ht : moved = true ∧ target s = true := Bool.and_eq_true_iff.mp halt
      cases he
      refine ⟨ht.2, ?_⟩
      intro n vs hv c hc
      exact ⟨0, hc, by simp [ht.1]⟩
    next _ =>
      cases hs : sstep br s with
      | none => simp [hs] at he
      | some pair =>
        rcases pair with ⟨u, m⟩
        simp only [hs] at he
        obtain ⟨ht, hh⟩ := ih u (moved || m) he
        refine ⟨ht, ?_⟩
        intro n vs hv c hc
        obtain ⟨k, hk, hp⟩ := sstep_sound br s u m hs n vs hv c hc
        obtain ⟨j, hj, hq⟩ := hh n vs hv _ hk
        refine ⟨k + j, ?_, ?_⟩
        · simpa only [Machine.runFrom_add] using hj
        · intro hmove
          cases moved <;> cases m <;> simp_all
          · omega
          · omega

/-! Segment comparison is proved faithful, including the discarded false
exterior on the left. Equality of normalized syntax is never an oracle. -/

inductive Token where
  | run (b : Bool) (a c : Nat)
  | box (x : Box)
  deriving DecidableEq, Repr

def tokenBits (n : Nat) (vs : List Nat) : Token → List Bool
  | .run b a c => List.replicate (a * n + c) b
  | .box x => boxBits x vs

def flatT (n : Nat) (vs : List Nat) (ts : List Token) : List Bool :=
  ts.flatMap (tokenBits n vs)

def tokenOf : Segment → Token
  | .bit b => .run b 0 1
  | .run b a c => .run b a c
  | .box x => .box x

def push : Token → List Token → List Token
  | .box x, ts => .box x :: ts
  | .run b a c, ts =>
    if a = 0 ∧ c = 0 then ts
    else match ts with
    | .run b' a' c' :: tail =>
      if b = b' then .run b (a + a') (c + c') :: tail else .run b a c :: ts
    | _ => .run b a c :: ts

def norm (xs : List Segment) : List Token := xs.foldr (fun x ts => push (tokenOf x) ts) []

def dropExterior (ts : List Token) : List Token :=
  match ts.reverse with
  | .run false _ _ :: tail => tail.reverse
  | _ => ts

def normL (xs : List Segment) : List Token := dropExterior (norm xs)

theorem flatT_append (n : Nat) (vs : List Nat) (a b : List Token) :
    flatT n vs (a ++ b) = flatT n vs a ++ flatT n vs b := by
  simp [flatT, List.flatMap_append]

theorem flatT_push (n : Nat) (vs : List Nat) (t : Token) (ts : List Token) :
    flatT n vs (push t ts) = tokenBits n vs t ++ flatT n vs ts := by
  cases t with
  | box x => rfl
  | run b a c =>
    simp only [push]
    split
    next hz =>
      rcases hz with ⟨rfl, rfl⟩
      simp [tokenBits]
    next _ =>
      cases ts with
      | nil => simp [flatT]
      | cons t ts =>
        cases t with
        | box x => rfl
        | run b' a' c' =>
          by_cases hb : b = b'
          · subst b'
            have he : (a + a') * n + (c + c') = (a * n + c) + (a' * n + c') := by
              simp only [Nat.add_mul]
              omega
            simp only [if_true, flatT, List.flatMap_cons, tokenBits,
              he, ← List.replicate_append_replicate, List.append_assoc]
          · simp only [if_neg hb]
            rfl

theorem flatT_norm (n : Nat) (vs : List Nat) (xs : List Segment) :
    flatT n vs (norm xs) = flat n vs xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [norm, List.foldr_cons, flatT_push, flat_cons]
    change tokenBits n vs (tokenOf x) ++ flatT n vs (norm xs) = _
    rw [ih]
    cases x <;> simp [tokenBits, tokenOf, segmentBits]

theorem flatT_dropExterior (n : Nat) (vs : List Nat) (ts : List Token) :
    ∃ k : Nat, flatT n vs ts = flatT n vs (dropExterior ts) ++ List.replicate k false := by
  cases he : ts.reverse with
  | nil => exact ⟨0, by simp [dropExterior, he]⟩
  | cons t tail =>
    cases t with
    | box x => exact ⟨0, by simp [dropExterior, he]⟩
    | run b a c =>
      cases b with
      | true => exact ⟨0, by simp [dropExterior, he]⟩
      | false =>
        have ht : ts = tail.reverse ++ [.run false a c] := by
          simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse he
        refine ⟨a * n + c, ?_⟩
        simp only [dropExterior, he]
        rw [ht, flatT_append]
        simp [flatT, tokenBits]

theorem normL_spec (n : Nat) (vs : List Nat) (xs : List Segment) :
    ∃ k : Nat, flat n vs xs = flatT n vs (normL xs) ++ List.replicate k false := by
  rw [← flatT_norm]
  exact flatT_dropExterior n vs (norm xs)

private theorem getD_zero_padding (k i : Nat) :
    (List.replicate k false).getD i false = false := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getD_append_padding (xs : List Bool) (k i : Nat) :
    (xs ++ List.replicate k false).getD i false = xs.getD i false := by
  induction xs generalizing i with
  | nil => exact getD_zero_padding k i
  | cons b xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem getD_tail (xs : List Bool) (i : Nat) :
    xs.tail.getD i false = xs.getD (i + 1) false := by
  cases xs <;> rfl

theorem normL_getD (n : Nat) (vs : List Nat) (a b : List Segment)
    (he : normL a = normL b) (i : Nat) :
    (flat n vs a).getD i false = (flat n vs b).getD i false := by
  obtain ⟨ka, ha⟩ := normL_spec n vs a
  obtain ⟨kb, hb⟩ := normL_spec n vs b
  rw [ha, hb, he, getD_append_padding, getD_append_padding]

theorem zipRep_at_congr {c : Config 252} (q : Option (Fin 252))
    (h : Int) (l r l' r' : List Bool)
    (hl : ∀ i, l.getD i false = l'.getD i false)
    (hr : ∀ i, r.getD i false = r'.getD i false)
    (hc : ZipRep c (zAtS q h l r)) : ZipRep c (zAtS q h l' r') := by
  refine ⟨hc.1, hc.2.1, ?_, ?_⟩
  · intro i
    exact (hc.2.2.1 i).trans (hl i)
  · intro i
    exact (hc.2.2.2 i).trans (hr i)

theorem zipRep_leftAt_congr {c : Config 252} (q : Option (Fin 252))
    (h : Int) (l r l' r' : List Bool)
    (hl : ∀ i, l.getD i false = l'.getD i false)
    (hr : ∀ i, r.getD i false = r'.getD i false)
    (hc : ZipRep c (leftAtS q h l r)) : ZipRep c (leftAtS q h l' r') := by
  apply zipRep_at_congr q (h - 1) l.tail (l.getD 0 false :: r)
    l'.tail (l'.getD 0 false :: r') _ _ hc
  · intro i
    simpa only [getD_tail] using hl (i + 1)
  · intro i
    cases i with
    | zero => exact hl 0
    | succ i => exact hr i

/-- A decidable comparison sufficient for exact whole-tape equivalence.
Only the left exterior false run is omitted; no register/spare is omitted. -/
def isMatch (s t : SConfig) : Bool :=
  decide (s.state = t.state ∧ s.onLeft = t.onLeft ∧
    norm s.right = norm t.right ∧ normL s.left = normL t.left)

theorem matches_sound (s t : SConfig) (hm : isMatch s t = true)
    (n : Nat) (vs : List Nat) (c : Config 252) :
    Represents n vs s c → Represents n vs t c := by
  have he : s.state = t.state ∧ s.onLeft = t.onLeft ∧
      norm s.right = norm t.right ∧ normL s.left = normL t.left := of_decide_eq_true hm
  rcases s with ⟨q, onLeft, l, r⟩
  rcases t with ⟨q', onLeft', l', r'⟩
  rcases he with ⟨rfl, rfl, hr, hl⟩
  intro hc
  obtain ⟨h, hc⟩ := hc
  refine ⟨h, ?_⟩
  have er : flat n vs r = flat n vs r' := by
    rw [← flatT_norm, ← flatT_norm, hr]
  have el : ∀ i, (flat n vs l).getD i false = (flat n vs l').getD i false :=
    normL_getD n vs l l' hl
  cases onLeft with
  | false => exact zipRep_at_congr _ _ _ _ _ _ el (by intro i; rw [er]) hc
  | true => exact zipRep_leftAt_congr _ _ _ _ _ _ el (by intro i; rw [er]) hc

/-- A successful finite checked trace implies actual positive Core execution
to the requested entire symbolic tape, for every admitted n and file vs. -/
theorem exec_to_matches (fuel : Nat) (br : Branch) (s wanted reached : SConfig)
    (he : exec fuel br (fun t => isMatch t wanted) s false = some reached)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 252)
    (hc : Represents n vs s c) :
    ∃ k : Nat, 0 < k ∧ Represents n vs wanted (machinePerm252.runFrom c k) := by
  obtain ⟨hm, hs⟩ := exec_sound fuel br (fun t => isMatch t wanted) s reached false he
  obtain ⟨k, hk, hp⟩ := hs n vs hv c hc
  exact ⟨k, hp rfl, matches_sound reached wanted hm n vs _ hk⟩

theorem represents_state (n : Nat) (vs : List Nat) (s : SConfig) (c : Config 252)
    (hc : Represents n vs s c) : c.state = s.state := by
  obtain ⟨h, hc⟩ := hc
  cases hs : s.onLeft <;> simpa [concrete, hs, zAtS, leftAtS] using hc.1

/-- The halting case still executes the actual final write and move: the
reached symbolic configuration is represented in full before its state is
projected to obtain this weaker endpoint conclusion. -/
theorem exec_to_halt (fuel : Nat) (br : Branch) (s reached : SConfig)
    (he : exec fuel br (fun t => decide (t.state = none)) s false = some reached)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 252)
    (hc : Represents n vs s c) :
    ∃ k : Nat, 0 < k ∧ (machinePerm252.runFrom c k).state = none := by
  obtain ⟨hm, hs⟩ := exec_sound fuel br (fun t => decide (t.state = none)) s reached false he
  obtain ⟨k, hk, hp⟩ := hs n vs hv c hc
  exact ⟨k, hp rfl, (represents_state n vs reached _ hk).trans (of_decide_eq_true hm)⟩

/-- Certificate-facing check: no explicit reached-state payload is required. -/
def verifies (fuel : Nat) (br : Branch) (s wanted : SConfig) : Bool :=
  (exec fuel br (fun t => isMatch t wanted) s false).isSome

theorem verifies_sound (fuel : Nat) (br : Branch) (s wanted : SConfig)
    (he : verifies fuel br s wanted = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 252)
    (hc : Represents n vs s c) :
    ∃ k : Nat, 0 < k ∧ Represents n vs wanted (machinePerm252.runFrom c k) := by
  cases hx : exec fuel br (fun t => isMatch t wanted) s false with
  | none => simp [verifies, hx] at he
  | some reached => exact exec_to_matches fuel br s wanted reached hx n vs hv c hc

def verifiesHalt (fuel : Nat) (br : Branch) (s : SConfig) : Bool :=
  (exec fuel br (fun t => decide (t.state = none)) s false).isSome

theorem verifiesHalt_sound (fuel : Nat) (br : Branch) (s : SConfig)
    (he : verifiesHalt fuel br s = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 252)
    (hc : Represents n vs s c) :
    ∃ k : Nat, 0 < k ∧ (machinePerm252.runFrom c k).state = none := by
  cases hx : exec fuel br (fun t => decide (t.state = none)) s false with
  | none => simp [verifiesHalt, hx] at he
  | some reached => exact exec_to_halt fuel br s reached hx n vs hv c hc

#print axioms sstep_sound
#print axioms exec_sound
#print axioms matches_sound
#print axioms exec_to_matches
#print axioms exec_to_halt
#print axioms verifies_sound
#print axioms verifiesHalt_sound

end SetTheory.BusyBeaver.ZFC.SymbolicPerm252
